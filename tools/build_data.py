#!/usr/bin/env python3
"""Builds the map data that ships with the app, from an OpenStreetMap extract of Israel.

    python tools/build_data.py israel-and-palestine-latest.osm.pbf data

Writes, under the output folder:
  meta.json          build date, grid cell size, and which cells have data
  places.json        names of towns, villages and places (whole country, one file)
  hike/<i>_<j>.json  marked trails and bike trails, per grid cell
  topo/<i>_<j>.json  dirt roads, paths, streams, peaks and springs, per grid cell
  routes.json        facts about each named trail, for the route finder: length, climb,
                     shape, start point, water on the way, road access, viewpoints on it (see route_facts)
  views.json         viewpoints (marked ones, and named peaks with a wide view that a marked trail reaches; none in
                     military land, see build_views): how far the view reaches in each direction, how to get there,
                     what kind of land is in sight (see view_facts)
  photos.json        up to three photos of the view from each viewpoint, from Wikimedia Commons, with the
                     photographer and licence (see find_photos)

Coordinates are integers in 1e-5 degrees (about 1 m). A line is stored as
[lat0, lon0, dlat1, dlon1, ...]: its first point, then the step to each next point.
A way that crosses several cells is written to each of them; the app skips repeats by id.

Heights for routes.json and views.json come from open elevation tiles (Mapterhorn, Copernicus GLO-30, with
AWS Terrain Tiles as the backup), the same sources the app draws its contour lines from.
Without them (no network) the routes are still written, without climb figures, and views.json is empty.
"""
import io
import json
import math
import os
import re
import sys
import time
import threading
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone

import osmium

# Same area as LIMITS in index.html.
SOUTH, WEST, NORTH, EAST = 29.2, 33.95, 33.6, 36.1
CELL = 0.2
Q = 1e5            # coordinate quantum: 1e-5 degree
TOLERANCE = 3      # line simplification tolerance, in quanta (about 3 m)

MARKS = {'red', 'blue', 'green', 'black', 'orange', 'purple', 'yellow', 'brown', 'white'}
ROUTES = {'hiking': 'h', 'foot': 'h', 'mtb': 'm', 'bicycle': 'm'}
TOPO_WAYS = {('highway', 'track'): 0, ('highway', 'path'): 1,
             ('waterway', 'stream'): 2, ('waterway', 'wadi'): 2, ('waterway', 'river'): 3}
PLACES = ['city', 'town', 'village', 'hamlet', 'isolated_dwelling', 'locality']

# Route finder facts
PAVED = {'motorway', 'trunk', 'primary', 'secondary', 'tertiary', 'unclassified', 'residential',
         'living_street', 'service', 'motorway_link', 'trunk_link', 'primary_link', 'secondary_link',
         'tertiary_link'}
ROAD_GRID = 0.002      # degrees (~200 m): a start point in or next to a square with a road has road access
WATER_GRID = 0.01      # degrees, for looking up water points near a trail
WATER_NEAR = 150       # metres from the trail
WATER_KINDS = {('natural', 'spring'): 0, ('amenity', 'drinking_water'): 1, ('man_made', 'water_tap'): 1,
               ('waterway', 'waterfall'): 2}
SAMPLE = 25            # metres between height samples along a trail
CLIMB_STEP = 5         # metres: smaller ups and downs are elevation-model noise, not climbing
LOOP_GAP = 500         # metres: a line whose two ends are this close is a loop for the walker
M_PER_DEG = 111195.0

# Viewpoints
VIEW_DIRS = 36            # sight lines around a viewpoint, one every 10 degrees
VIEW_NEAR = 2000          # metres: up to here sight lines use the fine elevation tiles
VIEW_FAR = 60000          # metres: how far each sight line is followed
VIEW_D = list(range(150, VIEW_NEAR, 50)) + list(range(VIEW_NEAR, 10000, 200)) + list(range(10000, VIEW_FAR + 1, 500))
EYE = 2                   # metres: eye height above the highest ground right at the viewpoint
REFRACTION = 0.13         # the usual coefficient; air bends light down a little, so far land shows a bit more
EARTH_R = 6371000.0
VIEW_ON_TRAIL = 200       # metres: a viewpoint this close to a trail is on the trail
PEAK_BY_VIEWPOINT = 400   # metres: a peak this close to a marked viewpoint is the same place
# Points tagged as viewpoints whose name says they are something else (a business, a home, a street...).
NOT_A_VIEW = re.compile(r'شركة|مكتب|منزل|محل |مطبخ|صالون|صالة|كفتيريا|مسبح|دوار|شارع|عمارة|فيلا|خيمة|كرفان|ديوان|غاز |'
                        r'مجمع|مخيم|الأمن|شبكة|ملعب|\bHome\b|Headquarters')
PEAK_OPEN = (20, 18)      # a named peak counts as a viewpoint when it sees 20 km or more in half the directions
# Only places a walker may go. Military land in OpenStreetMap is of two sorts here. A base or an army post (named
# so, tagged so, or a small area of landuse=military) is closed: no viewpoint inside it. A firing zone (tagged as a
# danger or training area, named so, or a large unnamed area of landuse=military) is open to walkers only at set
# times, mostly weekends and holidays: a viewpoint in one stays only when a marked trail reaches it or a paved road
# passes right by, and is flagged ('fz') so that the app can say so. A viewpoint whose own tags close it is left out.
# A named peak is only our guess at a viewpoint, and many tops with a wide view are army posts, in use or abandoned,
# so a peak counts only when a marked trail reaches its top, or when it is on the hand-picked list.
MILITARY_BASE = {'base', 'barracks', 'airfield', 'naval_base', 'range', 'checkpoint', 'office', 'ammunition',
                 'launchpad', 'nuclear_explosion_site'}
MILITARY_FIRE = {'danger_area', 'training_area'}
BASE_NAME = re.compile(r'מחנה|בסיס|מוצב|מתקן|יחידת|קריית|בה"ד|בא"ח|\b(base|camp|barracks|air ?base|airfield)\b', re.I)
FIRE_NAME = re.compile(r'שטח אש|\bfiring\b', re.I)
FIRING_ZONE_KM2 = 10      # an unnamed area of landuse=military this large (its bounding box) is a firing zone
CLOSED_ACCESS = {'no', 'private', 'military', 'forbidden'}
ON_TRAIL = 200            # metres to the nearest marked trail, for a peak or a viewpoint in a firing zone
FIRE_ROAD = 100           # metres to a paved road or car park, for a viewpoint in a firing zone

# Viewpoint photos, from Wikimedia Commons: freely licensed, and searchable by where they were taken.
COMMONS_API = 'https://commons.wikimedia.org/w/api.php'
USER_AGENT = 'IsraelHikingMap-data/1.0 (https://github.com/Bzazim/Israel-Hiking-Trip)'
PHOTO_RADIUS = 1000       # metres around the viewpoint
PHOTOS = 3                # per viewpoint
PHOTO_BUDGET = 25 * 60    # seconds for all the photo searches; viewpoints not reached keep their photos
# Never the view from the ground: space and air photos, night skies, insides, plants, animals, food, signs.
PHOTO_NEVER = re.compile(r'\bISS\d|view of earth|\b(night|milky way|stars|aerial|drone|interior|inside|inner|selfie|'
                         r'portrait|diagram|logo|maps?|signs?|signpost|plaques?|inscriptions?|flowers?|insects?|butterfly|'
                         r'moth|beetle|bee|spider|snail|lizard|gecko|snake|bird|fungus|mushroom|orchid|food|dish|meal|'
                         r'radio|banner)\b|לילה|כוכבים|אוויר|שלט|מפה|פרח|חרק|פרפר|ציפור|לטאה|נחש|מאכל', re.I)
# A thing at the place: left out unless the photo is said to be a view ("view from the tower").
PHOTO_THING = re.compile(r'\b(memorial|monument|graves?|tomb|caves?|cistern|well|burial|stone|boundary|church|mosque|'
                         r'synagogue|chapel|museum|sculpture|statue|mosaic|bench|toilets?|parking|playground|gondola|'
                         r'lift|antenna|outpost|post|fortification|house|building|room|collection)\b|'
                         r'אנדרט|מצבה|קבר|קבורה|מערה|מערת|מערות|\bבור\b|אבן|כנסי|מסגד|בית כנסת|פסל|חניון|מוזיאון|ספסל', re.I)
# Words that say the photo is of the view, or taken at a viewpoint.
PHOTO_VIEW = re.compile(r'\b(view|views|pano|panorama|panoramic|vista|landscape|scenery|looking|seen from|overlooking)\b|'
                        r'נוף|פנורמה|מבט', re.I)
PHOTO_PLACE = re.compile(r'\b(viewpoint|lookout|overlook|observation)\b|מצפה|מצפור|תצפית', re.I)
SPECIES = re.compile(r'^File:[A-Z][a-z]+ [a-z]{3,}')  # "Anemone coronaria ...": a plant or animal


def mark_of(t):
    """Marking colour of a route, as the app reads it (colour tag, else osmc:symbol)."""
    def pick(v):
        v = (v or '').lower().strip()
        return v if v in MARKS else None
    c = pick(t.get('colour') or t.get('color'))
    if not c:
        sym = (t.get('osmc:symbol') or '').lower().split(':')
        c = pick((sym[2] if len(sym) > 2 else '').split('_')[0]) or pick(sym[0])
    return c


def is_israel_trail(t):
    he = (t.get('name') or '') + (t.get('name:he') or '')
    en = (t.get('name:en') or '') + (t.get('name') or '')
    return 'שביל ישראל' in he or re.search(r'israel national trail', en, re.I) is not None


def military_kind(t):
    """'base' for a base or army post, 'fire' for a firing zone, 'land' for other military land (a base or a firing
    zone, by its size; see MilitaryLand), None for anything else."""
    m = t.get('military')
    name = ' '.join(t.get(k) or '' for k in ('name', 'name:he', 'name:en'))
    if m in MILITARY_BASE or BASE_NAME.search(name):
        return 'base'
    if m in MILITARY_FIRE or FIRE_NAME.search(name):
        return 'fire'
    if m or t.get('landuse') == 'military':
        return 'land'
    return None


def military_tags(t):
    """The tags of military land that say what it is, for the build log."""
    return ' '.join(f'{k}={t.get(k)}' for k in ('landuse', 'military', 'name', 'name:en', 'access') if t.get(k))


def closed(t):
    return t.get('access') in CLOSED_ACCESS or t.get('foot') in CLOSED_ACCESS


def inside(lat, lon):
    return SOUTH <= lat <= NORTH and WEST <= lon <= EAST


def simplify(pts, tol=TOLERANCE):
    """Douglas-Peucker on integer points, iterative."""
    if len(pts) < 3:
        return pts
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    tol2 = tol * tol
    while stack:
        a, b = stack.pop()
        (ay, ax), (by, bx) = pts[a], pts[b]
        dy, dx = by - ay, bx - ax
        L2 = dx * dx + dy * dy
        best, idx = -1.0, -1
        for i in range(a + 1, b):
            py, px = pts[i]
            if L2 == 0:
                d2 = (py - ay) ** 2 + (px - ax) ** 2
            else:
                cr = (px - ax) * dy - (py - ay) * dx
                d2 = cr * cr / L2
            if d2 > best:
                best, idx = d2, i
        if best > tol2:
            keep[idx] = True
            stack.append((a, idx))
            stack.append((idx, b))
    return [p for p, k in zip(pts, keep) if k]


def encode(pts):
    out = [pts[0][0], pts[0][1]]
    for (y0, x0), (y1, x1) in zip(pts, pts[1:]):
        out += [y1 - y0, x1 - x0]
    return out


def cells_of(pts):
    lats = [p[0] / Q for p in pts]
    lons = [p[1] / Q for p in pts]
    i0, i1 = math.floor(min(lats) / CELL), math.floor(max(lats) / CELL)
    j0, j1 = math.floor(min(lons) / CELL), math.floor(max(lons) / CELL)
    return [f'{i}_{j}' for i in range(i0, i1 + 1) for j in range(j0, j1 + 1)]


def cell_of(lat, lon):
    return f'{math.floor(lat / CELL)}_{math.floor(lon / CELL)}'


def metres(a, b):
    """Distance between two (lat, lon) points in degrees; flat-earth is plenty at trail scale."""
    dy = (b[0] - a[0]) * M_PER_DEG
    dx = (b[1] - a[1]) * M_PER_DEG * math.cos(math.radians((a[0] + b[0]) / 2))
    return math.hypot(dx, dy)


def grid_key(lat, lon, g):
    return (math.floor(lat / g), math.floor(lon / g))


class Routes(osmium.SimpleHandler):
    """Pass 1: marked trail and bike route relations, and the ways they use;
    and military land drawn as a relation (multipolygon), and the ways it is drawn with."""
    def __init__(self):
        super().__init__()
        self.routes = []          # [name, mark, kind, israelTrail, relation id]
        self.members = []         # way ids of each route, in relation order
        self.way_routes = {}      # way id -> [route index]
        self.military = []        # [kind, tags, id] of military multipolygons
        self.mil_ways = {}        # way id -> [index in military]

    def relation(self, r):
        t = {k.k: k.v for k in r.tags}
        mil = military_kind(t) if t.get('type') == 'multipolygon' else None
        if mil:
            idx = len(self.military)
            self.military.append([mil, military_tags(t), f'r{r.id}'])
            for m in r.members:
                if m.type == 'w':
                    self.mil_ways.setdefault(m.ref, []).append(idx)
            return
        kind = ROUTES.get(t.get('route'))
        if not kind:
            return
        mark = mark_of(t)
        nat = kind == 'h' and is_israel_trail(t)
        if kind == 'h' and not mark and not nat:
            return  # walking routes without a marking colour aren't marked trails
        idx = len(self.routes)
        self.routes.append([t.get('name:he') or t.get('name') or '', mark or '', kind, 1 if nat else 0, r.id])
        ways = []
        for m in r.members:
            if m.type == 'w':
                ways.append(m.ref)
                self.way_routes.setdefault(m.ref, []).append(idx)
        self.members.append(ways)


class Features(osmium.SimpleHandler):
    """Pass 2: geometry of trail ways, topographic ways, and named points.
    Also, for the route finder: full geometry of trail ways, where paved roads and car parks are,
    and where there is water (springs, taps, waterfalls)."""
    def __init__(self, way_routes, military=(), mil_ways=None):
        super().__init__()
        self.way_routes = way_routes
        self.mil_ways = mil_ways or {}
        # military land: [kind, tags, id, [lines]]; a multipolygon's lines are the ways it is drawn with
        self.military = [m + [[]] for m in military]
        self.hike = {}            # cell -> list of [id, route idxs, coords]
        self.topo = {}            # cell -> {'t': [...], 'p': [...]}
        self.places = []
        self.route_geom = {}      # trail way id -> [(lat, lon) in quanta]
        self.roads = {}           # ROAD_GRID square -> points (degrees) of paved roads and car parks in it
        self.water = {}           # WATER_GRID square -> [[lat, lon, kind, name]] (quanta)
        self.viewpoints = []      # [id, lat, lon, name] of points tagged tourism=viewpoint
        self.peaks = []           # [id, lat, lon, name] of named peaks

    def add_road_point(self, lat, lon):
        self.roads.setdefault(grid_key(lat, lon, ROAD_GRID), []).append((lat, lon))

    def add_road(self, pts):
        for (y0, x0), (y1, x1) in zip(pts, pts[1:] or pts):
            n = max(1, int(max(abs(y1 - y0), abs(x1 - x0)) / Q / (ROAD_GRID / 2)))
            for k in range(n + 1 if (y0, x0) == (y1, x1) else n):
                self.add_road_point((y0 + (y1 - y0) * k / n) / Q, (x0 + (x1 - x0) * k / n) / Q)
        self.add_road_point(pts[-1][0] / Q, pts[-1][1] / Q)

    def node(self, n):
        if not n.location.valid():
            return
        lat, lon = n.location.lat, n.location.lon
        if not inside(lat, lon):
            return
        t = n.tags
        name = t.get('name:he') or t.get('name') or ''
        if t.get('amenity') == 'parking':
            self.add_road_point(lat, lon)
        if t.get('tourism') == 'viewpoint' and not closed(t):
            self.viewpoints.append([f'n{n.id}', lat, lon, name])
        for (k, v), code in WATER_KINDS.items():
            if t.get(k) == v:
                self.water.setdefault(grid_key(lat, lon, WATER_GRID), []).append(
                    [round(lat * Q), round(lon * Q), code, name])
                break
        place = t.get('place')
        if place in PLACES and name:
            self.places.append([round(lat * Q), round(lon * Q), PLACES.index(place), name])
            return
        nat = t.get('natural')
        if nat in ('peak', 'spring'):
            ele = t.get('ele')
            try:
                ele = round(float(ele.replace(',', '.').split()[0])) if ele else None
            except ValueError:
                ele = None
            if nat == 'peak' and not name and ele is None:
                return
            if nat == 'peak' and name and not closed(t):
                self.peaks.append([f'p{n.id}', lat, lon, name])
            cell = self.topo.setdefault(cell_of(lat, lon), {'t': [], 'p': []})
            cell['p'].append([round(lat * Q), round(lon * Q), 0 if nat == 'peak' else 1, name, ele])

    def way(self, w):
        routes = self.way_routes.get(w.id)
        kind = None
        for (k, v), code in TOPO_WAYS.items():
            if w.tags.get(k) == v:
                kind = code
                break
        road = w.tags.get('highway') in PAVED or w.tags.get('amenity') == 'parking'
        view = w.tags.get('tourism') == 'viewpoint' and not closed(w.tags)
        mil = military_kind(w.tags)
        mil_rel = self.mil_ways.get(w.id)
        if routes is None and kind is None and not road and not view and not mil and not mil_rel:
            return
        pts = []
        for nd in w.nodes:
            if not nd.location.valid():
                continue
            p = (round(nd.location.lat * Q), round(nd.location.lon * Q))
            if not pts or pts[-1] != p:
                pts.append(p)
        if len(pts) < 2 and not road:
            return
        if not pts or not any(inside(y / Q, x / Q) for y, x in pts):
            return
        if view:
            name = w.tags.get('name:he') or w.tags.get('name') or ''
            self.viewpoints.append([f'w{w.id}', sum(p[0] for p in pts) / len(pts) / Q, sum(p[1] for p in pts) / len(pts) / Q, name])
        if road:
            self.add_road(pts)
        if mil and len(pts) >= 4 and pts[0] == pts[-1]:
            self.military.append([mil, military_tags(w.tags), f'w{w.id}', [pts]])
        for i in mil_rel or ():
            self.military[i][3].append(pts)
        if routes is None and kind is None:
            return
        if len(pts) < 2:
            return
        g = encode(simplify(pts))
        cells = cells_of(pts)
        if routes is not None:
            self.route_geom[w.id] = pts
            for c in cells:
                self.hike.setdefault(c, []).append([w.id, routes, g])
        if kind is not None:
            for c in cells:
                self.topo.setdefault(c, {'t': [], 'p': []})['t'].append([w.id, kind, g])


# ---------- Heights ----------

class Dem:
    """Heights from Terrarium tiles: Mapterhorn (GLO-30) first, AWS Terrain Tiles if that fails."""
    SOURCES = [
        ('https://tiles.mapterhorn.com/{z}/{x}/{y}.webp', 12, 512),
        ('https://s3.amazonaws.com/elevation-tiles-prod/terrarium/{z}/{x}/{y}.png', 13, 256),
    ]

    def __init__(self, sources=None):
        if sources:
            self.SOURCES = sources
        self.src = 0
        self.tiles = {}

    def _xy(self, lat, lon):
        _, z, size = self.SOURCES[self.src]
        n = 2 ** z
        fx = (lon + 180) / 360 * n
        fy = (1 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2 * n
        return fx * size, fy * size, size

    def _fetch(self, key):
        import numpy as np
        from PIL import Image
        url_t, z, _ = self.SOURCES[self.src]
        url = url_t.format(z=z, x=key[0], y=key[1])
        for _attempt in range(3):
            try:
                req = urllib.request.Request(url, headers={'User-Agent': 'israel-hiking-map data build'})
                with urllib.request.urlopen(req, timeout=40) as r:
                    img = Image.open(io.BytesIO(r.read())).convert('RGB')
                a = np.asarray(img, dtype=np.float32)
                return key, a[:, :, 0] * 256 + a[:, :, 1] + a[:, :, 2] / 256 - 32768
            except Exception:  # noqa: BLE001 - any failure means "no tile"
                time.sleep(1 + 2 * _attempt)
        return key, None

    def prefetch(self, points):
        """Downloads every tile under the given (lat, lon) points."""
        while self.src < len(self.SOURCES):
            keys = set()
            for lat, lon in points:
                px, py, size = self._xy(lat, lon)
                for dx in (0, 1):
                    for dy in (0, 1):  # bilinear lookups may reach the next tile
                        keys.add((int((px + dx) // size), int((py + dy) // size)))
            keys -= set(self.tiles)
            # Try a few first, to fall back quickly when a source is unreachable.
            probe = list(keys)[:4]
            with ThreadPoolExecutor(8) as ex:
                got = dict(ex.map(self._fetch, probe))
            if probe and all(v is None for v in got.values()):
                print(f'elevation source {self.SOURCES[self.src][0]} unreachable', flush=True)
                self.src += 1
                self.tiles = {}
                continue
            with ThreadPoolExecutor(12) as ex:
                got.update(ex.map(self._fetch, keys - set(probe)))
            self.tiles.update(got)
            bad = sum(1 for v in got.values() if v is None)
            print(f'elevation: {len(got)} tiles from {self.SOURCES[self.src][0]}, {bad} missing', flush=True)
            return True
        return False

    def height(self, lat, lon):
        if self.src >= len(self.SOURCES):
            return None
        px, py, size = self._xy(lat, lon)
        px, py = px - 0.5, py - 0.5  # pixel centres
        x0, y0 = math.floor(px), math.floor(py)
        fx, fy = px - x0, py - y0
        vals = []
        for yy, xx in ((y0, x0), (y0, x0 + 1), (y0 + 1, x0), (y0 + 1, x0 + 1)):
            t = self.tiles.get((xx // size, yy // size))
            if t is None:
                return None
            vals.append(float(t[yy % size, xx % size]))
        top = vals[0] * (1 - fx) + vals[1] * fx
        bot = vals[2] * (1 - fx) + vals[3] * fx
        return top * (1 - fy) + bot * fy


def resample(pts, step=SAMPLE):
    """Points every `step` metres along a line of quanta, as (lat, lon) degrees, both ends included."""
    deg = [(y / Q, x / Q) for y, x in pts]
    out = [deg[0]]
    carry = 0.0
    for a, b in zip(deg, deg[1:]):
        L = metres(a, b)
        if L == 0:
            continue
        pos = step - carry
        while pos <= L:
            t = pos / L
            out.append((a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t))
            pos += step
        carry = L - (pos - step)
    if carry > 1:
        out.append(deg[-1])
    return out


def climb(hs, step=CLIMB_STEP):
    """Metres up and down along a height profile, ignoring wiggles smaller than `step`.
    up - down always equals the last height minus the first."""
    up = down = 0.0
    ref = hs[0]
    for h in hs[1:]:
        if h - ref >= step:
            up += h - ref
            ref = h
        elif ref - h >= step:
            down += ref - h
            ref = h
    d = hs[-1] - ref
    if d > 0:
        up += d
    else:
        down -= d
    return up, down


class WayFacts:
    """Length, samples and height profile of one trail way (shared by the routes that use it)."""
    def __init__(self, pts):
        self.pts = pts
        self.samples = resample(pts)
        self.length = sum(metres(a, b) for a, b in zip(self.samples, self.samples[1:]))
        self.heights = None

    def set_heights(self, dem):
        hs = [dem.height(lat, lon) for lat, lon in self.samples]
        if any(h is None for h in hs):
            return
        self.heights = hs
        up, down = climb(hs)
        self.variation = up + down
        win = max(1, round(200 / SAMPLE))   # steepest 200 m stretch, as a grade
        self.steep = max((abs(hs[i + win] - hs[i]) / (win * SAMPLE) for i in range(len(hs) - win)), default=0)


def near_road(roads, lat, lon):
    i, j = grid_key(lat, lon, ROAD_GRID)
    return any((i + di, j + dj) in roads for di in (-1, 0, 1) for dj in (-1, 0, 1))


def road_distance(roads, lat, lon, rings=15):
    """Metres to the nearest paved road or car park (to within ~50 m), or None if farther than ~3 km."""
    i, j = grid_key(lat, lon, ROAD_GRID)
    best = None
    for r in range(rings + 1):
        for di in range(-r, r + 1):
            for dj in range(-r, r + 1):
                if max(abs(di), abs(dj)) != r:
                    continue
                for p in roads.get((i + di, j + dj), ()):
                    m = metres((lat, lon), p)
                    if best is None or m < best:
                        best = m
        # squares in the next ring are at least r squares away
        if best is not None and best <= r * ROAD_GRID * M_PER_DEG * 0.85:
            return best
    return best


def route_facts(rec, way_ids, facts, roads, water):
    """Everything the route finder knows about one route. Returns None for routes with no geometry."""
    ways = [facts[w] for w in dict.fromkeys(way_ids) if w in facts]
    if not ways:
        return None
    # Shape: a graph of trail pieces between junctions. No odd-degree junction: a loop. Two: a line.
    seen = Counter(p for f in ways for p in set(f.pts))
    deg = Counter()
    parent = {}

    def root(p):
        parent.setdefault(p, p)
        while parent[p] != p:
            parent[p] = parent[parent[p]]
            p = parent[p]
        return p

    for f in ways:
        cut = [p for i, p in enumerate(f.pts) if i in (0, len(f.pts) - 1) or seen[p] > 1]
        for a, b in zip(cut, cut[1:]):
            deg[a] += 1
            deg[b] += 1
            parent[root(a)] = root(b)
    odd = [p for p, d in deg.items() if d % 2]
    parts = len({root(p) for p in deg})
    first_way = set(ways[0].pts)
    as_deg = lambda p: (p[0] / Q, p[1] / Q)  # noqa: E731

    if parts == 1 and not odd:
        shape = 0
    elif parts == 1 and len(odd) == 2:
        shape = 1
    else:
        shape = 2  # several pieces or branches

    # Start: an end of the line (or any point of a loop) next to a road; else the relation's first point.
    ends = [as_deg(p) for p in odd]
    ends.sort(key=lambda e: (not near_road(roads, *e), (round(e[0] * Q), round(e[1] * Q)) not in first_way))
    if shape == 1 or (shape == 2 and ends):
        start = ends[0]
    else:
        start = next((s for f in ways for s in f.samples if near_road(roads, *s)), ways[0].samples[0])
    end = ends[1] if shape == 1 and len(ends) > 1 else None
    if shape == 1 and metres(start, end) <= LOOP_GAP:
        shape, end = 0, None   # the two ends meet: the walker comes back to the car

    km = sum(f.length for f in ways) / 1000
    lats = [p[0] for f in ways for p in f.samples]
    lons = [p[1] for f in ways for p in f.samples]
    q = lambda v: round(v * Q)  # noqa: E731
    out = {
        'id': rec[4], 'n': rec[0], 'm': rec[1], 'k': rec[2], 'nat': rec[3],
        'km': round(km, 2), 'sh': shape,
        's': [q(start[0]), q(start[1])],
        'bb': [q(min(lats)), q(min(lons)), q(max(lats)), q(max(lons))],
        'car': 1 if near_road(roads, *start) else (2 if any(near_road(roads, *s) for f in ways for s in f.samples[::8]) else 0),
    }
    if end:
        out['e'] = [q(end[0]), q(end[1])]

    if all(f.heights for f in ways):
        var = sum(f.variation for f in ways)
        hs = [h for f in ways for h in f.heights]
        if shape == 1:
            # ascent - descent = end height - start height, ascent + descent = total variation
            def h_at(p):
                best = min(((metres(p, s), f.heights[i]) for f in ways for i, s in enumerate(f.samples)),
                           key=lambda t: t[0])
                return best[1]
            dh = h_at(end) - h_at(start)
            up, dn = (var + dh) / 2, (var - dh) / 2
        else:
            up = dn = var / 2
        out.update({'up': round(max(up, 0)), 'dn': round(max(dn, 0)),
                    'lo': round(min(hs)), 'hi': round(max(hs)),
                    'st': round(max(f.steep for f in ways) * 100)})

    # Water within WATER_NEAR metres of the trail.
    found = {}
    for f in ways:
        for lat, lon in f.samples[::2]:
            i, j = grid_key(lat, lon, WATER_GRID)
            for di in (-1, 0, 1):
                for dj in (-1, 0, 1):
                    for w in water.get((i + di, j + dj), ()):
                        key = (w[0], w[1])
                        if key not in found and metres((lat, lon), (w[0] / Q, w[1] / Q)) <= WATER_NEAR:
                            found[key] = w
    if found:
        out['w'] = sorted(found.values(), key=lambda w: (w[2], not w[3]))[:12]
        out['wn'] = len(found)
    out['c'] = sorted({c for f in ways for c in cells_of(f.pts)})
    # Points along the trail every ~500 m (1 km on long trails), for the distance from the walker to the nearest
    # part of the trail. In 1e-4 degrees (~10 m), as [lat0, lon0, dlat1, dlon1, ...].
    spacing = 1000 if km > 50 else 500
    pts, last = [], None
    for f in ways:
        for i, s in enumerate(f.samples):
            if last is None or metres(last, s) >= spacing or (i == len(f.samples) - 1 and f is ways[-1]):
                pts.append((round(s[0] * 1e4), round(s[1] * 1e4)))
                last = s
    enc = [pts[0][0], pts[0][1]]
    for (y0, x0), (y1, x1) in zip(pts, pts[1:]):
        enc += [y1 - y0, x1 - x0]
    out['p'] = enc
    return out


class Mosaic:
    """One height grid over the country and the land around it, from coarser tiles (~70 m), for sight lines
    that run tens of kilometres, into Jordan, Lebanon, Syria and Sinai too."""
    SOURCES = [
        ('https://tiles.mapterhorn.com/{z}/{x}/{y}.webp', 10, 512),
        ('https://s3.amazonaws.com/elevation-tiles-prod/terrarium/{z}/{x}/{y}.png', 11, 256),
    ]
    PAD = 0.6  # degrees around the area

    def __init__(self):
        import numpy as np
        self.np = np
        dem = Dem(self.SOURCES)
        step = 0.05
        rows = int((NORTH - SOUTH + 2 * self.PAD) / step) + 1
        cols = int((EAST - WEST + 2 * self.PAD) / step) + 1
        self.ok = dem.prefetch([(SOUTH - self.PAD + i * step, WEST - self.PAD + j * step)
                                for i in range(rows) for j in range(cols)])
        if not self.ok:
            return
        _, self.z, self.size = dem.SOURCES[dem.src]
        xs = [k[0] for k in dem.tiles]
        ys = [k[1] for k in dem.tiles]
        self.x0, self.y0 = min(xs), min(ys)
        sz = self.size
        self.grid = np.zeros(((max(ys) - self.y0 + 1) * sz, (max(xs) - self.x0 + 1) * sz), dtype=np.int16)
        for (x, y), t in dem.tiles.items():
            if t is not None:
                self.grid[(y - self.y0) * sz:(y - self.y0 + 1) * sz, (x - self.x0) * sz:(x - self.x0 + 1) * sz] = \
                    np.clip(np.round(t), -32000, 32000)

    def heights(self, lat, lon):
        """Bilinear heights at arrays of points."""
        np = self.np
        n = 2 ** self.z * self.size
        px = (lon + 180) / 360 * n - self.x0 * self.size - 0.5
        py = (1 - np.arcsinh(np.tan(np.radians(lat))) / np.pi) / 2 * n - self.y0 * self.size - 0.5
        H, W = self.grid.shape
        px = np.clip(px, 0, W - 1.001)
        py = np.clip(py, 0, H - 1.001)
        x0, y0 = px.astype(int), py.astype(int)
        fx, fy = px - x0, py - y0
        g = self.grid
        top = g[y0, x0] * (1 - fx) + g[y0, x0 + 1] * fx
        bot = g[y0 + 1, x0] * (1 - fx) + g[y0 + 1, x0 + 1] * fx
        return top * (1 - fy) + bot * fy


def view_facts(lat, lon, dem, mosaic):
    """The view from a point. For each of VIEW_DIRS directions, the farthest ground in sight; and from the land
    in sight 1-20 km away, whether it is a wide lowland well below (a valley view) or high, broken land
    around (a mountain view). Sight lines bend down with the earth's curve, less a little for refraction."""
    np = mosaic.np
    az = np.radians(np.arange(VIEW_DIRS) * 360 / VIEW_DIRS)
    d = np.array(VIEW_D, dtype=float)
    kx = 1 / (M_PER_DEG * math.cos(math.radians(lat)))
    la = lat + np.outer(np.cos(az), d) / M_PER_DEG
    lo = lon + np.outer(np.sin(az), d) * kx
    h = mosaic.heights(la, lo)
    near = int(np.searchsorted(d, VIEW_NEAR))
    if dem is not None:  # the first two kilometres from the finer tiles
        for i in range(VIEW_DIRS):
            for j in range(near):
                v = dem.height(la[i, j], lo[i, j])
                if v is not None:
                    h[i, j] = v

    def ground(y, x):
        v = dem.height(y, x) if dem is not None else None
        return v if v is not None else float(mosaic.heights(np.array([y]), np.array([x]))[0])
    # A viewpoint usually stands at the edge of a drop: take the highest ground within ~50 m.
    g0 = max(ground(lat + 50 * math.cos(a) / M_PER_DEG, lon + 50 * math.sin(a) * kx) for a in np.radians(np.arange(0, 360, 45)))
    g0 = max(g0, ground(lat, lon))
    ang = (h - d * d / (2 * EARTH_R) * (1 - REFRACTION) - (g0 + EYE)) / d
    seen_above = np.concatenate([np.full((VIEW_DIRS, 1), -np.inf), np.maximum.accumulate(ang, axis=1)[:, :-1]], axis=1)
    vis = ang >= seen_above
    reach = np.where(vis, d, 0).max(axis=1)

    # The land in sight 1-20 km away. Valley view: flat ground (under 3% slope) at least 150 m below makes up
    # 8% of it or more; the sea surface (height ~0) doesn't count. Mountain view: the heights in sight spread
    # over 300 m or more (between the lowest and highest tenth).
    band = (d >= 1000) & (d <= 20000)
    slope = np.abs(np.diff(h, axis=1, append=h[:, -1:])) / np.diff(d, append=d[-1] + 1)
    seen = vis[:, band]
    hv, sv = h[:, band][seen], slope[:, band][seen]
    total = VIEW_DIRS * int(band.sum())
    flat_low = (hv <= g0 - 150) & (sv < 0.03) & (np.abs(hv) > 2)
    valley = int(flat_low.sum()) >= 0.08 * total
    mountains = len(hv) > 0 and float(np.percentile(hv, 90) - np.percentile(hv, 10)) >= 300
    return {
        'h': round(g0),
        'v': [int(round(x / 1000)) for x in reach],
        'val': 1 if valley else 0,
        'mtn': 1 if mountains else 0,
    }


class MilitaryLand:
    """Military land from OpenStreetMap, to ask whether a point is in it."""
    G = 0.05  # degrees: grid squares for finding the areas around a point

    def __init__(self, areas):
        self.grid = {}
        self.count = Counter()
        for kind, tags, aid, lines in areas:
            pts = [p for line in lines for p in line]
            if len(pts) < 4:
                continue
            y0, y1 = min(p[0] for p in pts), max(p[0] for p in pts)
            x0, x1 = min(p[1] for p in pts), max(p[1] for p in pts)
            if kind == 'land':
                km2 = (y1 - y0) / Q * M_PER_DEG / 1000 * (x1 - x0) / Q * M_PER_DEG / 1000 * math.cos(math.radians(y0 / Q))
                kind = 'fire' if km2 >= FIRING_ZONE_KM2 else 'base'
            self.count[kind] += 1
            a = (kind, tags, aid, lines, (y0, x0, y1, x1))
            (i0, j0), (i1, j1) = grid_key(y0 / Q, x0 / Q, self.G), grid_key(y1 / Q, x1 / Q, self.G)
            for i in range(i0, i1 + 1):
                for j in range(j0, j1 + 1):
                    self.grid.setdefault((i, j), []).append(a)

    def at(self, lat, lon):
        """The military area the point is in, as (kind, tags, id), or None. A base first, then a firing zone."""
        y, x = lat * Q, lon * Q
        found = []
        for kind, tags, aid, lines, (y0, x0, y1, x1) in self.grid.get(grid_key(lat, lon, self.G), ()):
            if not (y0 <= y <= y1 and x0 <= x <= x1):
                continue
            # Even-odd rule over all the lines of the area: a multipolygon's ways need not be joined into rings
            # first, and its inner rings (holes) come out right.
            inn = False
            for line in lines:
                for (ay, ax), (by, bx) in zip(line, line[1:]):
                    if (ay > y) != (by > y) and x < (bx - ax) * (y - ay) / (by - ay) + ax:
                        inn = not inn
            if inn:
                found.append((kind, tags, aid))
        return min(found, key=lambda a: a[0] != 'base') if found else None


def segment_metres(p, a, b):
    """Distance from point p to the segment a-b, all (lat, lon) in degrees."""
    k = math.cos(math.radians(p[0]))
    ay, ax = (a[0] - p[0]) * M_PER_DEG, (a[1] - p[1]) * M_PER_DEG * k
    by, bx = (b[0] - p[0]) * M_PER_DEG, (b[1] - p[1]) * M_PER_DEG * k
    dy, dx = by - ay, bx - ax
    L2 = dy * dy + dx * dx
    t = 0 if L2 == 0 else max(0.0, min(1.0, -(ay * dy + ax * dx) / L2))
    return math.hypot(ay + t * dy, ax + t * dx)


class TrailNear:
    """Marked trail ways, to ask how close the nearest one comes to a point."""
    G = 0.01  # degrees (~1 km)

    def __init__(self, geoms):
        self.geoms = geoms
        self.grid = {}
        for wid, pts in geoms.items():
            for y, x in pts:
                cell = self.grid.setdefault(grid_key(y / Q, x / Q, self.G), set())
                cell.add(wid)

    def within(self, lat, lon, m):
        i, j = grid_key(lat, lon, self.G)
        ways = set()
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                ways |= self.grid.get((i + di, j + dj), set())
        for wid in ways:
            pts = self.geoms[wid]
            for a, b in zip(pts, pts[1:] or pts):
                if segment_metres((lat, lon), (a[0] / Q, a[1] / Q), (b[0] / Q, b[1] / Q)) <= m:
                    return True
        return False


def picked_views(featured, items):
    """The ids among items ([id, lat, lon, name]) that a featured.json list names, by 'osm' name or 'near'."""
    out = set()
    for e in featured or []:
        if e.get('osm'):
            out |= {it[0] for it in items if it[3] == e['osm']}
        elif e.get('near'):
            best = min(items, key=lambda it: metres(e['near'], (it[1], it[2])), default=None)
            if best and metres(e['near'], (best[1], best[2])) <= 500:
                out.add(best[0])
    return out


def build_views(f, dem, featured=None):
    """Marked viewpoints, and named peaks with a wide view that a marked trail reaches and that have no marked
    viewpoint next to them. None in a base or closed; in a firing zone, only ones a marked trail or a paved road
    reaches (see MILITARY_BASE). Hand-picked ones (featured.json 'views') stay, and the ones 'hide' names go."""
    try:
        mosaic = Mosaic()
    except ImportError:
        print('numpy/Pillow missing: no viewpoints', flush=True)
        return []
    if not mosaic.ok:
        print('no elevation data: no viewpoints', flush=True)
        return []
    if dem is not None and dem.src >= len(dem.SOURCES):
        dem = None

    def bucket(items, g=WATER_GRID):
        out = {}
        for it in items:
            out.setdefault(grid_key(it[1], it[2], g), []).append(it)
        return out

    def nearest(buckets, lat, lon, within, g=WATER_GRID):
        i, j = grid_key(lat, lon, g)
        best = None
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                for it in buckets.get((i + di, j + dj), ()):
                    m = metres((lat, lon), (it[1], it[2]))
                    if m <= within and (best is None or m < best[0]):
                        best = (m, it)
        return best[1] if best else None

    vps = [v for v in f.viewpoints if not NOT_A_VIEW.search(v[3])]
    if len(vps) < len(f.viewpoints):
        print(f'viewpoints: {len(f.viewpoints) - len(vps)} left out by name (not a viewpoint)', flush=True)
    by_vp = bucket(vps)
    peaks = [p for p in f.peaks if not nearest(by_vp, p[1], p[2], PEAK_BY_VIEWPOINT)]

    featured = featured or {}
    keep = picked_views(featured.get('views'), vps + peaks)
    hide = picked_views(featured.get('hide'), vps + peaks)
    mil = MilitaryLand(f.military)
    print(f'military land: {dict(mil.count)} areas', flush=True)
    trails = TrailNear(f.route_geom)
    out_base, out_fire, in_fire, out_trail = [], [], [], 0
    cands, fire = [], set()
    for kind, items in ((0, vps), (1, peaks)):
        for it in items:
            if it[0] in hide:
                continue
            m = mil.at(it[1], it[2])
            if m and m[0] == 'fire':
                fire.add(it[0])
            if it[0] not in keep:
                if m and m[0] == 'base':
                    out_base.append((it, m))
                    continue
                on_trail = trails.within(it[1], it[2], ON_TRAIL)
                if m and not on_trail:
                    rd = road_distance(f.roads, it[1], it[2], 2)
                    if rd is None or rd > FIRE_ROAD:
                        out_fire.append((it, m))
                        continue
                if kind == 1 and not on_trail:
                    out_trail += 1
                    continue
            if it[0] in fire:
                in_fire.append((it, m))
            cands.append((kind, it))
    print(f'viewpoints: {len(hide)} hidden by hand (featured.json); left out: {len(out_base)} in bases and army '
          f'posts, {len(out_fire)} in firing zones with no marked trail or road to them, {out_trail} peaks with no '
          f'marked trail to the top; {len(in_fire)} kept in firing zones', flush=True)
    for what, lst in (('base, out', out_base), ('firing zone, out', out_fire), ('firing zone, kept', in_fire)):
        for it, m in lst:
            print(f'  {what}: {it[0]} {it[3] or "-"} ({it[1]:.4f}, {it[2]:.4f}) in {m[2]} {m[1]}', flush=True)
    print(f'viewpoints: {sum(1 for k, _ in cands if k == 0)} marked, {sum(1 for k, _ in cands if k == 1)} '
          f'named peaks to check', flush=True)
    if dem is not None:
        dem.prefetch([(c[1] + a, c[2] + b) for _, c in cands for a in (-0.02, 0, 0.02) for b in (-0.024, 0, 0.024)])

    by_peak = bucket(f.peaks, 0.02)
    by_place = bucket([[None, y / Q, x / Q, name] for y, x, k, name in f.places if k <= 3], 0.05)
    out = []
    for kind, (vid, lat, lon, name) in cands:
        v = view_facts(lat, lon, dem, mosaic)
        if kind == 1 and vid not in keep and sum(1 for x in v['v'] if x >= PEAK_OPEN[0]) < PEAK_OPEN[1]:
            continue
        o = {'id': vid, 'n': name, 'k': kind, 's': [round(lat * Q), round(lon * Q)]}
        if not name:  # name it after what is near
            near = nearest(by_peak, lat, lon, 1500, 0.02) or nearest(by_place, lat, lon, 5000, 0.05)
            o['n'] = 'תצפית ליד ' + near[3] if near else 'תצפית'
            o['nn'] = 1
        rd = road_distance(f.roads, lat, lon)
        o['r'] = None if rd is None else int(round(rd / 10) * 10)
        if vid in fire:
            o['fz'] = 1
        o.update(v)
        out.append(o)
    print(f'viewpoints: {len(out)} written ({sum(1 for o in out if o["k"] == 1)} of them peaks)', flush=True)
    return out


# ---------- Viewpoint photos (Wikimedia Commons) ----------

def strip_html(v):
    v = re.sub(r'<[^>]+>', ' ', v or '')
    v = re.sub(r'&nbsp;|&#160;', ' ', v)
    v = re.sub(r'&amp;', '&', v)
    v = re.sub(r'&[a-z]+;|&#\d+;', '', v)
    return ' '.join(v.split())


COMMONS_PROBLEMS = Counter()   # what went wrong, for the build log
_commons_lock = threading.Lock()
_commons_last = [0.0]
COMMONS_GAP = 1.0              # seconds between calls: the location search is shared and easily busy


def commons_problem(what):
    with _commons_lock:
        COMMONS_PROBLEMS[what] += 1
        if COMMONS_PROBLEMS[what] == 1:
            print(f'photos: Commons said: {what}', flush=True)


def commons(params):
    """One Commons API call, politely: a clear user agent, maxlag, one call every COMMONS_GAP seconds, and
    longer pauses when asked to slow down (HTTP 429 and its Retry-After, maxlag, rate limits)."""
    q = urllib.parse.urlencode({**params, 'format': 'json', 'formatversion': 2, 'maxlag': 5})
    req = urllib.request.Request(COMMONS_API + '?' + q, headers={'User-Agent': USER_AGENT})
    for attempt in range(5):
        with _commons_lock:
            wait = _commons_last[0] + COMMONS_GAP - time.monotonic()
            _commons_last[0] = time.monotonic() + max(wait, 0)
        if wait > 0:
            time.sleep(wait)
        try:
            with urllib.request.urlopen(req, timeout=40) as r:
                d = json.load(r)
        except urllib.error.HTTPError as e:
            commons_problem(f'HTTP {e.code}')
            retry = e.headers.get('Retry-After', '') if e.headers else ''
            time.sleep(min(int(retry) if retry.isdigit() else 10 * (attempt + 1), 120))
            continue
        except Exception as e:  # noqa: BLE001 - network trouble
            commons_problem(type(e).__name__)
            time.sleep(3 + 3 * attempt)
            continue
        if 'error' in d:
            code = d['error'].get('code', '?')
            commons_problem(f"{code}: {d['error'].get('info', '')[:150]}")
            if code == 'maxlag' or 'rate' in code or 'limit' in code or 'busy' in code:
                time.sleep(15 * (attempt + 1))  # e.g. cirrussearch-too-busy-error: "try again later"
                continue
            return None
        return d
    return None


def photo_entry(page):
    """[file name, photographer, licence, width/height] of a Commons file page, or None."""
    ii = (page.get('imageinfo') or [{}])[0]
    meta = ii.get('extmetadata') or {}
    name = page.get('title', '')[len('File:'):]
    if not name:
        return None
    author = strip_html((meta.get('Artist') or {}).get('value', ''))[:60]
    lic = strip_html((meta.get('LicenseShortName') or {}).get('value', ''))[:30]
    w, h = ii.get('width') or 0, ii.get('height') or 1
    return [name, author, lic, round(w / h, 2)]


def photo_score(page):
    """How likely a photo near a viewpoint shows its view; None if it surely doesn't."""
    ii = (page.get('imageinfo') or [{}])[0]
    w, h = ii.get('width') or 0, ii.get('height') or 0
    if ii.get('mime') not in ('image/jpeg', 'image/png', 'image/webp', 'image/tiff') or w < 800 or h < 400:
        return None
    ratio = w / h
    if ratio < 1.15:  # upright or square photos are seldom of the view
        return None
    meta = ii.get('extmetadata') or {}
    text = ' '.join([page.get('title', ''), strip_html((meta.get('ImageDescription') or {}).get('value', '')),
                     strip_html((meta.get('ObjectName') or {}).get('value', ''))])
    view = PHOTO_VIEW.search(text) is not None
    if PHOTO_NEVER.search(text) or (PHOTO_THING.search(text) and not view):
        return None
    if SPECIES.search(page.get('title', '')) and not view:
        return None  # "Anemone coronaria ...": a plant or animal
    score = 0.0
    if view:
        score += 3
    elif PHOTO_PLACE.search(text):
        score += 1.5
    if ratio >= 2:
        score += 2  # a panorama
    if page.get('categories'):
        score += 2  # a Quality image or Featured picture
    dist = ((page.get('coordinates') or [{}])[0]).get('dist')
    score -= (dist if dist is not None else PHOTO_RADIUS) / 250
    return score


def photos_near(lat, lon):
    d = commons({
        'action': 'query', 'generator': 'geosearch', 'ggsnamespace': 6, 'ggscoord': f'{lat:.5f}|{lon:.5f}',
        'ggsradius': PHOTO_RADIUS, 'ggslimit': 40,
        'prop': 'imageinfo|coordinates|categories', 'iiprop': 'size|mime|extmetadata',
        'iiextmetadatafilter': 'Artist|LicenseShortName|ImageDescription|ObjectName', 'iiextmetadatalanguage': 'en',
        'codistancefrompoint': f'{lat:.5f}|{lon:.5f}', 'colimit': 'max', 'cllimit': 'max',
        'clcategories': 'Category:Quality images|Category:Featured pictures on Wikimedia Commons',
    })
    if d is None:
        return None
    scored = []
    for page in (d.get('query') or {}).get('pages', []):
        sc = photo_score(page)
        if sc is not None and sc > -3:
            scored.append((sc, page))
    scored.sort(key=lambda t: -t[0])
    out, per_author = [], Counter()
    for sc, page in scored:
        e = photo_entry(page)
        if e and per_author[e[1]] < 2:  # not all three by one photographer
            per_author[e[1]] += 1
            out.append(e)
        if len(out) == PHOTOS:
            break
    return out


def chosen_photos(names):
    """Hand-picked files (featured.json 'photos'), with their photographer and licence."""
    d = commons({'action': 'query', 'titles': '|'.join('File:' + n for n in names), 'prop': 'imageinfo',
                 'iiprop': 'size|extmetadata', 'iiextmetadatafilter': 'Artist|LicenseShortName'})
    pages = {p.get('title'): p for p in ((d or {}).get('query') or {}).get('pages', []) if not p.get('missing')}
    return [e for e in (photo_entry(pages[t]) for t in ('File:' + n.replace('_', ' ') for n in names) if t in pages) if e]


def name_ok(name):
    """The checks a file name alone allows, for photos kept from an earlier build."""
    t = 'File:' + name
    view = PHOTO_VIEW.search(t) is not None
    return not (PHOTO_NEVER.search(t) or (PHOTO_THING.search(t) and not view) or (SPECIES.search(t) and not view))


def find_photos(views, featured, before=None):
    """Up to PHOTOS photos per viewpoint: hand-picked ones first (featured.json), then the best found nearby.
    Where a search fails, the viewpoint keeps its photos from the last build (before), if they still pass."""
    before = before or {}
    picked = {}
    for f in (featured or {}).get('views', []):
        if not f.get('photos'):
            continue
        if f.get('osm'):
            ids = [v['id'] for v in views if v['n'] == f['osm'] and not v.get('nn')]
        elif f.get('near'):
            best = min(views, key=lambda v: metres(f['near'], (v['s'][0] / Q, v['s'][1] / Q)), default=None)
            ids = [best['id']] if best and metres(f['near'], (best['s'][0] / Q, best['s'][1] / Q)) <= 500 else []
        else:
            ids = []
        chosen = chosen_photos(f['photos'])
        for i in ids:
            picked[i] = chosen
    out, failed, late = {}, 0, 0
    kept = {v['id']: [e for e in before.get(v['id'], []) if name_ok(e[0])] for v in views}
    if views and all(photos_near(v['s'][0] / Q, v['s'][1] / Q) is None for v in views[:3]):
        print(f'photos: Wikimedia Commons not answering ({dict(COMMONS_PROBLEMS)}); '
              f'the photos from the last build stay, through the name checks', flush=True)
        return {vid: e for vid, e in kept.items() if e}
    deadline = time.monotonic() + PHOTO_BUDGET
    # Viewpoints with no photos yet first; the rest from a place that moves on each month, so that within the
    # time allowed every viewpoint is searched again in turn.
    have = [v for v in views if before.get(v['id'])]
    turn = (datetime.now(timezone.utc).month * 397) % len(have) if have else 0
    views = [v for v in views if not before.get(v['id'])] + have[turn:] + have[:turn]

    def one(v):
        if time.monotonic() > deadline:
            return v['id'], 'late'
        return v['id'], photos_near(v['s'][0] / Q, v['s'][1] / Q)
    with ThreadPoolExecutor(1) as ex:
        for vid, found in ex.map(one, views):
            if found is None or found == 'late':
                if found is None:
                    failed += 1
                else:
                    late += 1
                found = kept.get(vid, [])
            mine = picked.get(vid, [])
            names = {e[0] for e in mine}
            got = (mine + [e for e in found if e[0] not in names])[:PHOTOS]
            if got:
                out[vid] = got
    print(f'photos: {len(out)} of {len(views)} viewpoints have photos, {sum(map(len, out.values()))} photos, '
          f'{failed} searches failed, {late} not searched (out of time) and kept their photos', flush=True)
    if COMMONS_PROBLEMS:
        print(f'photos: problems on the way: {dict(COMMONS_PROBLEMS)}', flush=True)
    for vid in list(out)[:5]:
        print('  e.g.', vid, [e[0] for e in out[vid]], flush=True)
    return out


def link_views(routes, members, facts, views):
    """Lists on each route the viewpoints within VIEW_ON_TRAIL metres of it, in the order they come."""
    grid = {}
    for v in views:
        grid.setdefault(grid_key(v['s'][0] / Q, v['s'][1] / Q, WATER_GRID), []).append(v)
    for o in routes:
        seen = []
        for w in dict.fromkeys(members[o['id']]):
            if w not in facts:
                continue
            for lat, lon in facts[w].samples[::2]:
                i, j = grid_key(lat, lon, WATER_GRID)
                for di in (-1, 0, 1):
                    for dj in (-1, 0, 1):
                        for v in grid.get((i + di, j + dj), ()):
                            if v['id'] not in seen and metres((lat, lon), (v['s'][0] / Q, v['s'][1] / Q)) <= VIEW_ON_TRAIL:
                                seen.append(v['id'])
        if seen:
            o['vp'] = seen


def build_routes(r, f, dem):
    named = [i for i, rec in enumerate(r.routes) if rec[0].strip()]
    facts = {}
    for i in named:
        for w in r.members[i]:
            if w not in facts and w in f.route_geom:
                facts[w] = WayFacts(f.route_geom[w])
    print(f'route finder: {len(named)} named routes, {len(facts)} ways', flush=True)
    try:
        if dem.prefetch([s for wf in facts.values() for s in wf.samples]):
            for wf in facts.values():
                wf.set_heights(dem)
    except ImportError:
        print('numpy/Pillow missing: routes written without heights', flush=True)
    out, members = [], {}
    for i in named:
        o = route_facts(r.routes[i], r.members[i], facts, f.roads, f.water)
        if o:
            out.append(o)
            members[o['id']] = r.members[i]
    with_h = sum(1 for o in out if 'up' in o)
    print(f'route finder: {len(out)} routes, {with_h} with heights', flush=True)
    return out, members, facts


def write(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(obj, f, ensure_ascii=False, separators=(',', ':'))


def main(pbf, out):
    r = Routes()
    r.apply_file(pbf)
    print(f'{len(r.routes)} routes, {len(r.way_routes)} route ways, {len(r.military)} military multipolygons', flush=True)
    f = Features(r.way_routes, r.military, r.mil_ways)
    f.apply_file(pbf, locations=True, idx='flex_mem')
    print(f'{len(f.hike)} trail cells, {len(f.topo)} topo cells, {len(f.places)} places, '
          f'{len(f.roads)} road squares, {sum(map(len, f.water.values()))} water points, '
          f'{len(f.viewpoints)} viewpoints, {len(f.peaks)} named peaks', flush=True)

    for sub in ('hike', 'topo'):
        d = os.path.join(out, sub)
        if os.path.isdir(d):
            for name in os.listdir(d):
                os.remove(os.path.join(d, name))
    for c, ways in f.hike.items():
        used = sorted({i for w in ways for i in w[1]})
        remap = {old: new for new, old in enumerate(used)}
        write(os.path.join(out, 'hike', c + '.json'),
              {'r': [r.routes[i] for i in used], 'w': [[w[0], [remap[i] for i in w[1]], w[2]] for w in ways]})
    for c, data in f.topo.items():
        write(os.path.join(out, 'topo', c + '.json'), data)
    write(os.path.join(out, 'places.json'), f.places)
    built = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    featured = None
    try:
        with open(os.path.join(out, 'featured.json'), encoding='utf-8') as fh:
            featured = json.load(fh)
    except (OSError, ValueError):
        pass
    dem = Dem()
    routes, members, facts = build_routes(r, f, dem)
    views = build_views(f, dem, featured)
    link_views(routes, members, facts, views)
    write(os.path.join(out, 'routes.json'), {'built': built, 'r': routes})
    write(os.path.join(out, 'views.json'), {'built': built, 'dirs': VIEW_DIRS, 'v': views})
    if views and os.environ.get('NO_PHOTOS') != '1':
        before = {}
        try:
            with open(os.path.join(out, 'photos.json'), encoding='utf-8') as fh:
                before = json.load(fh).get('p', {})
        except (OSError, ValueError):
            pass
        photos = find_photos(views, featured, before)
        write(os.path.join(out, 'photos.json'), {'built': built, 'p': photos})
    write(os.path.join(out, 'meta.json'), {
        'built': built, 'cell': CELL,
        'hike': sorted(f.hike), 'topo': sorted(f.topo)
    })


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
