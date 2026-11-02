#!/usr/bin/env python3
"""Builds the map data that ships with the app, from an OpenStreetMap extract of Israel.

    python tools/build_data.py israel-and-palestine-latest.osm.pbf data

Writes, under the output folder:
  meta.json          build date, grid cell size, and which cells have data
  places.json        names of towns, villages and places (whole country, one file)
  hike/<i>_<j>.json  marked trails and bike trails, per grid cell
  topo/<i>_<j>.json  dirt roads, paths, streams, peaks and springs, per grid cell
  routes.json        facts about each named trail, for the route finder: length, climb,
                     shape, start point, water on the way, road access (see route_facts)

Coordinates are integers in 1e-5 degrees (about 1 m). A line is stored as
[lat0, lon0, dlat1, dlon1, ...]: its first point, then the step to each next point.
A way that crosses several cells is written to each of them; the app skips repeats by id.

Heights for routes.json come from open elevation tiles (Mapterhorn, Copernicus GLO-30, with
AWS Terrain Tiles as the backup), the same sources the app draws its contour lines from.
Without them (no network) the routes are still written, without climb figures.
"""
import io
import json
import math
import os
import re
import sys
import time
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
    """Pass 1: marked trail and bike route relations, and the ways they use."""
    def __init__(self):
        super().__init__()
        self.routes = []          # [name, mark, kind, israelTrail, relation id]
        self.members = []         # way ids of each route, in relation order
        self.way_routes = {}      # way id -> [route index]

    def relation(self, r):
        t = {k.k: k.v for k in r.tags}
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
    def __init__(self, way_routes):
        super().__init__()
        self.way_routes = way_routes
        self.hike = {}            # cell -> list of [id, route idxs, coords]
        self.topo = {}            # cell -> {'t': [...], 'p': [...]}
        self.places = []
        self.route_geom = {}      # trail way id -> [(lat, lon) in quanta]
        self.roads = set()        # ROAD_GRID squares with a paved road or car park
        self.water = {}           # WATER_GRID square -> [[lat, lon, kind, name]] (quanta)

    def add_road(self, pts):
        for (y0, x0), (y1, x1) in zip(pts, pts[1:] or pts):
            n = max(1, int(max(abs(y1 - y0), abs(x1 - x0)) / Q / (ROAD_GRID / 2)))
            for k in range(n + 1):
                self.roads.add(grid_key((y0 + (y1 - y0) * k / n) / Q, (x0 + (x1 - x0) * k / n) / Q, ROAD_GRID))

    def node(self, n):
        if not n.location.valid():
            return
        lat, lon = n.location.lat, n.location.lon
        if not inside(lat, lon):
            return
        t = n.tags
        name = t.get('name:he') or t.get('name') or ''
        if t.get('amenity') == 'parking':
            self.roads.add(grid_key(lat, lon, ROAD_GRID))
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
        if routes is None and kind is None and not road:
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
        if road:
            self.add_road(pts)
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

    def __init__(self):
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
    return out


def build_routes(r, f):
    named = [i for i, rec in enumerate(r.routes) if rec[0].strip()]
    facts = {}
    for i in named:
        for w in r.members[i]:
            if w not in facts and w in f.route_geom:
                facts[w] = WayFacts(f.route_geom[w])
    print(f'route finder: {len(named)} named routes, {len(facts)} ways', flush=True)
    dem = Dem()
    try:
        if dem.prefetch([s for wf in facts.values() for s in wf.samples]):
            for wf in facts.values():
                wf.set_heights(dem)
    except ImportError:
        print('numpy/Pillow missing: routes written without heights', flush=True)
    out = []
    for i in named:
        o = route_facts(r.routes[i], r.members[i], facts, f.roads, f.water)
        if o:
            out.append(o)
    with_h = sum(1 for o in out if 'up' in o)
    print(f'route finder: {len(out)} routes, {with_h} with heights', flush=True)
    return out


def write(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(obj, f, ensure_ascii=False, separators=(',', ':'))


def main(pbf, out):
    r = Routes()
    r.apply_file(pbf)
    print(f'{len(r.routes)} routes, {len(r.way_routes)} route ways', flush=True)
    f = Features(r.way_routes)
    f.apply_file(pbf, locations=True, idx='flex_mem')
    print(f'{len(f.hike)} trail cells, {len(f.topo)} topo cells, {len(f.places)} places, '
          f'{len(f.roads)} road squares, {sum(map(len, f.water.values()))} water points', flush=True)

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
    write(os.path.join(out, 'routes.json'), {'built': built, 'r': build_routes(r, f)})
    write(os.path.join(out, 'meta.json'), {
        'built': built, 'cell': CELL,
        'hike': sorted(f.hike), 'topo': sorted(f.topo)
    })


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
