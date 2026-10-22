#!/usr/bin/env python3
"""Builds the map data that ships with the app, from an OpenStreetMap extract of Israel.

    python tools/build_data.py israel-and-palestine-latest.osm.pbf data

Writes, under the output folder:
  meta.json          build date, grid cell size, and which cells have data
  places.json        names of towns, villages and places (whole country, one file)
  hike/<i>_<j>.json  marked trails and bike trails, per grid cell
  topo/<i>_<j>.json  dirt roads, paths, streams, peaks and springs, per grid cell

Coordinates are integers in 1e-5 degrees (about 1 m). A line is stored as
[lat0, lon0, dlat1, dlon1, ...]: its first point, then the step to each next point.
A way that crosses several cells is written to each of them; the app skips repeats by id.
"""
import json
import math
import os
import re
import sys
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


class Routes(osmium.SimpleHandler):
    """Pass 1: marked trail and bike route relations, and the ways they use."""
    def __init__(self):
        super().__init__()
        self.routes = []          # [name, mark, kind, israelTrail]
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
        self.routes.append([t.get('name:he') or t.get('name') or '', mark or '', kind, 1 if nat else 0])
        for m in r.members:
            if m.type == 'w':
                self.way_routes.setdefault(m.ref, []).append(idx)


class Features(osmium.SimpleHandler):
    """Pass 2: geometry of trail ways, topographic ways, and named points."""
    def __init__(self, way_routes):
        super().__init__()
        self.way_routes = way_routes
        self.hike = {}            # cell -> list of [id, route idxs, coords]
        self.topo = {}            # cell -> {'t': [...], 'p': [...]}
        self.places = []

    def node(self, n):
        if not n.location.valid():
            return
        lat, lon = n.location.lat, n.location.lon
        if not inside(lat, lon):
            return
        t = n.tags
        name = t.get('name:he') or t.get('name') or ''
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
        if routes is None and kind is None:
            return
        pts = []
        for nd in w.nodes:
            if not nd.location.valid():
                continue
            p = (round(nd.location.lat * Q), round(nd.location.lon * Q))
            if not pts or pts[-1] != p:
                pts.append(p)
        if len(pts) < 2:
            return
        if not any(inside(y / Q, x / Q) for y, x in pts):
            return
        g = encode(simplify(pts))
        cells = cells_of(pts)
        if routes is not None:
            for c in cells:
                self.hike.setdefault(c, []).append([w.id, routes, g])
        if kind is not None:
            for c in cells:
                self.topo.setdefault(c, {'t': [], 'p': []})['t'].append([w.id, kind, g])


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
    print(f'{len(f.hike)} trail cells, {len(f.topo)} topo cells, {len(f.places)} places', flush=True)

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
    write(os.path.join(out, 'meta.json'), {
        'built': datetime.now(timezone.utc).strftime('%Y-%m-%d'), 'cell': CELL,
        'hike': sorted(f.hike), 'topo': sorted(f.topo)
    })


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
