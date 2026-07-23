"""
DIAGNOSTIC for the obligation-(b) failure on (2,3,2,2): is the out-of-cap col-2 read
(1) a real feature of the raw shears-only fold, (2) a shear/unpaired-compensator artifact,
(3) a blockCoords axis-transpose bug, or (4) a wrong (non-real) branch?

Diagnose-first (operator standing rule): print the actual residuals + isolate the cause.
"""
import sympy as sp
from cap_frontier_sufficiency import (make, layerCoords, widthMinUpto, blockCoords, supportAt,
    canonNormalizationOf, edgeShearRaw, step_arg, coreGen, real_foldResid, supported_on)

def canonCenter_append(d, S, J):
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

d = (2, 3, 2, 2); N, u = make(d)
print(f"d={d}: layer0=C0 {d[1]}x{d[0]} (rows d1={d[1]} x cols d0={d[0]});"
      f" layer1=C1 {d[2]}x{d[1]} (rows d2={d[2]} x cols d1={d[1]})")
print(f"widthMinUpto(1)=min(d0,d1)=min({d[0]},{d[1]})={widthMinUpto(d,1)}; layer1 col axis=d1={d[1]}")
print(f"blockCoords(1) caps col<{widthMinUpto(d,1)} ⟹ excludes col=2: {sorted(k for k in layerCoords(d,1) if k not in blockCoords(d,1))}")

# The branch clearing layer 0 (3x2) then rolling into layer 1.
e0 = ("case2", 0, 0, (0, 0, 0), canonCenter_append(d, 0, 0), 1)
e1 = ("case2", 0, 1, (0, 1, 1), canonCenter_append(d, 0, 1), 0)
print(f"\ncenters: e0={sorted(e0[4])}\n         e1={sorted(e1[4])}")

resid = real_foldResid(u, d, [e0, e1])
print(f"\n=== real foldResid at (0,2) [= (1,0) after rollover], {len(resid)} slots ===")
layer1 = sorted(layerCoords(d, 1))
for j, f in enumerate(resid):
    fs = sp.expand(f).free_symbols
    reads1 = [k for k in layer1 if u[k] in fs]
    print(f"  slot[{j}] reads layer-1 coords: {reads1}")
    print(f"           = {sp.expand(f)}")

# Which layer-1 coords does the WHOLE residual read?
reads_all = sorted(k for k in layer1 if any(u[k] in sp.expand(f).free_symbols for f in resid))
print(f"\n  layer-1 coords read (any slot): {reads_all}")
print(f"  caps to a 2x2 block on which axis? rows read={sorted(set(k[1] for k in reads_all))},"
      f" cols read={sorted(set(k[2] for k in reads_all))}")

# ---- ISOLATE: shears OFF (id) vs ON ----
def real_foldResid_noshear(u, d, edges):
    v = dict(u)
    for (case, sl, sc, piv, cen, delta) in reversed(edges):
        # force shear = id by using case "rollover"/"case11" semantics for the shear only
        w = dict(v)
        out = {}
        for k in v:
            if delta == 1:  out[k] = sp.Integer(1) if k == piv else w[k]
            elif case == "rollover": out[k] = w[k]
            else: out[k] = (w[piv] if k == piv else (w[piv]*w[k] if k in cen else w[k]))
        v = out
    return coreGen(v, d)

resid_ns = real_foldResid_noshear(u, d, [e0, e1])
reads_ns = sorted(k for k in layer1 if any(u[k] in sp.expand(f).free_symbols for f in resid_ns))
print(f"\n=== shears OFF (blow-ups only) ===")
print(f"  layer-1 coords read: {reads_ns}")
print(f"  col 2 read WITHOUT shear? {any(k[2]==2 for k in reads_ns)}   "
      f"(if False: col-2 is a SHEAR/unpaired-compensator artifact)")

# ---- also: does the shear (ii) at e1 write col-1 a col-2-reading term? ----
phi1 = canonNormalizationOf(u, d, 0, 1, (0, 1, 1))
print(f"\n=== shear φ at e1 (state (0,1), pivot (0,1,1)) on layer-1 col-1 coords ===")
for r in range(d[2]):
    if (1, r, 1) in phi1:
        print(f"  φ[(1,{r},1)] = {sp.expand(phi1[(1,r,1)])}")
