#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/15-psi-adjudication (pnp-psi). T2(b) refinement: is the per-edge-psi gap
#   FUNDAMENTAL (strictly-interior points, unfixable by enlarging R/domains) or merely the R<2
#   scaling artifact Leg 2 already flagged (boundary points, fixable)?
#   Two independent checks:
#   (I) strictly-interior gap search at the 2x2+u node with the ACTUAL bilinear Schur gauge,
#       using a GENEROUS source domain (R_src large) so a boundary/scaling gap would be filled.
#   (II) minimal analog: u-sector (psi=id) adjacent to a single d-sector (psi=Schur, BILINEAR),
#       reproduce the challenge's interior-gap mechanism with the real form (not the toy y^2).
from fractions import Fraction as F
from itertools import product
import sys

D11,D12,D21,D22,U = 0,1,2,3,4
NC = 5

def is_in_sector(e, y, Rsrc):
    """y is in edge e's PRE-gauge source image (max-modulus sector) with pivot ranging up to Rsrc,
       ratios up to 1.  i.e. |y_e| <= Rsrc and |y_k| <= |y_e| for all k."""
    if y[e] == 0:
        return all(v == 0 for v in y)
    return abs(y[e]) <= Rsrc and all(abs(y[k]) <= abs(y[e]) for k in range(NC))

def psi_inv(e, p):
    p = list(p)
    if e == U: return tuple(p)
    if e == D11 and p[D11] != 0:   p[D22] += p[D21]*p[D12]/p[D11]
    elif e == D12 and p[D12] != 0: p[D21] += p[D22]*p[D11]/p[D12]
    elif e == D21 and p[D21] != 0: p[D12] += p[D11]*p[D22]/p[D21]
    elif e == D22 and p[D22] != 0: p[D11] += p[D12]*p[D21]/p[D22]
    return tuple(p)

def covered_peredge(p, Rsrc):
    return any(is_in_sector(e, psi_inv(e, p), Rsrc) for e in range(NC))

def check_interior(steps=6, Rtarget=F(1,2), Rsrc=F(10)):
    """Search STRICTLY-INTERIOR target points |coord| <= Rtarget < 1 covered by pure family but
       missed by the per-edge family EVEN with a generous source domain Rsrc=10 (so any
       scaling/boundary gap is filled; a residual gap is FUNDAMENTAL)."""
    vals = [(-Rtarget + F(2,1)*Rtarget*s/steps) for s in range(steps+1)]
    gaps = []
    for p in product(vals, repeat=NC):
        # pure family always covers (some coord is max) -- restrict to genuinely interior d-max pts
        if not covered_peredge(p, Rsrc):
            gaps.append(p)
    return gaps

def check_toy_realform():
    """(II) 2D analog with the REAL bilinear Schur shape. Two max-modulus sectors of (x,y,z):
       treat z as the residual coord updated by a bilinear x*y term on ONE sector only.
       u-sector S_u = {x,y <= |z|} carries psi=id; d-sector S_d = {|z|<=|x|, |y|<=|x|} (x-max)
       carries the Schur residual z -> z - (y)*(z/x)?  -- use the exact 2x2+u node instead and
       exhibit ONE interior witness with rationals, mirroring the challenge's (-t+t^2/2, t)."""
    # exact interior witness family, mirroring the challenge: pick d11=d12=d21 = -t, d22 slightly
    # off, u small. Show it is x-max territory yet psi_inv pushes it out of every sector.
    outs = []
    for t in [F(1,2), F(2,5), F(3,10), F(1,4)]:
        p = (-t, -t, -t, -t + t*t/2, -t/3)   # interior for t<1
        cov = {e: is_in_sector(e, psi_inv(e, p), F(10)) for e in range(NC)}
        pure = any((p[e]!=0 and all(abs(p[k])<=abs(p[e]) for k in range(NC))) for e in range(NC))
        outs.append((t, p, pure, cov, any(cov.values())))
    return outs

if __name__ == "__main__":
    print("T2(b) refinement — is the per-edge gap FUNDAMENTAL (interior) or a scaling artifact?")
    gaps = check_interior()
    print(f"  (I) strictly-interior gap points (|coord|<=1/2, generous source R=10): {len(gaps)}")
    if gaps:
        for g in gaps[:3]:
            print("      interior gap witness:", [str(v) for v in g])
    print()
    print("  (II) challenge-shaped interior witnesses (real bilinear Schur form):")
    for (t,p,pure,cov,anycov) in check_toy_realform():
        print(f"      t={t}: p={[str(v) for v in p]} pure-covered={pure} per-edge-covered={anycov}")
    fundamental = len(gaps) > 0
    print()
    if fundamental:
        print("VERDICT: the per-edge-psi gap is FUNDAMENTAL (strictly-interior, survives R=10 source).")
        print("  => R-a (per-edge psi in the cover) is NOT a sound cover without domain surgery;")
        print("     the id-sector / Schur-sector boundary cannot be matched. R-b avoids it.")
    else:
        print("VERDICT: no interior gap under generous source -> the gap was a SCALING artifact (Leg-2),")
        print("  => R-a per-edge cover is recoverable by enlarging domains; gap is not fundamental.")
    sys.exit(0)
