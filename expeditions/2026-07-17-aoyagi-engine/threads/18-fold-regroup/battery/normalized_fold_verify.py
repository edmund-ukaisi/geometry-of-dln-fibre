#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/18-fold-regroup (pnp-fold). Follow-up: verify the NORMALIZED fold (geoChartMapNorm =
# geoChartMap o S, S = flatSwapCLE(pivot, diagTargetOf) the source swap that relocates the exceptional
# divisor to the diagonal) reproduces the ledger identity with divCoord = the DIAGONAL cell for EVERY
# fan-out copy (including off-diagonal pivots). This confirms t14's "kill-condition dissolved" claim and
# grounds the threaded-cocycle cert. Exact symbolic.
import sympy as sp

def swap(point, a, b):
    out = dict(point)
    out[a], out[b] = point[b], point[a]
    return out

def blowup(point, center, pivot):
    piv = point[pivot]
    return {c: (piv if c == pivot else (piv*point[c] if c in center else point[c])) for c in point}

def norm_chart(point, center, pivot, diag):
    """geoChartMapNorm = geoChartMap(center,pivot) o swap(pivot,diag)."""
    return blowup(swap(point, pivot, diag), center, pivot)

def compose_norm(path, cells):
    """path ROOT-first; each node {center, pivot, diag}. Root outermost (deepest applied first).
       Returns |det| (the swap S is a transposition, det S = -1; the Jacobian ATOM uses |det|,
       matching flatSwapCLE_abs_det_fderiv_one)."""
    src = {c: sp.Symbol('z_'+c, positive=True) for c in cells}
    pt = dict(src)
    for node in reversed(path):
        pt = norm_chart(pt, node['center'], node['pivot'], node['diag'])
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(sp.Abs(J.det())), src

def ledger(divs, src):
    m = sp.Integer(1)
    for d in divs:
        m *= src[d['coord']] ** (d['divExp'] - 1)
    return sp.factor(m)

def check(name, path, cells, divs):
    det, src = compose_norm(path, cells)
    led = ledger(divs, src)
    ok = sp.simplify(det - led) == 0
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
    print(f"        |det| = {det}")
    print(f"        ledger= {led}")
    return ok

if __name__ == "__main__":
    print("== NORMALIZED fold (geoChartMap o S): divCoord = DIAGONAL for ALL fan-out pivots ==")
    allok = True

    # (N1) case-2 births A: 2x2 block {dA(diag), x01, x10, x11}, fan-out pivot = x11 (OFF-diagonal),
    #      diag target dA. Terminal. Ledger names dA (the diagonal) with divExp 4.
    cells = ['dA','x01','x10','x11']
    p = [ {'center':['dA','x01','x10','x11'], 'pivot':'x11', 'diag':'dA'} ]
    allok &= check("N1 case-2 birth, OFF-diagonal fan-out pivot x11, diag dA (terminal)",
                   p, cells, [{'coord':'dA','divExp':4}])

    # (N2) case-2 births A off-diag pivot, THEN case-1(1) merges into A via A's diagonal dA.
    #      This is the exact shape that BROKE un-normalized (probe_diagonal). Should now PASS.
    cells = ['dA','x01','x10','x11','e']
    p = [ {'center':['dA','x01','x10','x11'], 'pivot':'x11', 'diag':'dA'},   # off-diag fan-out pivot
          {'center':['dA','e'], 'pivot':'dA', 'diag':'dA'} ]                 # case-1(1): pivot=diag, S=id
    allok &= check("N2 case-2(off-diag pivot) + case-1(1) merge via diagonal dA  [was the kill-condition]",
                   p, cells, [{'coord':'dA','divExp':5}])

    # (N3) case-2 births A (off-diag pivot); case-1(2) splits B off A. B's fan-out pivot OFF-diagonal
    #      (yB), diag target dB. u-corner = dA. case-1(2) center {dA,dB,yB} => dCN=3, d-block {dB,yB}
    #      size 2 = runLen*resCols. Inheritance: divExp(B) = divExp(A)+2 = 4+2 = 6.
    cells = ['dA','x01','x10','x11','dB','yB']
    # case-1 center = {u-corner dA} u {d-block {dB(diag), yB}}; fan-out pivot yB (off-diag), diag dB
    p = [ {'center':['dA','x01','x10','x11'], 'pivot':'x11', 'diag':'dA'},
          {'center':['dA','dB','yB'], 'pivot':'yB', 'diag':'dB'} ]
    allok &= check("N3 case-2(off-diag) + case-1(2) split B off A (off-diag pivot yB, diag dB) [inherit]",
                   p, cells, [{'coord':'dA','divExp':4}, {'coord':'dB','divExp':6}])

    # (N4) depth-3 MIXED (the charge's requested run): case-2 A ; case-1(2) split B off A ; case-1(1)
    #      merge into B. Off-diagonal fan-out pivots where applicable; track through every step.
    #      Ledger: A divExp 4 ; B divExp = 4+2 (split, d-block {dB,yB} size 2) then +1 (merge {dB,f}) = 7.
    #      => z_dA^3 * z_dB^6.
    cells = ['dA','x01','x10','x11','dB','yB','f']
    p = [ {'center':['dA','x01','x10','x11'], 'pivot':'x11', 'diag':'dA'},   # case-2 births A
          {'center':['dA','dB','yB'], 'pivot':'yB', 'diag':'dB'},           # case-1(2) split B off A
          {'center':['dB','f'], 'pivot':'dB', 'diag':'dB'} ]                # case-1(1) merge into B (S=id)
    allok &= check("N4 depth-3 MIXED case2(A)+case12(B off A)+case11(merge B) [inherit+accumulate]",
                   p, cells, [{'coord':'dA','divExp':4}, {'coord':'dB','divExp':7}])

    # (N5) two off-diagonal fan-out copies of the SAME case-2 node share the diagonal divCoord (finding-3
    #      dissolved): both pivots x01 and x11, terminal; both give z_dA^3.
    cells = ['dA','x01','x10','x11']
    for piv in ['x01','x10','x11','dA']:
        p = [ {'center':['dA','x01','x10','x11'], 'pivot':piv, 'diag':'dA'} ]
        allok &= check(f"N5 case-2 fan-out pivot {piv} -> divCoord dA (per-pivot divCoord dissolved)",
                       p, cells, [{'coord':'dA','divExp':4}])

    print()
    print("VERDICT:", "PASS -- normalized fold puts every divisor on its diagonal; ledger identity holds "
          "for all fan-out pivots (kill-condition dissolved by S)" if allok else "FAIL")
    import sys; sys.exit(0 if allok else 1)
