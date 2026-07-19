#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/18-fold-regroup (pnp-fold, witness). The fold-Jacobian REGROUPING cert.
#
# Verifies, by DIRECT exact symbolic composition of the max-modulus geoChartMap charts, that the
# composite Fréchet-Jacobian determinant of a root->leaf geometric path equals the per-piece ledger
# monomial  prod_k |z_{divCoord k}(w)|^{divExp k - 1}  where divExp is the stepUpdate-ACCUMULATED
# exponent. Confirms the three regrouping identities (case-2 / case-1(2) / case-1(1)) and the
# SCOPED CONDITION (diagonal birth for non-terminal divisors) whose violation is the kill-condition.
#
# Chart model (faithful to Lean geoChartMap = q.symm o (pivotChart pi x id) o q):
#   z_pi |-> z_pi ;  z_c |-> z_pi * z_c (c in center, c != pi) ;  z_c |-> z_c (spectator).
# Fold order (faithful to geomEdges: composite = geoChartMap(n) o child): ROOT outermost, DEEPEST
# node applied first to source w.
import sympy as sp

# ---- chart + composite -------------------------------------------------------
def chart(point, center, pivot):
    piv = point[pivot]
    return {c: (piv if c == pivot else (piv*point[c] if c in center else point[c])) for c in point}

def compose_and_det(path, cells):
    """path = list of node dicts {center, pivot} ROOT-FIRST. Returns factored |det D composite|."""
    src = {c: sp.Symbol('z_'+c, positive=True) for c in cells}   # positive: |.| = value, clean powers
    pt = dict(src)
    for node in reversed(path):                                   # deepest first, root last
        pt = chart(pt, node['center'], node['pivot'])
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(J.det()), src

# ---- ledger (stepUpdate accumulation) ---------------------------------------
def ledger_monomial(divisors, src):
    """divisors = list of {'coord': cellname, 'divExp': int}. Returns prod z_coord^{divExp-1}."""
    m = sp.Integer(1)
    for d in divisors:
        m *= src[d['coord']] ** (d['divExp'] - 1)
    return sp.factor(m)

# ---- scenarios: each builds (path, cells, divisors) with divExp per stepUpdate ---------------
def scen_case2_only():
    """Single case-2 birth of a 2x2 block; pivot = diagonal d00. divExp = 4."""
    cells = ['d00','d01','d10','d11']
    path = [ {'center':['d00','d01','d10','d11'], 'pivot':'d00'} ]
    divisors = [ {'coord':'d00', 'divExp': 4} ]           # case2: resRows*resCols = 2*2
    return "case-2 only (birth, diagonal pivot)", path, cells, divisors

def scen_case2_then_case11():
    """case-2 births A (exp4). Descendant case-1(1) merges into A (+ runLen*resCols = 1). divExp(A)=5."""
    cells = ['A','b','c','d','e']
    path = [ {'center':['A','b','c','d'], 'pivot':'A'},    # root case-2, births A at diagonal
             {'center':['A','e'], 'pivot':'A'} ]           # child case-1(1): merge into A (u-pivot A)
    divisors = [ {'coord':'A', 'divExp': 4 + 1} ]          # 4 birth + 1 merge
    return "case-2(birth A) + case-1(1)(merge A)", path, cells, divisors

def scen_case2_then_case12():
    """case-2 births A(exp4). Descendant case-1(2) splits new e off A: divExp(e)=divExp(A)+runLen*resCols
       =4+1=5 ; A keeps exp4. (Inheritance test.)"""
    cells = ['A','b','c','d','e']
    path = [ {'center':['A','b','c','d'], 'pivot':'A'},    # root case-2 births A
             {'center':['A','e'], 'pivot':'e'} ]           # child case-1(2): pivot e (new), u-corner A
    divisors = [ {'coord':'A','divExp':4}, {'coord':'e','divExp':5} ]
    return "case-2(birth A) + case-1(2)(split e off A) [inheritance]", path, cells, divisors

def scen_case12_then_case11():
    """depth-3: case-2 A(4); case-1(2) e off A (divExp 5); case-1(1) merge e (+1 -> 6). A stays 4."""
    cells = ['A','b','c','d','e','f']
    path = [ {'center':['A','b','c','d'], 'pivot':'A'},
             {'center':['A','e'], 'pivot':'e'},            # split e off A: divExp(e)=4+1=5
             {'center':['e','f'], 'pivot':'e'} ]           # merge into e: +1 -> 6
    divisors = [ {'coord':'A','divExp':4}, {'coord':'e','divExp':6} ]
    return "case-2(A)+case-1(2)(e off A)+case-1(1)(merge e) [inherit+accumulate]", path, cells, divisors

def scen_double_case11():
    """case-2 A(4); two case-1(1) merges into A (+1 each) -> divExp(A)=6."""
    cells = ['A','b','c','d','e','g']
    path = [ {'center':['A','b','c','d'], 'pivot':'A'},
             {'center':['A','e'], 'pivot':'A'},            # merge +1
             {'center':['A','g'], 'pivot':'A'} ]           # merge +1
    divisors = [ {'coord':'A','divExp': 4+1+1} ]
    return "case-2(A)+case-1(1)+case-1(1) [double accumulate]", path, cells, divisors

def scen_nonuniform_runlen():
    """case-2 A(2x3=6). case-1(1) merge with runLen=2,resCols=3 -> +6 -> divExp(A)=12."""
    cells = ['A','a1','a2','a3','a4','a5','m1','m2','m3','m4','m5','m6']
    resblock = ['A','a1','a2','a3','a4','a5']              # 6 cells = 2x3
    dblock   = ['m1','m2','m3','m4','m5','m6']             # 6 cells = runLen 2 x resCols 3
    path = [ {'center':resblock, 'pivot':'A'},
             {'center':['A']+dblock, 'pivot':'A'} ]        # case-1(1): u-pivot A, d-block 2x3
    divisors = [ {'coord':'A','divExp': 6 + 6} ]           # 6 birth + runLen*resCols(=6) merge
    return "case-2(2x3, A)+case-1(1)(runLen2 x resCols3) [non-uniform block]", path, cells, divisors

def scen_two_independent():
    """Two divisors born at different levels, non-interacting; both terminal off... use diagonal births.
       case-2 A(4) at root; child case-2 B(4) in the residual; both terminal. Product z_A^3 z_B^3."""
    cells = ['A','b','c','d','B','p','q','r']
    path = [ {'center':['A','b','c','d'], 'pivot':'A'},    # births A
             {'center':['B','p','q','r'], 'pivot':'B'} ]   # births B (disjoint cells)
    divisors = [ {'coord':'A','divExp':4}, {'coord':'B','divExp':4} ]
    return "case-2(A)+case-2(B) [two independent divisors]", path, cells, divisors

SCENARIOS = [scen_case2_only, scen_case2_then_case11, scen_case2_then_case12,
             scen_case12_then_case11, scen_double_case11, scen_nonuniform_runlen,
             scen_two_independent]

def run_positive():
    print("== POSITIVE: composite Jacobian == ledger monomial (diagonal births) ==")
    allok = True
    for s in SCENARIOS:
        name, path, cells, divisors = s()
        det, src = compose_and_det(path, cells)
        led = ledger_monomial(divisors, src)
        ok = sp.simplify(det - led) == 0
        allok = allok and ok
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
        print(f"         |det| = {det}")
        print(f"         ledger= {led}")
    return allok

def run_killcondition():
    print()
    print("== KILL-CONDITION: OFF-DIAGONAL birth of a NON-TERMINAL divisor breaks the identity ==")
    # case-2 births a 2x2 block at OFF-diagonal pivot d11; child case-1(1) merges via DIAGONAL d00
    # (divBirthCoord is always the diagonal). Ledger (per-pivot finding-3) names d11 with divExp 5.
    cells = ['d00','d01','d10','d11','e']
    path = [ {'center':['d00','d01','d10','d11'], 'pivot':'d11'},   # OFF-diagonal birth
             {'center':['d00','e'], 'pivot':'d00'} ]                # merge via diagonal corner
    det, src = compose_and_det(path, cells)
    led = ledger_monomial([{'coord':'d11','divExp':5}], src)
    broke = sp.simplify(det - led) != 0
    print(f"  off-diagonal birth + descendant merge:")
    print(f"     |det|  = {det}   (exponent SPLIT across diagonal d00 and pivot d11)")
    print(f"     ledger = {led}   (finding-3 names the off-diagonal pivot d11)")
    print(f"  [{'CONFIRMED' if broke else 'NOT-BROKEN'}] identity fails off-diagonal => "
          f"SCOPED CONDITION: non-terminal divisors must be born at their diagonal corner")
    # and confirm the DIAGONAL version of the SAME shape passes (control)
    path2 = [ {'center':['d00','d01','d10','d11'], 'pivot':'d00'},
              {'center':['d00','e'], 'pivot':'d00'} ]
    det2, src2 = compose_and_det(path2, cells)
    led2 = ledger_monomial([{'coord':'d00','divExp':5}], src2)
    ctrl = sp.simplify(det2 - led2) == 0
    print(f"  [{'PASS' if ctrl else 'FAIL'}] control (same shape, DIAGONAL birth): |det|={det2} == ledger")
    return broke and ctrl

if __name__ == "__main__":
    ok1 = run_positive()
    ok2 = run_killcondition()
    print()
    print("VERDICT:", "PASS -- all diagonal-birth scenarios match ledger; kill-condition witnessed"
          if (ok1 and ok2) else "FAIL")
    import sys; sys.exit(0 if (ok1 and ok2) else 1)
