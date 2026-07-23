"""
Does the FAITHFUL clean D_J have R3's u001^2, or is R3's u001^2 a genuine deviation (the omitted pivot-ROW
clear)?  Faithful (honest_clear) result at the (2,2,2,2) reuse node vs R3's actual fold residual.

Mechanism (traced): R3 = −γ recoord, NO clearing. R3's u001^2 in col-1 (D_J) arises because the ed2 recoord
reads A0's UNCLEARED pivot-row entry u001 (readEntry(0,0,1)) AND the coreGen reads the uncleared A0[0][1]=u001
— two u001 sources multiply. The FAITHFUL clears the pivot row at ed1 (u001 -> 0) BEFORE ed2, so ed2's
recoord reads 0 and no u001^2 forms. So the faithful clean D_J should be degree <= 1 in u001; R3 is degree 2.
The fix (clear the pivot ROW, the U col-op twin of the column-clear) sets u001 -> 0 = rank-reducing, NOT
shear-representable — same skeleton-revision tension as the column clear, row side.
"""
import sympy as sp

# ---- R3 actual reuse-node residual (fold), (2,2,2,2) : recompute col-1 u001-degree ----
from importlib.util import spec_from_file_location, module_from_spec
import os
_here = os.path.dirname(os.path.abspath(__file__))
spec = spec_from_file_location("rn", os.path.join(_here, "r3flip_reuse_node.py"))
# r3flip_reuse_node runs report() on import; instead re-implement the tiny fold inline to avoid its prints.

def make(d):
    N = len(d) - 1
    return N, {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L+1]) for c in range(d[L])}
def rd(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S+1] and 0 <= col < d[S]) else sp.Integer(0)
def cn(u, d, sL, sC, piv, sign):
    a, b = piv[1], piv[2]; phi = {}
    for (L, r, c) in u:
        if L == sL and r != a and c != b and sC <= r and sC <= c:
            phi[(L, r, c)] = -rd(u, d, sL, r, b) * rd(u, d, sL, a, c)
        elif L == sL + 1 and c == a:
            phi[(L, r, c)] = sign * sum((rd(u, d, sL, i, b) * rd(u, d, sL+1, r, i) for i in range(d[sL+1]) if i != c), sp.Integer(0))
        else:
            phi[(L, r, c)] = sp.Integer(0)
    return phi
def ae(u, d, case, sL, sC, piv, cen, delta, sign):
    w = dict(u) if case in ("case11", "rollover") else {k: u[k] + cn(u, d, sL, sC, piv, sign)[k] for k in u}
    out = {}
    for k in u:
        if case == "rollover": out[k] = w[k]
        elif delta == 1: out[k] = sp.Integer(1) if k == piv else w[k]
        else: out[k] = (w[piv] if k == piv else (w[piv]*w[k] if k in cen else w[k]))
    return out
def core(u, d):
    N = len(d) - 1
    P = sp.Matrix(d[N], d[N-1], lambda r, c: u[(N-1, r, c)])
    for L in range(N-2, -1, -1): P = P * sp.Matrix(d[L+1], d[L], lambda r, c: u[(L, r, c)])
    return [sp.expand(P[i, j]) for i in range(P.rows) for j in range(P.cols)]
def fold(d, edges, sign):
    N, u = make(d); v = dict(u)
    for e in reversed(edges): v = ae(v, d, *e, sign)
    return core(v, d), u

br = [("case2",0,0,(0,0,0),set(),1),("case2",0,1,(0,1,1),{(0,1,1)},0),("rollover",0,2,None,set(),0)]
d = (2,2,2,2)
r3, u = fold(d, br, -1)
u001 = u[(0,0,1)]
print("R3 (−γ, NO clear) reuse-node residual, u001-degree per slot:")
for j, f in enumerate(r3):
    du = 0 if u001 not in f.free_symbols else sp.Poly(f, u001).degree()
    print(f"   slot {j}: u001-deg {du}" + ("  <-- u001^2 (D_J col-1)" if du >= 2 else ""))

# ---- FAITHFUL (honest_clear) reuse-node residual, both ± input-change ----
print("\nFAITHFUL (honest_clear: +γ recoord A1·Q1^{-1}, pivot row+col CLEARED, A0=diag(1,e2)):")
D = 2
A2 = sp.Matrix(2, 2, lambda r, c: sp.Symbol(f"a2{r}{c}"))
A1 = sp.Matrix(2, 2, lambda r, c: sp.Symbol(f"a1{r}{c}"))
u010f, u001f, e2 = sp.symbols("u010 u001 e2")
Q1inv = sp.Matrix([[1, 0], [u010f, 1]])        # +γ recoord (column-clear compensator)
w = A1 * Q1inv
D0 = sp.diag(1, e2)
Uinv = sp.Matrix([[1, u001f], [0, 1]])         # input change (pivot-row clear compensator)
for tag, Mrhs in [("with input-change Uinv", w * D0 * Uinv), ("without Uinv", w * D0)]:
    M = A2 * Mrhs
    print(f"  {tag}:")
    for i in range(2):
        for j in range(2):
            f = sp.expand(M[i, j])
            du = 0 if u001f not in f.free_symbols else sp.Poly(f, u001f).degree()
            print(f"     [{i}][{j}] u001-deg {du}: {f}")

print("\nVERDICT: faithful D_J is degree <= 1 in u001 (input-change) or 0 (no input-change); R3 is degree 2.")
print("=> R3's u001^2 is a GENUINE DEVIATION from the faithful clean D_J — the omitted pivot-ROW clear.")
print("   The row clear (u001 -> 0) is rank-reducing (not shear-representable): skeleton-revision, row side.")


# ---- DIAGNOSTIC (NOT a boostReady verdict): raw-coord degree ----
# boostReady_case11 = Deg1SupportedOn the boost CENTER, but the center is in the NORMALIZED-CHART coords
# (e2 = u011 - u010·u001, and the recoorded layer-1 w), NOT the raw {u011,u100,u110}. Since u001 is
# ENTANGLED inside e2, the raw-coord degree below is a DIAGNOSTIC ONLY — whether R3's u001^2 breaks
# boostReady is CHART-dependent and is the def-side read (seat-L4D has the exact center). Reported so the
# def-side can map it; NOT a boostReady pass/fail from this seat.
print("\n" + "=" * 72)
print("DIAGNOSTIC (raw-coord degree; NOT the boostReady verdict — chart center is def-side):")
raw_center = [u[(0,1,1)], u[(1,0,0)], u[(1,1,0)]]   # raw {u011,u100,u110} (old-shear labels; chart differs)
for j, f in enumerate(r3):
    f = sp.expand(f)
    cdeg = 0 if not any(cc in f.free_symbols for cc in raw_center) else \
        max(sum(m) for m in sp.Poly(f, *[cc for cc in raw_center if cc in f.free_symbols]).monoms())
    udeg = 0 if u001 not in f.free_symbols else sp.Poly(f, u001).degree()
    print(f"   slot {j}: raw-center-deg {cdeg}; u001-deg {udeg}")
print("=> ROBUST finding: R3's D_J is degree-2 in u001 where the FAITHFUL D_J is degree <= 1 — a genuine")
print("   deviation (the omitted pivot-ROW clear). Whether it breaks boostReady_case11 (Deg1SupportedOn the")
print("   CHART center e2/w) is chart-dependent = def-side (seat-L4D); this seat reports the deviation fact.")
