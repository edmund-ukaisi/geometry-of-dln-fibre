#!/usr/bin/env python3
"""L7 case-11 fan adjudication — the exact (2,2,2,2) witness (pnp-fan, 2026-07-22).

Verifies EXACTLY (fractions.Fraction, no float) at the FIRST case-11 (merge) node of the real
(2,2,2,2) resolution tree that the COVER does NOT need case-11 interior fan pivots:

  (A) a c0-argmax point is covered by the case-11 CANONICAL pivot c0 (the merged birth corner);
  (B) a B-argmax point (a current-layer block coord > c0) is covered by the case-1(2) SIBLING's fan,
      with c0 FIXED as a spectator (ledger-corner-preserving) — NOT by a case-11 interior pivot;
  (H) the case-11 INTERIOR pivot MOVES c0 (image_{c0} = w_p*w_{c0} != w_{c0}), which is why the naive
      `pivot in canonCenterOf` membership pin broke stepMapRaw_fixes_parentLedgerCorner.

Verdict: covered-under-(b); ledger-corner-preserving (a) coincides with (b) at case-11.

The first case-11 node (from the faithful oracle trace, map/battery/_edgespec_traversal_334.py):
  Lean layer S=1, cleared J=0, path ['2','2','R']; merges the divisor born at (layer 0, cleared 1).
"""
from fractions import Fraction as F

d = [2, 2, 2, 2]                      # d_0..d_3 ; Lean N=3, layers 0,1,2 ; flatDim=12
def wmu(n): return min(d[: n + 1])    # widthMinUpto

S, J = 1, 0
c0 = (0, 1, 1)                        # merged divisor's birth corner (layer 0 < S), = canonPivotOf(case11)
runLen, resCols = 1, d[S + 1] - J     # =2 ; bump = runLen*resCols = 2

B        = [(S, r, cc) for r in range(d[S + 1]) for cc in range(d[S]) if J <= r and J <= cc and cc < J + runLen]
center11 = [c0] + B
center12 = [(S, r, cc) for r in range(d[S + 1]) for cc in range(d[S]) if J <= r and J <= cc and cc < wmu(S)]
coords   = [(l, r, cc) for l in range(3) for r in range(d[l + 1]) for cc in range(d[l])]

def BB(center, piv, w):               # blockBlowupMap on flat coords: piv->w_piv, center\{piv}->w_piv*w_k, spectators fixed
    return {k: (w[piv] if k == piv else (w[piv] * w[k] if k in center else w[k])) for k in coords}

def lift(center, piv, x):             # argmax lift: pivot slot=x_piv, ratio=x_k/x_piv (center), spectator=x_k
    out = {}
    for k in coords:
        if k == piv:        out[k] = x[k]
        elif k in center:   out[k] = (x[k] / x[piv]) if x[piv] != 0 else F(0)
        else:               out[k] = x[k]
    return out

ok = True
# structural facts
ok &= (len(center11) - 1 == runLen * resCols)          # Jac exponent = bump
ok &= all(b in center12 for b in B)                    # B subset of sibling center
ok &= (c0 not in center12)                             # c0 is a sibling spectator
# ledger-preserving pivots at case11 = {p in center : c0 not in center\{p}} = {c0}
ledger_preserving_11 = [p for p in center11 if c0 not in [q for q in center11 if q != p]]
ok &= (ledger_preserving_11 == [c0])
print("structure: |center11|-1 =", len(center11) - 1, "= bump", runLen * resCols,
      "; B⊆case12:", all(b in center12 for b in B), "; c0 spectator of case12:", c0 not in center12,
      "; ledger-preserving @case11:", ledger_preserving_11)

eps = F(1, 3)
# (A) c0-argmax -> case11 canonical pivot c0
xA = {k: F(0) for k in coords}; xA[c0] = eps; xA[(1, 0, 0)] = F(1, 9)
wA = lift(center11, c0, xA); imgA = BB(center11, c0, wA)
A = all(imgA[k] == xA[k] for k in coords) and all(abs(wA[k]) <= 1 for k in center11 if k != c0)
print("(A) c0-argmax covered by case11 canonical pivot c0:", A)
ok &= A

# (B) B-argmax -> case12 sibling, c0 fixed spectator ; case11 canonical fails
xB = {k: F(0) for k in coords}; xB[(1, 0, 0)] = eps; xB[c0] = F(1, 9)
case11_fails = abs(xB[(1, 0, 0)] / xB[c0]) > 1
wB = lift(center12, (1, 0, 0), xB); imgB = BB(center12, (1, 0, 0), wB)
B_ok = all(imgB[k] == xB[k] for k in coords) and imgB[c0] == xB[c0] and all(abs(wB[k]) <= 1 for k in center12 if k != (1, 0, 0))
print("(B) B-argmax: case11-canonical fails (ratio>1):", case11_fails,
      "; covered by case12 sibling with c0 fixed:", B_ok)
ok &= case11_fails and B_ok

# (H) case11 INTERIOR pivot moves c0
wH = {k: F(0) for k in coords}; wH[(1, 0, 0)] = F(1, 2); wH[c0] = F(1, 2)
moved = BB(center11, (1, 0, 0), wH)[c0] != wH[c0]
print("(H) case11 interior pivot (1,0,0) MOVES c0 (breaks parentLedgerCorner):", moved)
ok &= moved

print("\nCASE-11 FAN ADJUDICATION:", "PASS (covered-under-(b); (a)≡(b) @case11)" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
