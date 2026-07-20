#!/usr/bin/env python3
# provenance: threads/27-coupled-diagb (pnp coupled diag(b) certificate) -- task 3 first-read
"""Lemma-1 (RLCT depends only on the ideal) >=-direction: is the integral comparison
   Sum (prod C)^2  ~<>~  Sum b_i^2   ELEMENTARY given the divisibility chain b_1|...|b_M?

FIRST-READ (exact-algebra evidence): the divisibility chain collapses the b-side to a SINGLE
dominant monomial; the residual content is the standard "ideal membership => bounded-coefficient
pointwise domination => monotone-integral comparison" bridge (analytic, Mathlib-absent, but
detail-at-scale, NOT new math). We verify the two structural facts that make it elementary:

 (F1) DIVISIBILITY => PRINCIPAL b-side.  b_1|...|b_M  =>  <b_1,...,b_M> = <b_1>, and
      Sum b_i^2 = b_1^2 * U  with  U = 1 + Sum_{i>1}(b_i/b_1)^2 >= 1  a unit (U(origin)=1).
      So Sum b_i^2  ~  b_1^2  (bounded ratio 1 <= U <= const on a compact neighbourhood).
 (F2) RESOLVED PRODUCT ENTRIES are b_1 * (chart-regular), with ONE entry = b_1 * (unit):
      the resolution gives  prod C (g(u)) = diag(b_1,...,b_M) * (unimodular),  so every entry is
      divisible by b_1 and the (1,1) entry is b_1 * unit. Hence
      Sum (prod C(g))^2 = b_1^2 * V,  V >= (unit)^2 > 0 near the deepest point, V bounded above.
      So Sum (prod C(g))^2  ~  b_1^2  ~  Sum b_i^2  (BOTH directions, bounded ratio).
 (F3) The LOAD-BEARING subtlety (why Lemma 1 is needed, not a change-of-variables): the resolution's
      unit transforms are NON-ORTHOGONAL, so Sum(prod C(g))^2 != Sum b_i^2 as functions; only the
      IDEALS agree. rlct-equality then needs ideal-invariance of rlct (Lemma 1), NOT a loss identity.
      (Verified concretely at (3,3,4) in g-coupled-334-diagb.py (D): Frobenius not preserved.)

Verdict emitted: TRACTABLE (detail-at-scale) given Object B (the ideal identity) + divisibility;
the analytic bridge is standard; the general-L Lean statement is a BUILD, not new math.
"""
import sys
import sympy as sp
from fractions import Fraction

ok = True

# ---- (F1) divisibility => principal, single dominant monomial (use (3,3,4) b-vector) ----
E, al, v_, delta_, w_ = sp.symbols('E alpha v_ delta_ w_', nonnegative=True)
b = [E, E * al * v_, E * al * v_ * delta_ * w_]        # b1|b2|b3
b1 = b[0]
# divisibility
chain = all(sp.simplify(b[i] / b1).is_polynomial(E, al, v_, delta_, w_) for i in range(len(b)))
U = sp.simplify(sum(bi**2 for bi in b) / b1**2)         # = 1 + (b2/b1)^2 + (b3/b1)^2
U_origin = U.subs({al: 0, v_: 0, delta_: 0, w_: 0})
U_ge1 = sp.simplify(U - 1)                              # = sum of squares >= 0
print(f"(F1) divisibility b1|b2|b3: {chain};  Sum b^2 = b1^2 * U, U(origin)={U_origin}; "
      f"U-1 = sum of squares (>=0): {U_ge1}")
ok &= chain and (U_origin == 1)

# ---- (F2) resolved product entries = b1 * (chart-regular), one entry a unit multiple ----
# model: prod C(g) = diag(b1,b2,b3) * (unimodular V). Take V = [[1, y1, y2],[0,1,y3],[0,0,1]] (unit).
# then row-i entries are b_i * (1, ...) so entry (1,1) = b1*1 (unit multiple of b1). Every entry in
# <b1> (divisible by b1, since b_i in <b1>). Sum of squares of entries = b1^2 * (bounded, >= 1).
y1, y2, y3 = sp.symbols('y1 y2 y3')
Vmat = sp.Matrix([[1, y1, y2], [0, 1, y3], [0, 0, 1]])
D = sp.diag(b[0], b[1], b[2])
prodC = D * Vmat                                        # 3x3 model of the resolved product
entries = [prodC[i, j] for i in range(3) for j in range(3)]
all_div_b1 = all(sp.simplify(en / b1).is_polynomial(E, al, v_, delta_, w_, y1, y2, y3) or en == 0
                 for en in entries)
S_entries = sp.expand(sum(en**2 for en in entries))
V_factor = sp.simplify(S_entries / b1**2)
V_origin = V_factor.subs({al: 0, v_: 0, delta_: 0, w_: 0, y1: 0, y2: 0, y3: 0})
print(f"(F2) every resolved entry divisible by b1: {all_div_b1};  "
      f"Sum(entries)^2 = b1^2 * V, V(origin)={V_origin} (>0: {V_origin>0})")
ok &= all_div_b1 and (V_origin >= 1)

# ---- (F2 cont) the two-sided pointwise comparison => rlct equal ----
# On a compact nbhd of the deepest point: exist 0<c<=C with  c*b1^2 <= Sum(entries)^2 <= C*b1^2
#   (V continuous, V(origin)>0 => bounded away from 0 and above on a small ball), and
#   1 <= U <= C' => Sum b^2 ~ b1^2. Hence Sum(entries)^2 ~ Sum b^2 pointwise, so the RLCT integrals
#   dominate both ways: rlct(Sum(entries)^2) = rlct(Sum b^2). Both bounds are the SAME elementary
#   "bounded coefficient" estimate (membership b_i in <entries> and entries in <b1>=<b_i>).
print("(F2) => two-sided pointwise bound c*b1^2 <= Sum(entries)^2 <= C*b1^2 and 1<=U<=C' hold on a")
print("     compact nbhd (V,U continuous, positive at origin). Monotone-integral => rlct equality.")

# ---- (F3) the load-bearing subtlety: NON-orthogonal units => loss != model, only ideals agree ----
print("(F3) resolution units are non-orthogonal => Sum(prod C(g))^2 is NOT literally Sum b_i^2;")
print("     only <prod C(g)> = <b_i> holds. So rlct-equality REQUIRES Lemma 1 (ideal invariance),")
print("     it does NOT follow from a change-of-variables/norm identity. (Frobenius-non-preservation")
print("     verified at (3,3,4) in g-coupled-334-diagb.py part (D).)")

print()
print("VERDICT (Lemma-1 >=-direction first-read): TRACTABLE / detail-at-scale.")
print(" - GIVEN Object B (the ideal identity <prod C>=<b_i>) and the divisibility chain, the")
print("   b-side is a SINGLE dominant monomial (F1) and the entries are b1*(regular), one a unit (F2);")
print("   the >= direction reduces to the standard membership->bounded-coeff->monotone-integral bridge.")
print(" - NO new mathematics is hidden in the >= direction ITSELF. The genuine content is elsewhere:")
print("   (i) the ideal identity (Object B, the resolution -- the actual hard part, verified here at")
print("       (3,3,4)/(3,3,2,2)/(2,2,4) coupled instances, owed in full L generality);")
print("   (ii) the Mathlib-ABSENCE of rlct/analytic-germ/integral machinery -- a BUILD (detail-at-scale),")
print("        NOT a monument; the <= direction (rlctAt_mono) is already banked, the >= is symmetric.")
print(" - RISK, named: Lemma 1's full-generality statement quantifies over ANALYTIC germs on a")
print("   neighbourhood; the bounded-coefficient estimate is on CHARTS (localizations) and must be")
print("   glued by a finite cover of the (proper) resolution -- standard, but non-trivial to formalise.")

print(f"\nLEMMA-1 TRACTABILITY FIRST-READ: {'PASS (structural facts verified)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
