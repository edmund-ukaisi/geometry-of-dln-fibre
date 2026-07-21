#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Fidelity tie: the Lean `weightedCofactor`
# (Core.Aoyagi.WeightedCofactor) reproduces the thread-34 certificate's printed Q̂, §4 minimal (2,2,1).
"""
The Lean `weightedCofactor c R` builds Q̂ ENTRYWISE as `Q̂ a d = c a d * R a d`, where R = Q₁⁻¹ and
c is the divisibility ratio (b_a = c a d · b_d on supp R). This battery checks — EXACTLY (sympy) —
that this entrywise Q̂ (with the ratio c chosen from the b'-chain) equals the certificate's
CONJUGATION Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹, and its printed value [[1,0],[e'z,1]] (codex answer §4),
and that the inverse-free commutation `diag(b')·Q₁⁻¹ = Q̂·diag(b')` (the Lean lemma
`diagonal_mul_eq_weightedCofactor_mul_diagonal`) holds — plus unipotence and Q̂ = I at the deepest
point (the Lean `weightedCofactor_unitLower` / `weightedCofactor_eq_one`).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

z, v, ep = sp.symbols('z v ep')          # ep = e'
# certificate §4: the left det-0 row op Q₁ and its inverse
Q1     = sp.Matrix([[1, 0], [-z, 1]])
Q1inv  = Q1.inv()                        # [[1,0],[z,1]]
check("Q₁⁻¹ = [[1,0],[z,1]]", sp.simplify(Q1inv - sp.Matrix([[1, 0], [z, 1]])) == sp.zeros(2, 2))

# child dominant b' = (v, v·e'); divisibility chain b'_1 | b'_2 (b'_2 = e'·b'_1)
bp = [v, v * ep]
diagbp = sp.diag(*bp)

# THE CERTIFICATE'S Q̂ (conjugation)
Qhat_conj = sp.simplify(diagbp * Q1inv * diagbp.inv())
check("Q̂_conj = diag(b')·Q₁⁻¹·diag(b')⁻¹ = [[1,0],[e'z,1]]  (printed §4)",
      sp.simplify(Qhat_conj - sp.Matrix([[1, 0], [ep * z, 1]])) == sp.zeros(2, 2))

# THE LEAN Q̂ (entrywise, from the ratio c): c a d = b'_a / b'_d on supp(Q₁⁻¹); diag entries = 1.
#   supp(Q₁⁻¹) off-diagonal = (2,1) only ⟹ the only nontrivial ratio is c_21 = b'_2/b'_1 = e'.
def ratio(a, d):
    return sp.Integer(1) if a == d else sp.cancel(bp[a] / bp[d])
Qhat_lean = sp.Matrix(2, 2, lambda a, d: ratio(a, d) * Q1inv[a, d])   # Lean weightedCofactor
check("Lean weightedCofactor Q̂ (entrywise c·R) == certificate conjugation Q̂",
      sp.simplify(Qhat_lean - Qhat_conj) == sp.zeros(2, 2))
check("ratio c_21 = b'_2/b'_1 = e'  (the divisibility ratio; EXACT, polynomial)",
      sp.simplify(ratio(1, 0) - ep) == 0)

# THE LEAN COMMUTATION LEMMA: diag(b')·Q₁⁻¹ = Q̂·diag(b')  (inverse-free)
check("commutation  diag(b')·Q₁⁻¹ = Q̂·diag(b')  (diagonal_mul_eq_weightedCofactor_mul_diagonal)",
      sp.simplify(diagbp * Q1inv - Qhat_lean * diagbp) == sp.zeros(2, 2))

# unipotence (unit lower): diagonal 1, strictly-upper 0
check("Q̂ unit-lower: Q̂_11=Q̂_22=1, Q̂_12=0  (weightedCofactor_unitLower)",
      Qhat_lean[0, 0] == 1 and Qhat_lean[1, 1] == 1 and Qhat_lean[0, 1] == 0)

# Q̂ = I at the deepest point: all exceptional coords → 0 (z=0 ⟹ Q₁⁻¹=I; ratios' R-support entry z→0)
Qhat_at0 = Qhat_lean.subs({z: 0})
check("Q̂ = I at the deepest point (z=0)  (weightedCofactor_eq_one)",
      sp.simplify(Qhat_at0 - sp.eye(2)) == sp.zeros(2, 2))

# transport tie: diag(b')·Hpre = Q̂·(diag(b')·Hnext) when Hpre = Q₁⁻¹·Hnext  (weightedCofactor_transport)
Hnext = sp.Matrix([[sp.Symbol('h1')], [sp.Symbol('h2')]])
Hpre = Q1inv * Hnext
check("transport  diag(b')·Hpre = Q̂·(diag(b')·Hnext)  when Hpre=Q₁⁻¹·Hnext (weightedCofactor_transport)",
      sp.simplify(diagbp * Hpre - Qhat_lean * (diagbp * Hnext)) == sp.zeros(2, 1))

print(f"\nL4-core Q̂ certificate-tie: {'PASS' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
