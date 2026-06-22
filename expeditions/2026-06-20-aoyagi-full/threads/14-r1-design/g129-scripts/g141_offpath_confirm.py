import sympy as sp
# CONFIRM decision C: the squeeze is OFF-PATH because it drops the x_p² exceptional weight.
# Node: blow up the rank-defect via pivotBlowupOn → core∘φ = x_p²·Q. The RLCT of x_p²·Q via the MONOMIAL
# route accounts the x_p² as an exceptional divisor (k=1, h=card-1, ratio (h+1)/2 = card/2). The SQUEEZE
# route would compare core to Φ and strip x_p² as a 'unit' — but x_p² VANISHES at x_p=0 (it is NOT a unit!),
# so stripping it is illegitimate and DROPS the weight. Confirm x_p² is not a unit (vanishes on the divisor).
xp, q = sp.symbols('x_p q', real=True)
core_pulled = xp**2 * q   # core ∘ pivotBlowupOn (q = the residual Q, a unit≥1 after full resolution)
print("core∘φ = x_p²·Q. Is x_p² a unit near x_p=0?  x_p²|_{x_p=0} =", core_pulled.subs(xp,0), " (=0 ⟹ NOT a unit)")
print("""
⟹ x_p² CANNOT be stripped as a squeeze-unit (a unit must be bounded away from 0). The squeeze
c₁Φ≤F≤c₂Φ + rlctAt_mono strips only genuine UNITS (the c₁,c₂ constants); applying it here to remove
x_p² is illegitimate. The MONOMIAL route correctly KEEPS x_p² as the exceptional divisor:
  rlctAtOn(x_p²·Q) via monomialThreshold: x_p² ⟹ (k,h)=(1, card-1) [Jacobian u^{card-1}], ratio card/2.
If instead one (wrongly) squeezed x_p² away, the recursion would be measure-preserving (det-1 only) and
conserve dimension ⟹ telescope to ambient/2 = 4 for (2,2,2), NOT 3/2. That is the g32 dimension-
conservation death. CONFIRMED off-path.
""")
print("=== The CORRECT C1 mechanism (monomial) ===")
print("""
 (1) pivotBlowupOn(active, p): core∘φ = x_p²·Q, Jacobian |x_p|^{card-1}. The x_p² is the EXCEPTIONAL
     DIVISOR — (k,h)=(1, card-1), ratio via axisRatio_regularSeq = card/2, ACCOUNTED by monomialThreshold.
 (2) EXACT det-unit measure-preserving regular-change (generalizing lemma2Fwd): an EXACT change of
     variables (det ±1, lintegral-level splice, NO Jacobian, NO two-sided bound) straightening Q's
     bilinear rank-defect center to a coordinate subspace, so the next pivotBlowupOn can fire.
 (3) recurse on the resolved residual Q (ΣM drops).
The det-unit regular-change is EXACT (lemma2Fwd is a concrete det-±1 polynomial map, measurePreserving_lemma2
PROVEN) — NOT the squeeze (a two-sided inequality). The squeeze parked off-path.
""")
