import sympy as sp
# Map the 5 contract fields onto the (2,2,2) Lean anchor, and find the missing-field flag for general M.
#
# (2,2,2) anchor (from the Lean):
#   lemma2Fwd: (t1,t2,t3,b00,b01,b10,b11) -> (t1,E,F0,δ,q,G,H), E=b00+t1 b10, F0=b01+t1 b11,
#              δ=t3−t1 t2, q=t2, G=b10, H=b11. det=−1, measure-preserving.
#   step1Residual = (b00+t1 b10)²+(b01+t1 b11)²+(t2 b00+t3 b10)²+(t2 b01+t3 b11)²  [= ‖Â B‖², the core]
#   resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)²   [the normal form, vertex {E=F0=δ=0}]
#   step1Residual v = resolvedForm(lemma2Fwd v)   [strict-transform eq, FIELD 5]
#   step2E/step2D/pivotBlowupOn {1,2,3}: blow up slots {E,F0,δ}={1,2,3}  [FIELD 3 center]
#
# FIELD-BY-FIELD:
print("=== Mapping the 5 fields onto the (2,2,2) anchor ===")
print("Field 1 TYPE (resolvedForm: chart domain -> straightened coords):")
print("  (2,2,2): lemma2Fwd : (Fin 7 → ℝ) → (Fin 7 → ℝ). ✓ EXHIBITED (the straightening map).")
print()
print("Field 2 MEASURE-PRESERVING / det-1:")
print("  (2,2,2): measurePreserving_lemma2 (det=−1, unit Jac, no exponent shift). ✓ EXHIBITED.")
print()
print("Field 3 COORDINATE-CENTER ID ({r−pq=0}→{w=0}, explicit pivot set):")
print("  (2,2,2): the δ-coord δ=t3−t1 t2 (= the bilinear {r−pq=0} straightened to {δ=0}); the center")
print("  is {E=F0=δ=0}=slots{1,2,3}, and pivotBlowupOn {1,2,3} consumes EXACTLY that index set. ✓ EXHIBITED")
print("  with explicit pivot set {1,2,3}. (This is the #121 bilinear-center straightening, in Lean.)")
print()
print("Field 5 STRICT-TRANSFORM EQ (core x = core'(resolvedForm x)):")
print("  (2,2,2): step1Residual v = resolvedForm(lemma2Fwd v). ✓ EXHIBITED (ring-proven).")
print()
print("Field 4 REDUCED-CHAIN MAP (exposes reduced M' + residual core'):")
print("  (2,2,2): resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)² is the NORMAL QUADRATIC FORM, NOT exposed")
print("  as a smaller ‖prod(C')‖² chain product. The (2,2,2) anchor goes STRAIGHT to the resolved")
print("  quadratic — it does NOT exhibit a reduced-chain map. !!! POTENTIAL MISSING FIELD at general M !!!")
