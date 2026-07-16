"""
couplerad_deeplog.py -- the EXACT deep-cell charge-weight for b=1, a=1 (the b=1 dispatch witnesses).

Pins the per-stratum σ-measure/charge accounting at δ=0 for schurrec's ChargedRectSchurCore deep locus.
corneradj (decorrelated) found the charge weight is LOGARITHMIC (Ch(S) ~ ln(1/σ)), NOT a power -- this
CORRECTS my earlier power-preview. Verified here exactly (sympy).

Setup (b=1, a=1): near the rank-drop, S has one order-1 singular value σ₁~1 and the next σ₂=σ→0.
A_cor ∈ ℝ^{1×M₂}; x = A_cor·u₁ (large-dir coord), y = A_cor·u₂ (small-dir coord).
  charge weight  W(S) = ∫_{A_cor box} ‖A_cor·S‖^{−1} dA_cor  ~  ∫∫_{[−1,1]²} (x² + σ²y²)^{−1/2} dx dy.
The S-measure carries σ^{c−1}dσ, c = codim of the rank-drop ≥ 1.
"""
import sympy as sp

x, y, sig, d = sp.symbols('x y sigma delta', positive=True)

print("="*88)
print("b=1,a=1 deep-cell charge weight W(S) ~ ∫∫ (x²+σ²y²)^{−1/2} dx dy  (near rank-drop, σ=small SV)")
print("="*88)

# inner x-integral over [0,1] (double for [-1,1]); exact:
Ix = sp.integrate((x**2 + sig**2*y**2)**sp.Rational(-1, 2), (x, 0, 1))
print("  ∫_0^1 (x²+σ²y²)^{−1/2} dx =", sp.simplify(Ix), "  = arcsinh(1/(σy))")
# small-σ asymptotic of arcsinh(1/(σy)) = ln(2/(σy)) + O((σy)²):
print("  arcsinh(1/(σy)) → ln(2/(σy))  as σy→0   [LOGARITHMIC in σ]")
# outer y-integral of ln(1/(σy)) over [0,1]:
Iy = sp.integrate(sp.log(1/(sig*y)), (y, 0, 1))
print("  ∫_0^1 ln(1/(σy)) dy =", sp.simplify(Iy), "  ⟹  W(S) ~ ln(1/σ) + const   [confirms corneradj: LOG, not power]")

print()
print("The S-measure (codim c≥1) PAYS the log — exact:")
for cval in [1, 2, 3]:
    val = sp.integrate((1 + sp.log(1/sig)) * sig**(cval-1), (sig, 0, d))
    print(f"  ∫_0^δ (1+ln(1/σ))·σ^({cval}−1) dσ = {sp.simplify(val)}   (FINITE)")

print()
print("Crude-power consequence (Lean-friendlier, avoids arcsinh): ln(1/σ) ≤ C_ε·σ^{−ε} for σ∈(0,1), any ε>0.")
print("So W(S) ≤ C_ε σ^{−ε}, and ∫_0^δ σ^{−ε}·σ^{c−1} dσ < ∞ for ε < c (c≥1 ⟹ pick ε∈(0,1)):")
eps = sp.symbols('epsilon', positive=True)
val = sp.integrate(sig**(-eps) * sig**(1-1), (sig, 0, d))   # c=1
print("  ∫_0^δ σ^{−ε}·σ^{1−1} dσ =", sp.simplify(val), " (finite for ε<1)")

print()
print("VERDICT (b=1,a=1): W(S) LOG-bounded; S-measure (codim≥1) integrates it; δ=0 (log is sub-power, no")
print("codim shift); γ=0. Lean: either explicit arcsinh→log, or crude W≤C_ε σ^{−ε} (ε<1) + measure σ^{c−1}.")
print()
print("⚠ SCOPE: the LOG is a=1-specific. For a≥2 (b=1) the inner integral is a POWER (σ^{−(a−1)}) and the")
print("y-integral ∫y^{−(a−1)}dy needs a>=2 handled by the deeper (b≥2-style) measure — a DIFFERENT (power) case.")
print("All 3 b=1 dispatch witnesses have a=1, so the LOG form is exactly what they need.")
