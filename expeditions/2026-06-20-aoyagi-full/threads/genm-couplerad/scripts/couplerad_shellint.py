"""
couplerad_shellint.py -- design (ii): the coupled §w3 SHELL-INTEGRATION for the interior free-box bound
  ∫∫_box det((Acor·S)(Acor·S)ᵀ)^{−a/2} dAcor dS < ⊤   for a+b ≤ ρ  (ρ = deepTailMin = rank S generic).

Decompose S by σ_ρ(S) (smallest singular value) into shells {σ_ρ ∈ [ε,2ε)}. Per shell, a charge bound
C(ε); shell S-measure ~ ε^{c−1}dε with c = codim{rank S ≤ ρ−1} = (M₂−ρ+1)(n−ρ+1) ≥ 1. Converge iff
∫_0 C(ε)·ε^{c−1}dε < ⊤.

KEY FINDING: schurB's UNIFORM-δ atom (chargedWishartWeight_lt_top, isotropic floor SSᵀ⪰δ²I) gives the CRUDE
C(ε) ~ ε^{−ab} (from charge ≥ (δ²)^b det(Acor Acorᵀ)), which DIVERGES at c ≤ ab. The TIGHT (graded-floor:
top ρ−1 order-1, σ_ρ~ε) bound gives C(ε) ~ log(1/ε) [b=1,a=1, exact-verified couplerad_deeplog], FINITE
for c≥1. c ≤ ab for EVERY dispatch witness => the shell-integration needs the TIGHT bound, not the crude atom.
"""
import sympy as sp
eps, d = sp.symbols('epsilon delta', positive=True)

def codim(M2, n, rho): return (M2 - rho + 1) * (n - rho + 1)

print("interior free-box shell-integration: ∫_0 C(ε)·ε^{c-1} dε,  c = (M₂−ρ+1)(n−ρ+1)")
print("="*94)
witnesses = [("(4,4,4,4)→(3,4,4)", 4, 4, 1, 1), ("(5,5,5,5)→(4,5,5)", 5, 5, 1, 1),
             ("(3,3,4,4)→(2,4,4)", 4, 4, 1, 1), ("(3,4,5,4)→(2,5,4)", 5, 4, 1, 2)]
for name, M2, n, a, b in witnesses:
    rho = min(M2, n); c = codim(M2, n, rho); ab = a * b
    crude_ok = (c > ab)
    tight = sp.integrate((1 + sp.log(1/eps)) * eps**(c-1), (eps, 0, d))
    print(f"  {name}: M₂={M2} n={n} ρ={rho} (a,b)=({a},{b}) c={c} ab={ab}")
    print(f"     CRUDE (schurB uniform, C~ε^-ab): ∫ε^({-ab}+{c}-1) {'FINITE' if crude_ok else 'DIVERGES'} (needs c>ab)")
    print(f"     TIGHT (graded/log, C~log 1/ε):   ∫log(1/ε)ε^({c}-1) = {sp.simplify(tight)}  FINITE")

print()
print("VERDICT: c ≤ ab for ALL dispatch witnesses (c=1=ab square; c=2=ab for (3,4,5,4)) => schurB's")
print("uniform-δ atom's ε^{-ab} DIVERGES in the shell-integration. The interior needs the TIGHT per-shell")
print("bound (graded floor: top ρ−1 order-1 + σ_ρ~ε → log for b=1,a=1). schurB's uniform atom is the")
print("SHALLOW-BULK consumer (σ_ρ ≥ δ₀ fixed); the tight interior is the §w3-deep graded/log estimate.")
print()
print("MINIMAL GAP (flag): the tight per-shell bound. Route (a) schurB builds a GRADED-floor Wishart atom")
print("(SSᵀ ⪰ δ₀²·P_top(ρ−1) + ε²·P_last), exposing the log; or route (b) wire the §w3-deep log directly.")
print("Log-integrability ∫log(1/ε)ε^{c-1}dε<∞ (c≥1) is standard/sound — NO wall; the graded bound is the build.")
