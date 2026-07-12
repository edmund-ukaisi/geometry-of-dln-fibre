<task>
Adjudicate a base-integral finiteness architecture for a decorated (S,J) resolution — 3 confirmation points.
Adversarial: try to BREAK each. Reason in exact algebra. Self-contained. (This has flip-flopped twice; a
decorrelated confirmation is needed before committing — do NOT rubber-stamp.)

SETUP. A width-2 decorated base must show ∫ (∏|u_ℓ|^{jac_ℓ})·decLoss(u,z)^{−c'} < ⊤ for c' < ½·minAdm, where
decLoss = Σ_i (∏_ℓ|u_ℓ|^{supp i ℓ}·res_i(z))², commonDivisor(u)=∏|u_ℓ|^{k_ℓ}, k_ℓ=⨅_i supp i ℓ. A
"dehomogenised generator" i₀ has supp i₀ ℓ = k_ℓ ∀ℓ (its monomial = commonDivisor). The residuals come from a
front peel: the corank block Γ = A_cor (b×M₂, a FREE integration variable) times the deeper product Z=Zdeep
(M₂×M_L); the surviving corank generator's residual is res_{i₀} = H₁ = |q₁ + s·q₂| where q₁,q₂ are rows of
Γ·Z and s is a bounded angular chart coordinate. A "units sector" σ_min(A₂) ≥ ε bounds the DEEPER Z below
(Z·Zᵀ ≽ ε²·I), but A_cor=Γ is FREE (unconstrained, integrated).

TWO candidate base derivations / γ-clauses:
 (i₀-COMPONENT): decLoss ≥ commonDivisor(u)²·res_{i₀}(z)² (the i₀ term); needs res_{i₀} = H₁ ≥ c > 0 (a
   pointwise-coercive COMPONENT). 
 (ROUTE-A, "corankLeaf"): decLoss ≍ commonDivisor(u)²·frobSq(Γ·Z); use Rayleigh frobSq(Γ·Z) ≥ λ_min(Z·Zᵀ)·
   frobSq(Γ) ≥ ε²·frobSq(Γ), then integrate Γ as a FREE BLOCK: ∫(∏|u|^{jac})·commonDivisor^{−2c'}·
   frobSq(Γ)^{−c'} = (u-monomial integral)·(∫frobSq(Γ)^{−c'}dΓ). γ-clause = the Z-UNITS-BOUND Z·Zᵀ ≽ c·I
   (block/eigenvalue level), NOT a component.

CONFIRM (adversarially):
 Q1. Is res_{i₀} = H₁ = min-over-s |q₁+s q₂| = σ_min([q₁;q₂]) = σ_min(Γ·Z), and is this UNBOUNDED below under
     σ_min(A₂) ≥ ε alone (because Γ=A_cor is free and can be near-rank-deficient, so σ_min(ΓZ)→0 even with
     σ_min(Z)≥ε)? I.e. is the i₀-COMPONENT γ (res_{i₀} ≥ c) UNSATISFIABLE by peel-outputs on the units sector
     (too strong)? Or is there a reason res_{i₀} is bounded below that I'm missing?
 Q2. Does ROUTE-A close the base at ½minAdm: given decLoss ≍ commonDivisor²·frobSq(ΓZ) and Z·Zᵀ≽ε²I, does
     ∫(∏|u|^{jac})·decLoss^{−c'} < ⊤ for c' < ½minAdm — via Rayleigh (frobSq(ΓZ)≥ε²·frobSq(Γ)) + the SEPARABLE
     product (u-monomial integral finite for c'<monomialThreshold, × free-block ∫frobSq(Γ)^{−c'}dΓ finite for
     c'<½·(dim Γ))? Do the charges combine to ½minAdm (u-charge + Γ-block-charge = minAdm), or does the
     separable product give only a MIN (undershoot)? [The concern: separable ⟹ min(u-threshold, Γ-threshold),
     which must each be ≥ ½minAdm OR the charges genuinely ADD.]
 Q3. Is the ROUTE-A γ (Z·Zᵀ ≽ c·I, block/eigenvalue-level) PRESERVED by the peel's units sector σ_min(A₂)≥ε
     (a faithful peel keeps the deeper product nondegenerate), UNLIKE the i₀-component (which the free Γ
     breaks)? I.e. is the block-level Z-units-bound the right, preservable γ?
</task>

<output_contract>
Q1,Q2,Q3: verdict (CONFIRM / REFUTE / GAP) + exact reason, [DERIVED]/[INFERRED]. On Q2 be explicit about
ADD-vs-MIN: does route-A's separable product actually reach ½minAdm, or is there a charge-combination subtlety
(e.g. the u-monomial must carry minAdm − ½dim(Γ), or the Γ-block dim must itself be ½minAdm)? End: is the
reconciliation (drop i₀-component γ; use route-A corankLeaf + block-level Z-units-bound γ) SOUND, and any
residual gap before it's committed.
</output_contract>

<grounding_rules>
Adversarial — this reconciliation reverses a prior decision, so try to break it. Distinguish an UNSATISFIABLE
clause (too strong, peel can't produce it) from an unpreservable one. On Q2, the ADD-vs-MIN of the separable
product is the crux — check whether route-A's free-block-Γ actually gives ½minAdm or undershoots. Do not paste
code.
</grounding_rules>
