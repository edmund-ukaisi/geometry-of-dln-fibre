<task>
Adversarially stress-test whether a coupled-corner RLCT estimate SECRETLY COLLAPSES to a lower threshold —
the "technically-correct-but-subtly-wrong" trap. Reason in exact algebra. Self-contained.

SETUP. A decorated (S,J) descent for deep-linear-network loss finiteness peels a front block and resolves a
COUPLED CORNER by a blow-up. On the intersection / deficient-rank locus the resolved loss is
    G = u₀²·(U₀ + τ²·U₁),     measure  |u₀|^{p₀}·|u₁|^{p₁} du₀ du₁,  u₁ = u₀·τ,
where u₀ is the front Γ-block exceptional radial, u₁ a coupled deeper radial (τ = u₁/u₀ the angular),
p₀,p₁ the block-dimension Jacobian powers, and U₀,U₁ are "unit" factors built from the DEEPER matrix A₂'s
Gram (A₂ is the deeper product matrix). The CLAIM to test: the corner RLCT is
    ½·Σ(p_i+1) = ½·minAdm   (charges ADD across the two coupled divisors),
PROVIDED U₀,U₁ > 0 stay BOUNDED BELOW on the chart. The FEAR: the DLN sum-form `u₀²(U₀+τ²U₁)` secretly
collapses to the product caricature `z²(x²+y²)` (whose RLCT is a strictly SMALLER `min`, not the coupled
sum), giving a threshold BELOW ½minAdm — i.e. (□) would be false / the descent unsound.

ESTABLISHED (take as given): the intersection tube is finite for c' < ½minAdm via a JOINT two-scale
pushforward density `μ{s₂≤t₂,s₃≤t₃} ≍ t₂³·t₃·log(e/t₂)` (`∫ s₂⁻³s₃⁻η dμ < ∞ ⟺ η=2c'−6 < 1 ⟺ c'<7/2` for the
anchor (3,3,3,4)); the MARGINALS give only `η<1/4` (insufficient). So the coupled/joint estimate is what
reaches ½minAdm; a per-divisor or marginal estimate undershoots.

ADVERSARIAL QUESTIONS:
 Q1. Does `u₀²(U₀+τ²U₁)` with `U₀,U₁ > 0` bounded below actually have corner RLCT `½Σ(p_i+1)` (charges ADD),
     or does it collapse like `z²(x²+y²)`? Pin the EXACT difference between the coupled SUM-form and the
     product caricature — where does the "collapse" come from in the caricature, and is the SUM-form immune
     iff `U₀+τ²U₁` is a UNIT (bounded below, non-vanishing on the τ-box)?
 Q2. ★ Is `U₀ > 0 bounded below` genuinely SECURED, or is there a subtle sub-locus of the chart where
     `U₀ → 0` CORRELATED with the blow-up (so the "unit" is not uniformly bounded below and a hidden
     collapse occurs)? Consider: `U₀` is a Gram/minor of the deeper `A₂`; on the GENERIC-`A₂` chart (A₂ full
     rank) `U₀ ≠ 0` pointwise, but is it bounded below UNIFORMLY, or does approaching the A₂-rank-drop
     boundary drive `U₀→0` on the chart? Does securing it require a QUANTITATIVE sector `{σ_min(A₂) ≥ ε}`
     (excising the A₂-rank-drop), or is pointwise-nonzero enough?
 Q3. If a quantitative sector is needed, does splitting off `{σ_min(A₂) < ε}` (the A₂-rank-drop) to a
     recursive branch actually recover a threshold `≥ ½minAdm` there, or could the deeper branch carry a
     LOWER RLCT (the `x²(x²+y^{2N})`-type trap: higher codim, lower threshold)? What must the split establish?
</task>

<output_contract>
Answer Q1, Q2, Q3. For each: verdict (SOUND / COLLAPSES / NEEDS-SECTOR / GAP) + the exact-algebra reason.
Mark [DERIVED]/[INFERRED]. On Q1 give the explicit RLCT of both `u₀²(U₀+τ²U₁)` (U₀,U₁ units) AND `z²(x²+y²)`
to pin the difference. End with: is there a genuine COLLAPSE obstruction, or is the coupled estimate sound
given a securable (quantitative-sector) units bound? The single cheapest check that would expose a collapse.
</output_contract>

<grounding_rules>
Try to BREAK the ½minAdm claim by finding a collapse. Distinguish "pointwise U₀≠0" (weak) from "U₀ bounded
below uniformly on the chart" (what the estimate needs). Distinguish a genuine collapse obstruction (RLCT
truly < ½minAdm) from a securable sector requirement. Reason in exact algebra; do not paste code.
</grounding_rules>
