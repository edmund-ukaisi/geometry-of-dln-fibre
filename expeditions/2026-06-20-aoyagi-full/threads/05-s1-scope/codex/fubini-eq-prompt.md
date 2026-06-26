<task>
Decorrelated soundness check of the two subtlest pieces of a Lean RLCT lemma (the smooth-block Fubini
shift `rlctAt(Σxᵢ² + G²) = n/2 + λ(G²)`, n=1 step + iteration). Confirm or refute the analytic logic.
RLCT λ(F) at a point = sSup{ c ≥ 0 : |F|^{-c} locally integrable near the point }.

PIECE 1 — the ≤ direction (non-integrability / cusp), n=1. Goal: rlctAt(x²+H) ≤ 1/2 + λ(H) (x∈ℝ, H≥0 a
measurable core, H≠0 a.e.). Mechanism (contrapositive `step_lintegral_top` → `core_int_of_joint_int`):
  - For c > 1/2: IF the joint |x²+H|^{-c} is integrable on Icc(-R,R)×V, THEN |H|^{-(c-1/2)} integrable on V.
  - Proof of the contrapositive: cusp lower bound — on {x² ≤ H z}, x²+H ≤ 2H, so (exponent -c < 0, antitone)
    (2H)^{-c} ≤ (x²+H)^{-c}. Restrict the joint integrand below by [x²≤H]·(2H)^{-c}·wt. Tonelli (y-outer):
    the inner x-slice ∫_{Icc(-R,R)} [x²≤H z](2H)^{-c} dx = (2H z)^{-c}·(2√(H z))  [the 1-D cusp volume
    vol{x:x²≤s}=2√s], which equals 2^{1-c}·(H z)^{1/2-c}·wt z. So the y-integral = ∫_V 2^{1-c}(H z)^{1/2-c}wt z.
    If |H|^{-(c-1/2)} is NOT integrable on V, this = ⊤ (note 1/2-c = -(c-1/2)), forcing the joint = ⊤,
    contradicting joint-integrable.
QUESTION 1: Is this cusp mechanism SOUND? Specifically: (a) is the lower bound (2H)^{-c} ≤ (x²+H)^{-c} on
the cusp in the right direction (lower-bounding the joint so its divergence forces divergence)? (b) does the
inner slice (2H)^{-c}·2√H = 2^{1-c}·H^{1/2-c} correctly produce the SHIFTED exponent c-1/2 in the core
integral? (c) is "core diverges at exponent c-1/2 ⟹ joint diverges" the correct contrapositive for ≤?

PIECE 2 — the iteration n=1 → general n. `rlct_additive_smooth_block_aux` inducts on n: peel one
coordinate via a MEASURE-PRESERVING homeomorphism `chartN : (Fin(m+1)→ℝ)×Y ≃ₜ ℝ×((Fin m→ℝ)×Y)` (forward
x↦(x₀, x∘succ); inverse Fin.cons), rewrite Σ_{i<m+1} xᵢ² = x₀² + Σ_{i<m} xᵢ², apply the n=1 step
`rlct(x₀² + [Σ_{<m}+G²]) = 1/2 + rlct(Σ_{<m}+G²)`, then the induction hypothesis `rlct(Σ_{<m}+G²) = m/2 +
rlct(G²)`. The MP-homeomorph invariance `rlctAtOn(F∘e) = rlctAtOn F (e w)` transports the threshold.
QUESTION 2: Is the iteration SOUND? (a) Does RLCT-invariance under a measure-preserving homeomorphism hold
(rlctAtOn(F∘e w0) = rlctAtOn F (e w0))? (b) Does peeling preserve the intermediate core's a.e.-nonvanishing
(Σ_{<m}xᵢ²+G² ≥ G² > 0 a.e., so the n=1 step's H≠0-a.e. hypothesis is met at each step)? (c) any subtlety
in the base case n=0 (empty regular block, (Fin 0→ℝ)×Y ≃ Y)?
</task>

<output_contract>
Two numbered verdicts (one per PIECE), each with sub-points (a)(b)(c): SOUND/FLAG + one-line reason.
Flag any sign error, wrong-direction inequality, or missing hypothesis. Distinguish fact from inference.
</output_contract>

<grounding_rules>
The cusp volume vol{x:x²≤s}=2√s, rpow antitonicity for negative exponents, and MP-invariance of locally-
integrable thresholds are standard; use them. Flag inferences. Don't invent Mathlib lemma names.
</grounding_rules>
