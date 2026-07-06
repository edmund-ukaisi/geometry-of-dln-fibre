<task>
I am formalising, in Lean 4 + Mathlib (v4.29), the "integrability threshold" underlying the
real log-canonical threshold (RLCT) of a nonnegative loss germ. This is the CITE-FREE analytic
substrate — NOT the zeta-pole (λ,m) definition (that is deferred, needs cited meromorphic
continuation). I must pick the Lean definition of the threshold value and validate it on a witness.

Setup: K : (Fin n → ℝ) → ℝ, K ≥ 0, a base point x₀, K(x₀) = 0. Classically the RLCT threshold
is sup { c ≥ 0 : ∫_{U} K(x)^{-c} dx < ∞ for some neighbourhood U of x₀ } — the exponent at which
the local integral of K^{-c} transitions finite→infinite.

The Lean landmine: over ℝ, `Real.rpow` collapses the pole — `(0:ℝ)^(-c) = 0` for c ≠ 0
(`Real.zero_rpow`). So `K(x)^{-c}` as an ℝ-valued function is 0 exactly on the zero-set {K=0},
which is measure-zero for a non-degenerate germ. Question is whether `IntegrableOn (fun x ↦ (K x)^(-c)) U`
(ℝ-valued Bochner integrability) still faithfully captures the blow-up on the positive part {K>0},
OR whether I must use the ℝ≥0∞ lower integral `∫⁻ x in U, ENNReal.ofReal ((K x)^(-c))` where
`(0:ℝ≥0∞)^(neg) = ⊤` genuinely.

Candidate definitions of the admissible set A(K,x₀,U) ⊆ {c : ℝ | 0 ≤ c}:
  (A) c ∈ A  ⟺  IntegrableOn (fun x ↦ (K x) ^ (-c)) U volume        [ℝ Bochner]
  (B) c ∈ A  ⟺  ∫⁻ x in U, ENNReal.ofReal ((K x) ^ (-c)) ∂volume < ⊤ [ℝ≥0∞ lintegral]
Then threshold := sSup A (over a FIXED small U, or ⋃ over shrinking U — a design sub-choice).

Witness to validate: n = 1, K(t) = |t|, x₀ = 0, U = Ioo 0 t or Ioo (-t) t (t>0).
Expect threshold = 1, because ∫₀ x^{-c} converges iff c < 1 (`integrableOn_Ioo_rpow_iff` in Mathlib:
IntegrableOn (fun x ↦ x^s) (Ioo 0 t) ↔ -1 < s; here s = -c, so integrable iff c < 1).
So A = {c ≥ 0 : c < 1} = [0,1), sSup = 1. Good.

Concerns to adjudicate:
1. Do (A) and (B) define the SAME admissible set for germs with a measure-zero zero-set? I believe
   yes: |‖(K x)^(-c)‖| = (K x)^(-c) a.e. (they differ only on {K=0}, null), and Bochner-integrability
   of a nonneg function ⟺ finite lintegral of its ‖·‖. So (A) ⟺ (B) here. Is that right, and is (A)
   therefore an honest formulation of the threshold (not a formulation that silently ignores the pole)?
2. sSup over ℝ of a possibly-unbounded or empty set: A always contains 0 (K^0 = 1, integrable on
   bounded U), so A nonempty. A could be unbounded above (e.g. K ≡ 1 near x₀, no pole → every c
   admissible → threshold = ⊤, not representable in ℝ). Should the value live in ℝ≥0∞ to hold that
   case honestly, or is capping/junk-at-⊤ in ℝ acceptable for a "germ that vanishes at x₀" scope?
   Which is the more standard / more bedrock choice?
3. Fixed U vs ⋃ shrinking U (germ-genuine): the honest RLCT is a germ invariant (independent of U
   once U small). For the CITE-FREE substrate, is it cleaner to (i) fix U as a parameter and prove
   U-independence later, or (ii) define via a neighbourhood filter (∃ U ∈ 𝓝 x₀, IntegrableOn … U)?
   Option (ii) makes "admissible" = "IntegrableAtFilter (K^(-c)) (𝓝 x₀)" — Mathlib has
   `IntegrableAtFilter`. Does that give the cleaner germ-invariant object?

Downstream use: the value must (later, cited) equal ½·codim for the DLN square-Frobenius loss, and
must satisfy monotonicity (K ≤ K' pointwise near x₀ ⟹ thresholds ordered) and coord-change invariance
under diffeomorphism (via Mathlib `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`).
</task>

<output_contract>
1. RECOMMENDED DEFINITION: pick (A)/(B) × {fixed U | filter 𝓝 x₀ | ℝ≥0∞ value}, one sentence why.
2. Is claim (1) — (A)⟺(B) for null zero-set — correct? State the precise Mathlib-shaped justification
   or the counterexample.
3. The sSup-in-ℝ vs value-in-ℝ≥0∞ call for the no-pole (threshold=∞) case: which, and why is it bedrock.
4. Fixed-U vs IntegrableAtFilter (𝓝 x₀): which is the cleaner germ-invariant substrate, and does the
   witness (K=|t|) still give exactly 1 under it.
5. Any TRAP in the witness computation (the |x|=x-on-Ioo-0-t step, the sSup [0,1) = 1 step) I should
   pre-stage.
Be concise; rank concerns, flag inference vs. fact.
</output_contract>

<grounding_rules>
Flag any Mathlib lemma name you assert as "believed, verify" unless you are certain it exists at v4.29.
Distinguish mathematical fact from Lean-formalisation-convenience inference.
</grounding_rules>
