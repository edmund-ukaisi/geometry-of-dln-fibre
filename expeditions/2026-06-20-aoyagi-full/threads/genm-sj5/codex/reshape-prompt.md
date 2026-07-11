<task>
Lean 4 + Mathlib (v4.29) measure-theory reshape. I need the cleanest construction of a
measure-preserving `MeasurableEquiv` (and its measure-preservation proof + norm identities) to
discharge ONE `sorry` (a `≤` between two lintegrals). This is a design/API-path question: I have all
the building blocks, I want the composition order that minimizes plumbing and avoids v4.29 snags.

## The goal (the sorry)

Fixed naturals `m r : ℕ`, `0 < m`, `0 < r`. Real scalars `κ c' σ : ℝ` (`σ = sigMin P ≥ 0`, `κ > 0`,
`c' > 0`). `U : Matrix (Fin r) (Fin r) ℝ` orthogonal (`U * Uᵀ = 1`), `c : Fin r` a fixed column index.

Define (over the RAW pi type `A₀ : Fin m → Fin r → ℝ`, `Matrix.of A₀` its matrix view):
  Vc(A₀) = ∑ i, ((A₀ · U) i c)^2               -- squared L2 norm of column `c` of A₀·U
  Ur(A₀) = ∑ j ∈ Finset.univ.erase c, ∑ i, ((A₀ · U) i j)^2   -- squared norm of the OTHER columns
  twoBlockLoss(A₀) = σ^2 * Vc(A₀) + κ^2 * Ur(A₀)

Target inequality (integrand ≥ 0 everywhere, so monotone-in-domain is free):

  ∫⁻ A₀ in matBox m r 1, ENNReal.ofReal (twoBlockLoss(A₀) ^ (-c'))
    ≤ ∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin (m*(r-1)))) R
                 ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R),
        ENNReal.ofReal ((κ^2 * ‖p.1‖^2 + σ^2 * ‖p.2‖^2) ^ (-c'))

where `R = Real.sqrt (m*r)` and `matBox m r 1 = {A₀ | ∀ i k, A₀ i k ∈ Set.Icc (-1:ℝ) 1}`
(a set in `Fin m → Fin r → ℝ`, ambient measure = the nested-pi Lebesgue `volume`; measurable).

Note: `p.1 ∈ EuclideanSpace ℝ (Fin (m*(r-1)))` is the "u"-block (weight κ²), `p.2 ∈ EuclideanSpace ℝ (Fin m)`
is the "v"-block (weight σ², the collapsing column `c`).

## Strategy I have in mind (two stages) — critique / improve it

STAGE A (kill the orthogonal U, no equiv): Enclose matBox in the Frobenius ball
`FB R = {A₀ | frobSq A₀ < R^2}` (matBox ⊆ FB R since each entry ∈ [-1,1] ⇒ frobSq ≤ m*r = R², but
corners hit = R² exactly, so I likely need R slightly bigger OR closed-ball / a strict `<` argument).
Then use the banked full-space orthogonal CoV `lintegral_comp_orthRightMulₚ` with an INDICATOR trick:
apply it to `g(Γ) = (FB R).indicator (fun Γ => ofReal((σ²·Vc'(Γ)+κ²·Ur'(Γ))^(-c'))) Γ` where Vc',Ur'
read columns of Γ directly (no U). Since `frobSq (A₀·U) = frobSq A₀` (U orthogonal), the indicator is
U-invariant, giving `∫_{FB} (of the A₀·U integrand) = ∫_{FB} (of the Γ integrand)`. Net: reduces to
  ∫⁻ Γ in FB R, ofReal((σ²·(∑ i,(Γ i c)²) + κ²·(∑ j≠c ∑ i,(Γ i j)²))^(-c'))
i.e. columns read DIRECTLY, no U.

STAGE B (the column-split reshape): build a measure-preserving `MeasurableEquiv`
  e : (Fin m → Fin r → ℝ) ≃ᵐ (EuclideanSpace ℝ (Fin (m*(r-1))) × EuclideanSpace ℝ (Fin m))
with:
  - ‖(e Γ).1‖² = ∑ j≠c ∑ i, (Γ i j)²   (u-block = other columns, flattened)
  - ‖(e Γ).2‖² = ∑ i, (Γ i c)²         (v-block = column c)
Then: ∫_{FB} (integrand) = ∫_{FB} (H ∘ e)  where H(u,v) = ofReal((κ²‖u‖²+σ²‖v‖²)^(-c'));
      ≤ ∫_{e⁻¹'(ball_u R × ball_v R)} (H ∘ e)         [lintegral_mono_set; need FB R ⊆ e⁻¹'(...), i.e.
                                                        on FB, ‖(eΓ).1‖ ≤ frobSq^{1/2} < R and same for .2]
      = ∫_{ball_u R × ball_v R} H                      [MeasurePreserving.setLIntegral_comp_preimage_emb]

## Available Mathlib / codebase building blocks (CONFIRMED to exist, v4.29)

- `MeasurableEquiv.piEquivPiSubtypeProd (p) : (∀ i, β i) ≃ᵐ (∀ i:{x//p x}, β i) × (∀ i:{x//¬p x}, β i)`
  with `measurePreserving_piEquivPiSubtypeProd` / `volume_preserving_piEquivPiSubtypeProd`.
- `MeasurableEquiv.arrowProdEquivProdArrow α β γ : (γ → α × β) ≃ᵐ (γ → α) × (γ → β)` with
  `volume_measurePreserving_arrowProdEquivProdArrow`.
- `MeasurableEquiv.arrowCongr' (eα)(eβ)` with `volume_preserving_arrowCongr'`.
- `MeasurableEquiv.piCurry (X) : (∀ i j, X i j) ≃ᵐ (∀ ij:Σi, X ij.1 ij.2)`; `measurePreserving_piCurry`.
- `MeasurableEquiv.piCongrLeft` with `volume_preserving_piCongrLeft`.
- `MeasurableEquiv.toLp 2 X : X ≃ᵐ WithLp 2 X` (here X = `Fin k → ℝ`, WithLp 2 = EuclideanSpace),
  `PiLp.volume_preserving_toLp (Fin k)`.
- `finProdFinEquiv : Fin p × Fin q ≃ Fin (p*q)`; `Fintype.equivFinOfCardEq`.
- codebase `eMatFlat p q : (Fin p → Fin q → ℝ) ≃ᵐ (Fin (p*q) → ℝ)` (= piCurry.symm ∘ arrowCongr' sigFlat),
  measure-preserving `measurePreserving_eMatFlat`, `frobSq_eq_flatSum`, `eMatFlat_apply`.
- `EuclideanSpace.norm_sq_eq y = ∑ i, ‖y i‖²` ; `WithLp.ofLp_toLp`.
- `Fintype.card {j : Fin r // j ≠ c} = r - 1`.
- banked: `lintegral_comp_orthRightMulₚ (p) (Q) (hQ : Q*Qᵀ=1) g hg : ∫ Γ, g (fun i => Γ i ᵥ* Q) = ∫ Γ, g Γ`
  (full-space); `(A₀ * U) i = A₀ i ᵥ* U` (matrix mult = per-row vecMul).

## Key questions

1. Is STAGE A (indicator-in-`g` trick to get a BALL-restricted orthogonal CoV from the full-space
   `lintegral_comp_orthRightMulₚ`) sound and the cleanest way? Any pitfall with `Set.indicator` inside
   the `∫⁻` and matching the FB-membership `frobSq(A₀·U)=frobSq A₀`? Is there a slicker route (e.g. skip
   the ball and do the split at the matrix level BEFORE enlarging, so the orthogonal CoV never needs
   restriction)? Reconsider from scratch if the whole A/B split is not the cleanest.

2. For STAGE B, what is the cleanest composition of the listed equivs to build `e`, splitting the INNER
   (column) index `Fin r` at `c`? The obstruction: the split index is inner (rows are outer). Candidate:
   per-row split with `arrowCongr' (refl (Fin m)) (piEquivPiSubtypeProd (·=c))` then
   `arrowProdEquivProdArrow` to pull the product out, then flatten each block via `eMatFlat`/`toLp`.
   Give the EXACT `.trans` chain, the target types at each step, and which MP lemma discharges each.
   Watch the `{j//j=c}` (card 1) vs `{j//j≠c}` (card r-1) subtypes and the `(r-1)*m` vs `m*(r-1)` order.

3. The norm identities: after the chain, how to prove `‖(e Γ).1‖² = ∑ j≠c ∑ i,(Γ i j)²` and
   `‖(e Γ).2‖² = ∑ i,(Γ i c)²` with least pain (via `EuclideanSpace.norm_sq_eq` + reindex sums)?
   Any `Finset.sum` reindexing lemma (`Equiv.sum_comp`, `Fintype.sum_sigma`, `Finset.sum_subtype`) that
   makes the erase-c ↔ {j//j≠c} bridge clean?

4. Is there a materially SIMPLER overall route I'm missing (e.g. a single `LinearIsometryEquiv` whose
   measure-preservation Mathlib already gives, or reproving a bespoke two-block bound over the matrix
   box directly instead of consuming the product-ball `twoBlock_radial_le`)?
</task>

<output_contract>
1. VERDICT on the A/B strategy: sound / has-a-gap / there-is-a-better-route (one paragraph).
2. STAGE A: the cleanest concrete recipe (or the better alternative), with the exact indicator/CoV
   incantation and how to handle the matBox-corner `frobSq = R²` boundary (bump R, or closed ball, or
   `≤` via a null corner set). Name the exact lemmas.
3. STAGE B: the exact `MeasurableEquiv` `.trans` chain with types at each node and the MP lemma per
   node; then the norm-identity proof sketch. Flag any node where a needed MP lemma might NOT exist in
   v4.29 (so I can pre-empt).
4. The single biggest risk / most likely time-sink, and the cheapest way to de-risk it first.
Keep it tight and concrete — Lean identifiers, not prose. ~1 page.
</output_contract>

<grounding_rules>
Distinguish "I am confident this Mathlib lemma exists with this signature in v4.29" from "you should
grep to confirm". If you propose a lemma name you're unsure about, say so explicitly and give the
fallback. Do not invent lemma names silently. The goal is a green build with zero sorry/axiom.
</grounding_rules>
