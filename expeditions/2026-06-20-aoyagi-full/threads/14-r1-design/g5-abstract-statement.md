# G5-abstract — c-o-v-tree-gluing: precise statement + proof skeleton (for fm-2, task #52)

- **Seat:** `pp` (design, measure-side). For `fm-2` (task #52). The reusable measure engine the (2,2,2)
  cover and the general atlas both instantiate.
- **Mathlib anchors CHECKED** (against `.lake/packages/mathlib`): the c-o-v lemma, the null-image lemma,
  lintegral set-additivity all exist. G5-abstract = compose them by finite iteration.

## The minimal deliverable: the SINGLE-STEP lemma (the reusable atom)

For a FIXED M (the ladder), NO abstract rose-tree datatype is needed — the resolution is finitely-many
compositions of ONE single-step lemma. Build that first.

> **G5-step.** Let `U ⊆ ℝ^N` measurable, `μ = volume`. Let `{φ_i : ℝ^N → ℝ^N}_{i : ι}` (`ι` Fintype),
> each `C¹` on a measurable `V_i`, with `Z_i ⊆ V_i` ("exceptional": non-injective / `det = 0` locus):
> - **(H-null)** each `Z_i` is null;
> - **(H-inj)** `InjOn φ_i (V_i \ Z_i)`;
> - **(H-cover)** `U =ᵃᵉ ⋃ i, φ_i '' (V_i \ Z_i)`;
> - **(H-disj)** the `φ_i '' (V_i \ Z_i)` are pairwise a.e.-disjoint.
> Then for any measurable `g : ℝ^N → ℝ≥0∞`:
> ```
> ∫⁻ x in U, g x ∂μ = ∑ i, ∫⁻ y in (V_i \ Z_i), ENNReal.ofReal |(fderiv ℝ φ_i y).det| * g (φ_i y) ∂μ.
> ```

## Proof skeleton (Lean)

1. `U =ᵃᵉ ⋃ i, φ_i '' (V_i \ Z_i)` — from (H-cover) directly; the `Z_i`-images are null (H-null +
   `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`), so dropping them is a.e.-harmless.
2. `∫⁻ x in U, g = ∫⁻ x in (⋃ i, φ_i '' (V_i \ Z_i)), g` — `setLIntegral_congr` on the a.e.-equal sets.
3. `= ∑ i, ∫⁻ x in φ_i '' (V_i \ Z_i), g` — lintegral over an a.e.-disjoint finite union (set-additivity
   of `lintegral`; (H-disj)).
4. per term: `∫⁻ x in φ_i '' (V_i \ Z_i), g = ∫⁻ y in (V_i \ Z_i), ofReal |det fderiv φ_i y| · g(φ_i y)`
   — `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (`Jacobian.lean:1189`) with `hs` = `V_i \ Z_i`
   measurable, `hf'` = `C¹` there, `hf` = (H-inj).

## The ONE friction (InjOn-off-null adapter)

Mathlib's c-o-v wants `InjOn` on the WHOLE measurable set. Blow-up charts are injective only OFF the
exceptional `Z_i` (a null set). The adapter: apply the lemma to `s = V_i \ Z_i` (injective there); the
excised `Z_i` is null so `∫⁻ over V_i = ∫⁻ over V_i \ Z_i` (a `setLIntegral` congr modulo the null
`Z_i`). Intricate-standard, no new math.

## Why ℝ≥0∞ (not Bochner) — the load-bearing choice

The threshold integrand `|F|^{-c}` is `+∞` above the rlct. Over `lintegral` (ℝ≥0∞-valued) the identity
`∫⁻ = ∑` holds UNCONDITIONALLY (no integrability side-conditions) — Tonelli/monotone, `+∞` handled.
This is why G5 is intricate-standard, not the wall: stating it over `lintegral` sidesteps every
integrability obligation. (Do NOT state it over Bochner `∫` — that reintroduces integrability hyps the
threshold integrand fails.)

## The tree (general-M only — NOT needed for the ladder)

The general resolution is a finite ROSE TREE; G5-step applies at each node, recursing into children.
Lean (general-M): structural recursion on a tree datatype, OR unfold to leaves (compose G5-step finitely
often). For FIXED M the LEAF-SUM form suffices — `N` applications of G5-step, no tree datatype. Defer
the abstract-tree form until general-M (it's part of the G3-roadmap, not the down-payment).

## How the ladder instantiates it

- **(2,2,2):** G5-step at the A-blowup (`ι` = 4 charts) ∘ at each step-2 (`ι` = 3) ∘ at each block
  (`ι` = 4) = the 24-leaf `∫⁻=∑∫⁻`. Each application discharges (H-null/inj/cover/disj) from the
  EXPLICIT polynomial charts (mechanical).
- **(2,1,2):** does NOT use G5 (Fubini-product, the variables separate — the product-MIN lemma instead).
- **(1,1,1):** does NOT use G5 (one identity chart = whole space).

So G5-step's first real consumer is (2,2,2); building it (task #52) and proving the (2,2,2) cover are
the same work at that scale.

## Exact Mathlib anchors (CHECKED — for the active build)

Every step of the skeleton has a named Mathlib lemma; G5-step is composing them, no new analysis:
- **Per-chart c-o-v (step 4):** `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
  (`Mathlib/MeasureTheory/Function/Jacobian.lean:1189`):
  `(hs : MeasurableSet s)(hf' : ∀ x∈s, HasFDerivWithinAt f (f' x) s x)(hf : InjOn f s)(g : E→ℝ≥0∞) : ∫⁻ x in f''s, g = ∫⁻ x in s, ofReal |(f' x).det| · g (f x)`.
- **Disjoint finite-union additivity (step 3):** `lintegral_biUnion_finset` (or `lintegral_iUnion` for the
  indexed form) — for pairwise-disjoint measurable pieces, `∫⁻ over ⋃ = ∑ ∫⁻ over each`.
- **a.e.-set congruence (step 2):** `setLIntegral_congr` — `s =ᵃᵉ t ⟹ ∫⁻ x in s, g = ∫⁻ x in t, g`.
- **Null-exceptional image (H-null discharge):** `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` —
  the `det fderiv = 0` locus has null image (the exceptional `φ_i '' Z_i` is null).

## The InjOn-off-null adapter, as a concrete sub-lemma (the one friction, spelled out)

The friction is purely: c-o-v wants `InjOn f s`, but blow-up charts are injective only on `V_i \ Z_i`.
The adapter is a TWO-LINE composition — state it as its own sub-lemma so it's reused at every node:

> **G5-adapter.** If `Z` is null and `f` is `C¹` and `InjOn f (V \ Z)`, then
> `∫⁻ x in f''(V \ Z), g = ∫⁻ y in (V \ Z), ofReal |det fderiv f y| · g(f y)`,
> and (dropping the null `Z` from the source) `∫⁻ y in V, … = ∫⁻ y in (V \ Z), …`.

Proof: the eq over the image is `lintegral_image_eq_lintegral_abs_det_fderiv_mul` on `s = V \ Z`
(measurable; `f` `InjOn` there; `C¹`); the source-side drop is `setLIntegral_congr` with
`V \ Z =ᵃᵉ V` (from `diff_null_ae_eq_self`, since `Z` null). So every chart uses `V \ Z` where
injectivity holds, while the sum is stated over `V` (the `Z`-contribution being null). NO new analysis.

## Suggested build order for task #52 (fm-2)

1. **G5-adapter** (the 2-line sub-lemma above) — the reusable atom; isolates the InjOn-off-null friction.
2. **G5-step** (the finite a.e.-disjoint null-cover ⟹ `∫⁻_U = ∑_i ...`) — adapter + `lintegral_biUnion_finset`
   + `setLIntegral_congr` (for `U =ᵃᵉ ⋃`).
3. **(2,2,2) leaf-sum** — G5-step composed at the A-blowup (4) ∘ step-2 (3) ∘ block (4); discharge the
   per-node hyps from the explicit polynomial charts.
Stop at the leaf-sum for fixed-M; the abstract-tree datatype is general-M (G3 roadmap), NOT needed here.
