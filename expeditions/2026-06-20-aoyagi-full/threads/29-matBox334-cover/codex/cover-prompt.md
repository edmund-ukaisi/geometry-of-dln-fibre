<task>
I am formalising, in Lean 4 + Mathlib (v4.29 pin), the LAST gap of a measure-theory finiteness theorem.
I want a decorrelated review of the PROOF ARCHITECTURE for the cleanest Lean structure, especially the
two hardest sub-pieces (a 9-chart radial cover over a 3x3 matrix, and a per-chart permutation
normalization). I am NOT asking for Lean syntax — I want the mathematical/structural design vetted and the
cheapest correct decomposition identified.

## The target (sole remaining `sorry`)

```
theorem matBox334_blowup_lt_top (c' : ℝ) (hc0 : 0 < c') (hc4 : c' < 4) :
    ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) < ⊤
```
- `A0 : Fin 3 → Fin 3 → ℝ`, `A1 : Fin 3 → Fin 4 → ℝ`. `matBox p n 1 = [-1,1]^{p×n}` (free entries).
- `frobSq M = ∑ᵢ ∑ⱼ (M i j)^2`. `rmatMul X Y i j = ∑ₖ X i k * Y k j`. `^(-c')` is `Real.rpow`.
- The integrand has a singularity where `frobSq(A0·A1) → 0`, i.e. where the product degenerates.

## What is ALREADY BANKED (sorry-free, I consume these; do NOT redesign these)

1. `resolved334_lt_top (c') (hc2 : 2 < c') (hc4 : c' < 4) :`
   `∫⁻ Δ in matBox 2 2 1, ∫⁻ S in matBox 2 4 1, ∫⁻ T in morseBox 4 1,`
   `  ENNReal.ofReal ((∑ i, (T i)^2 + frobSq (rmatMul Δ S))^(-c')) < ⊤`
   — the "resolved normal form" RHS. Δ is 2×2, S is 2×4, T is a free 4-vector (`morseBox 4 1 = [-1,1]^4`).
   NOTE: requires `2 < c'`.

2. `frobSq_angularR_ge (b0 b1 g0 g1 d00 d01 d10 d11 : ℝ) (hg0 : g0^2 ≤ 1) (hg1 : g1^2 ≤ 1) (A1 : Fin 3 → Fin 4 → ℝ) :`
   `(1/5) * ((∑ j, (A1 0 j + (b0*A1 1 j + b1*A1 2 j))^2)`
   `  + frobSq (rmatMul (!![d00,d01; d10,d11] : Matrix (Fin 2)(Fin 2) ℝ) (fun k j => A1 (k.succ) j)))`
   `  ≤ frobSq (rmatMul (angularR b0 b1 g0 g1 d00 d01 d10 d11) A1)`
   where `angularR ... = !![1, b0, b1; g0, d00+g0*b0, d01+g0*b1; g1, d10+g1*b0, d11+g1*b1]`.
   This is the per-chart comparability for the pivot at position (0,0): when A0 = a·R with R having a 1
   in the TOP-LEFT corner, `frobSq(R·A1) ≥ (1/5)(‖T‖² + frobSq(Δ·S))` with T = top row + shear, Δ = 2×2
   lower-right minor, S = A1 rows 1,2. The ratios |g0|,|g1| ≤ 1 are guaranteed on a max-modulus-entry chart.

3. Cover machinery on a FLAT carrier `Fin N → ℝ`:
   - `argmaxCellOn (active : Finset (Fin N)) (p) = {y | y p ≠ 0 ∧ ∀ j ∈ active, |y j| ≤ |y p|}` (entry p is max-modulus).
   - `univ_ae_cover (active) (p) (hp : p ∈ active) : (univ : Set (Fin N → ℝ)) =ᵐ ⋃ q ∈ active, argmaxCellOn active q`.
   - `pivotBlowupOn (active) p x = fun i => if i=p then x p else if i ∈ active then x p * x i else x i` (radial blowup: pivot kept, others scaled by pivot).
   - `pivotBlowupOnDeriv_det (active)(p)(hp)(x) : det = (x p)^(active.card - 1)`. For active=univ over Fin 9, card-1 = 8, so |det| = |a|^8.
   - `g5_pivotNode (active) (U) (hUcov : U =ᵐ ⋃ argmaxCellOn) (g) :`
     `∫⁻ x in U, g x = ∑ p ∈ active, ∫⁻ x in chartDomOn active p \ pivotZeroOn p, ofReal|det(pivotBlowupOnDeriv active p x)| * g (pivotBlowupOn active p x)`
     — the packaged "cover ∫_U by argmax charts, change of variables" node, all measure obligations discharged. `chartDomOn active p = {x | ∀ j ∈ active, j≠p → |x j| ≤ 1}`, `pivotZeroOn p = {x | x p = 0}`.
   - `coordZero_null (p) : volume {x | x p = 0} = 0`.
   - `matToFlatEquiv (r n) : (Fin r → Fin n → ℝ) ≃ᵐ (Fin (r*n) → ℝ)` measure-preserving (flatten a matrix to a vector).
   - Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (geometric c-o-v) and `Real.rpow_le_rpow_of_exponent_ge (0<x)(x≤1)(z≤y) : x^y ≤ x^z`.

## The intended route (from a pen-and-paper design cert), and my two worries

Cover A0's 9 entries by the 9 max-modulus-entry charts (`argmaxCellOn (univ : Finset (Fin 9))`), via
flattening A0 with `matToFlatEquiv 3 3`. On chart p=(i,j): A0 = a·R, |det| = |a|^8, and
`frobSq(A0·A1) = a²·frobSq(R·A1)` (degree-2 homogeneity). Then
`|det|·frobSq(A0·A1)^{-c'} = |a|^{8-2c'} · frobSq(R·A1)^{-c'}`,
Tonelli-separate the |a|-axis (finite for c' < 9/2, banked `radialAxis334_lt_top`), and lower-bound
`frobSq(R·A1) ≥ (1/5)(‖T‖²+frobSq(Δ·S))` to feed `resolved334_lt_top`.

WORRY 1 (the permutation). `frobSq_angularR_ge` is stated for the pivot at (0,0). For a general pivot
(i,j), R has its 1 at position (i,j), not (0,0). I plan to use that frobSq is invariant under row/column
permutations: permute A0's rows (i→0) and columns (j→0) to bring the pivot to (0,0); the column
permutation of A0 induces a ROW permutation of A1, which is a measure-preserving bijection of `matBox 3 4 1`
(symmetric box). Question: is this the cleanest way, or is there a cheaper structure? E.g. should I instead
prove a pivot-(i,j) variant of `frobSq_angularR_ge` directly (9 cases), or is there a slick way to avoid
the permutation entirely (e.g. cover only by a SINGLE chart sufficient up to a measure-preserving relabel)?
Is the "9 charts but each reduces to (0,0) by an A0-row/col perm + A1-row perm" genuinely sound, given the
A1-box is symmetric so its measure is perm-invariant?

WORRY 2 (the box rescale + the c' ≤ 2 case). After the per-chart bound I get
`∫_{chart} |a|^{8-2c'} · (1/5)^{-c'} (‖T‖²+frobSq(Δ·S))^{-c'}` over a chart domain where the angular
ratios are in [-1,1] but T = (top row of A1) + (shear by ratios)·(rows 1,2 of A1) ranges over a LARGER box
than morseBox 4 1 (since |ratios|≤1 and A1 entries in [-1,1], T entries are in roughly [-3,3]). I need to
rescale/enlarge to feed `resolved334_lt_top` which is stated on `morseBox 4 1 = [-1,1]^4` and `matBox 2 2 1`,
`matBox 2 4 1`. Question: what is the cleanest way to handle the box mismatch? Options: (a) prove a scaled
variant `resolved334_lt_top` on box [-K,K] (by scaling c-o-v, picks up a constant), (b) dominate the chart
domain integral by an integral over a fixed larger box and relate to `resolved334` by monotonicity +
rescale, (c) something else. ALSO: `resolved334_lt_top` needs `2 < c'`. For `0 < c' ≤ 2`, I plan to split
the domain by `{frobSq ≥ 1}` (integrand ≤ 1, finite over the bounded box) vs `{0 < frobSq < 1}` (use
`rpow_le_rpow_of_exponent_ge` to bump c' up to some c'' ∈ (2,4), then the c''-integral over the same domain
≤ the full c''-integral which is finite by the cover). Is this split sound and is it the cheapest reduction
to the `2 < c'` case?

## A KEY subtlety I want vetted

In the banked `frobSq_angularR_ge`, the "Δ" 2×2 minor is `!![d00,d01;d10,d11]` and the angular matrix is
`!![1,b0,b1; g0,d00+g0*b0,...; g1,...]`. So the lower-right 2×2 block of R is `Δ + γβ` (a SHIFTED minor),
not the raw lower-right entries of A0/|a|. When I do `pivotBlowupOn` on the flat A0, the chart gives me
R with R_p = 1 and R_k = A0_k / a (raw ratios). To match `angularR`'s parametrization I must read off
b0,b1 (top row ratios), g0,g1 (left col ratios), and d00..d11 such that `d00 = R[1][1] - g0*b0` etc.
(the de-shift). Is this read-off (solving for d-params from the raw R entries) a real obligation, or does
it fall out trivially because `angularR` is a bijective reparametrization of the 8 free off-pivot ratios?
Confirm the count: R has 8 free entries (the 9 minus the pinned 1); angularR has 8 params (b0,b1,g0,g1,d00..d11);
the map params→R is a bijection (triangular: read b,g off the first row/col, then d off the rest). Is that right?
</task>

<output_contract>
Respond in exactly these sections, terse:
1. VERDICT on the overall route: sound / has-a-hole / cheaper-alternative. One paragraph.
2. WORRY 1 (permutation): is the perm route sound? Is it the cheapest? If a cheaper structure exists, name
   it concretely (which lemma shape). Flag any soundness trap in "A1-row-perm is measure-preserving on the
   symmetric box".
3. WORRY 2a (box rescale): rank options (a)/(b)/(c) by Lean-effort; give the cheapest concrete shape. Note
   the EXACT box T ranges over (T_j = A1 0 j + b0·A1 1 j + b1·A1 2 j with |b|≤1, |A1|≤1, so |T_j| ≤ 3).
4. WORRY 2b (c'≤2 split): is it sound and cheapest? Any trap (e.g. measurability of the split sets, the
   frobSq=0 locus where rpow is ill-behaved).
5. The KEY subtlety (angularR reparametrization bijection): confirm or refute the read-off count.
6. The SINGLE highest-risk Lean step in this plan, and the cheapest way to de-risk it.
7. Anything I am MISSING (a confound, a measurability gap, a non-vacuity issue).
</output_contract>

<grounding_rules>
- Distinguish what you can verify from the given statements vs what you are inferring.
- If a banked lemma's stated form does not actually support a step I claim, SAY SO explicitly — that is the
  most valuable output.
- Do not invent Mathlib lemma names; if you reference one, mark it as "verify it exists".
</grounding_rules>
