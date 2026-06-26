<task>
I have reduced a Lean measure-theory finiteness theorem to a single remaining gap (one `sorry`), a
per-chart lemma. I want you to VET whether (a) the per-chart lemma STATEMENT is the right object (so the
next person builds on a correct interface), and (b) one structural simplification I claim ("indicator
decoupling") is mathematically SOUND. I am NOT asking you to write a proof — I want the statement and the
key insight audited for soundness.

## Context

`matBox p n 1 = [-1,1]^{p×n}`. `frobSq M = ∑ᵢⱼ (M i j)²`. `rmatMul X Y i j = ∑ₖ X i k · Y k j`.
The original target (now PROVED modulo the gap below):
`∫_{A0∈matBox 3 3 1} ∫_{A1∈matBox 3 4 1} frobSq(A0·A1)^{-c'} < ⊤` for `2 < c' < 4`.

I flattened A0 (3×3) to `Fin 9 → ℝ` via a measure-preserving coordinate equiv `matToFlatEquiv 3 3`, then
used the banked "argmax pivot blowup cover" machinery on `Fin 9`:
- `argmaxCellOn univ p = {y | y p ≠ 0 ∧ ∀ j, |y j| ≤ |y p|}` (entry p is max-modulus).
- `pivotBlowupOn univ p y = fun i => if i=p then y p else y p · y i` (radial blowup, pivot = scale).
- `chartDomOn univ p = {y | ∀ j ≠ p, |y j| ≤ 1}` (ratios bounded).
- `pivotZeroOn p = {y | y p = 0}`.
- `recStep` splits `∫_{flatBox} g = ∑_{p} ∫_{chartDomOn p \ pivotZeroOn p} |det(blowupDeriv)| · flatBox.indicator g (blowup y)`, with `|det(blowupDeriv univ p y)| = |y p|^8`.
- `flatBox334 = {y : Fin 9→ℝ | ∀ i, |y i| ≤ 1}` (the flattened A0-box).
- `gFlat334 c' y = ∫_{A1∈matBox 3 4 1} frobSq(rmatMul (unflatten y) A1)^{-c'}`.

So the WHOLE thing reduces (PROVED) to: each of the 9 summands is `< ⊤`. That single remaining gap is:

```
theorem matBox334_chart_lt_top (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) (p : Fin 9) :
    ∫⁻ y in chartDomOn univ p \ pivotZeroOn p,
        ENNReal.ofReal (|y p|^8)            -- (after rewriting |det| = |y p|^8)
          * flatBox334.indicator (gFlat334 c') (pivotBlowupOn univ p y)
      < ⊤
```

## What I have established (PROVED, by `rfl` / banked lemmas)
- `|det(blowupDeriv univ p y)| = |y p|^8`.
- `pivotBlowupOn univ p y i = if i=p then y p else y p · y i`.
- unflatten distributes the scalar: `unflatten (fun i => a · R i) r c = a · (unflatten R) r c`.
- `frobSq((a•M)·A1) = a²·frobSq(M·A1)` (degree-2 homogeneity, banked).
- I have a banked `resolved334_box_lt_top (K) (2<c'<4)`:
  `∫_{Δ∈box22 K}∫_{S∈box24 K}∫_{T∈morseBox 4 K} (∑T² + frobSq(Δ·S))^{-c'} < ⊤`.
- A banked per-(0,0)-pivot bound: `frobSq(R·A1) ≥ (1/5)(∑T² + frobSq(Δ·S))` where R is the 3×3 angular
  matrix with a 1 in the TOP-LEFT corner, T = (A1 row0) + shear, Δ = lower-right 2×2 minus γβ, S = A1 rows 1,2.
- A banked radial 1-D fact: `∫_{[-1,1]} |a|^{8-2c'} < ⊤` for c' < 9/2 (so for c' < 4).

## THE TWO THINGS TO VET

VET-1 (the indicator decoupling — is it SOUND?). I claim: ON `chartDomOn univ p` (where `|y_k| ≤ 1` for
k≠p), the indicator `flatBox334.indicator (...) (pivotBlowupOn univ p y)` fires IFF `|y p| ≤ 1`. Reason:
the blown-up entries are `y p` (at p) and `y p · y_k` (k≠p); since `|y_k| ≤ 1` on the chart domain,
`|y p · y_k| ≤ |y p|`, so `|y p| ≤ 1 ⟹ all blown-up entries ≤ 1` (and conversely `y p` itself must be ≤ 1).
Hence the indicator depends ONLY on `|y p|`, decoupling the radial coordinate `y p` from the 8 ratios.
Is this reasoning correct? Any edge case (e.g. y p = 0 — but that's excluded by `\ pivotZeroOn p`; or the
"converse" direction where some |y_k| could matter)?

VET-2 (is the STATEMENT the right object?). Is `matBox334_chart_lt_top` as stated the correct
per-chart obligation that `recStep` produces, and is it genuinely finite for `2<c'<4` (not vacuous, not
mis-scoped)? In particular: after the radial separation and the per-pivot permutation to the (0,0) normal
form, is feeding `resolved334_box_lt_top 3` (boxes enlarged to K=3) the right move, given the de-shift
`d = raw - γβ` puts Δ-entries in [-2,2] and T-entries in [-3,3]? Is K=3 sufficient for BOTH Δ and T, or do
I need different radii per block (and does `resolved334_box_lt_top` with a single K=3 cover both, since
[-2,2] ⊆ [-3,3])?

VET-3 (the per-pivot permutation soundness). For a general pivot p=(i,j) (not (0,0)), I bring the pivot to
(0,0) by permuting A0's rows (i→0) and columns (j→0). The A0 column permutation induces a row permutation
of A1. Is it sound that this A1-row-permutation is measure-preserving on `matBox 3 4 1` (the symmetric box),
so the A1-integral is unchanged? And that frobSq(A0·A1) is invariant under (rowperm A0, colperm A0 + the
induced rowperm A1)? Any subtlety I'm missing (e.g. the permutation must be applied consistently to the
blown-up R, not just abstractly)?
</task>

<output_contract>
Terse, three sections:
VET-1: SOUND / has-a-flaw. If flawed, the exact edge case.
VET-2: right-object / mis-scoped. Confirm or correct the K=3 box-radius choice; flag if the statement is
  vacuous or wrong-typed.
VET-3: sound / flawed. Confirm the A1-row-perm MP + frobSq invariance, or name the subtlety.
Then: the SINGLE most likely place this chart lemma's proof will go wrong, and the cheapest guard.
</output_contract>

<grounding_rules>
- Distinguish verified-from-given vs inferred. If a claimed banked lemma can't support a step, say so.
- Do not invent Mathlib lemma names.
</grounding_rules>
