<task>
I am formalising in Lean 4 + Mathlib a single remaining `sorry` (`hproducer`) inside a theorem
`framedParams_split_eq_frame_raw` about the RLCT of deep linear networks. I need a design review of
the proposed proof route, focusing on SOUNDNESS and Lean-feasibility, BEFORE I invest.

## Setup (objects, all in one Lean file `DeepestGaugeConstruction.lean`)

L = network depth (we only care about L = 2 here; there are 2 vacuous-at-L=2 interior sorries elsewhere).
H : Fin (L+1) → ℕ layer widths. r = rank. B = rank-r target matrix. We are at the "deepest point" w0.
w ranges over flat parameter space `Fin (flatDim H) → ℝ`. `split : flat ≃ₜ DeepestSplit` a homeomorphism.
`A w := (paramsEquivFlat H).symm w : Params H` is the raw per-layer matrix tuple.
`prod H (A w)` = the product of the layer matrices = the network's output matrix.
`N(w) := prod H (A w) − B` = the residual (→ 0 at w0).

Two energy functions of w:

(1) `Sreg(w)`. Let `P := reindex(rThr_0, pivotThr_L J)(P0 · (prod(A w) − B) · QL)` where P0,QL are FIXED
invertible endpoint frames, rThr = the "first-r-then-rest" threshold split, pivotThr J = the threshold
split whose LEFT block enumerates the r PIVOT columns Set.range J (sorted), J the B-pivot embedding.
P is reindexed into 2x2 blocks `fromBlocks (P00−1) P01 P10 P11`.
`Sreg(w) := ∑(P00−1)² + ∑P01² + ∑P10²` (Frobenius energies of the three "regular" blocks).
This is what the LOSS sees.

(2) `∑ deepestEFull²(split w)`. `deepestEFull q i` reads the SAME three blocks but of a DIFFERENT matrix:
`Q := reindex(rThr_0, pivotThr_L J)(prod H (framedParamsPivot H r hr hL J Pf Qf q))`, where
`framedParamsPivot` is a per-layer reconstruction: non-last layers `s` give `Pf s · (A w) s · Qf s`
(a clean conjugation), but the LAST layer is reindexed on the COLUMN side by `pivotThr_L (pivotJSucc J)`
and carries the gauge "reads" placed at PIVOT columns. So `prod(framedParamsPivot(split w))` is NOT
simply `P0 · prod(A w) · QL`: the last factor carries a fixed orthogonal column-permutation `Pπ`
relating the pivot ordering to the threshold ordering. Call this refuted clean telescope `hS1'`.

`deepestEFull_base : deepestEFull … 0 = 0` is PROVED (both energies vanish at w0).

## The target `hproducer` (the conjuncts I must produce, ∃ t γ₁ γ₂ δ₁ δ₂ > 0 and ∃ U ∈ 𝓝 w0, ∀ w ∈ U):
(a) block decomposition: `reindex(P0·(prod(A w)−B)·QL) = fromBlocks (P00−1) P01 P10 P11`, P00 invertible.
(b) two-sided comparability: `δ₁·Sreg(w) ≤ ∑deepestEFull²(split w) ≤ δ₂·Sreg(w)`.
(c) leak bound: `∑(P10·P00⁻¹·P01)² ≤ t²·Sreg(w)`.
(d)/(e) folded core comparability: `Sreg + ∑Rcore² ≍ Sreg + coreΦ` (Rcore = P11 − P10 P00⁻¹ P01, coreΦ =
`deepestCoreF (deepestCoreAbsorb (split w)).2.1`), via a BUILT atom `schur_core_germ_comparability`.

## The proposed route (from a pen-and-paper cert, "A' pointwise"):
The cert claims (b) is NOT a germ/Taylor statement but a POINTWISE fixed-invertible-map Frobenius
comparability: it asserts a FACT2 identity `reindex_piv(M·Pπ) = reindex_thr(M)` reconciling the pivot
ordering with the threshold ordering, applied to the DEVIATION ONLY (keeping the corner subtraction in
the pivot convention — flagged soundness-critical: do NOT colPerm the corner or a spurious −1 appears).
After FACT2, both `∑deepestEFull²` and `Sreg` are claimed to be `‖E·vec(N-conj(w))‖²` for two FIXED
invertible linear maps E_thr, E_piv (permutations × the fixed unit QL), hence pointwise comparable by a
generic "two fixed invertible reindexings of the same residual ⇒ both PD Gram forms, same kernel ⇒
two-sided comparable" lemma. Exact-certified only at r=1,H0=1,H2=2. FACT2 is NOT yet a Lean lemma.

## My concerns I want adjudicated:
1. Is (b) actually pointwise-true (a fixed-map comparability), or does the column-permutation `Pπ` sitting
   on the LAST factor INSIDE the product genuinely make `∑deepestEFull²(split w)` and `Sreg(w)` differ by
   more than a fixed invertible map of the SAME residual N(w)? Concretely: `deepestEFull` reads
   `prod(framedParamsPivot(split w))` which has a NONLINEAR dependence on w (it is a product of L=2
   layer-matrices, each affine in w); `Sreg` reads `P0·(prod(A w)−B)·QL`. Are these two genuinely
   `(fixed invertible map) applied to the same N(w)` POINTWISE, or only to leading order at w0?
   At L=2: `prod(A w) = (A w)_0 · (A w)_1`. Is `prod(framedParamsPivot(split w))` equal to
   `(fixed P0) · prod(A w) · (fixed QL·Pπ-ish)` pointwise, or is the gauge "core read" injecting extra
   w-dependence that is NOT a fixed linear image of N(w)?
2. If (b) is only leading-order (germ) true, the pointwise route is unsound and I'd need the Taylor route.
   Which is it? Give the single cheapest discriminating test (a small explicit L=2 numeric or symbolic
   test) that would settle pointwise-vs-germ.
3. Module placement: the (b)-atom references `deepestEFull`, which is DEFINED in the SAME file as
   `hproducer`. The cert assumed it was in a lower module (so the atom could go in a new higher module).
   Given it is same-file, must the (b)-atom be proved INLINE in `hproducer`, with only the generic
   fixed-map Frobenius lemma extracted to the lower module `DeepestSchurComparability`? Any cleaner option?
4. Realistic Lean LoC + risk ranking of the 5 sub-lemmas: (i) the (b)-atom, (ii) eventually P00 invertible
   (det continuous, =1 at w0), (iii) eventually leak (Cauchy-Schwarz, P01/P10→0, ⅟P00 bounded), (iv)
   wiring the built core atom, (v) the 𝓝 assembly (finite ∩). Which is the real risk?

KEY EXTRA STRUCTURE you should use: there is a PROVED lemma `deepestEPivot_sq_sum_eq_blocks` stating
`∑ deepestEPivot²(p) = ∑(Q.toBlocks₁₁−1)² + ∑Q.toBlocks₁₂² + ∑Q.toBlocks₂₁²` where Q is the reindex of
`prod(framedParamsRegPivot p)` (the T=0 / core-slot-zero version). And `deepestEFull_coreZero`:
`deepestEFull(reg,0,spec) = deepestEPivot(reg,spec)`. So `∑deepestEFull²(split w)` ALSO equals the
three-block Frobenius energy of Q(w) = reindex(prod(framedParamsPivot(split w))) by the analogous block-
sum identity. So BOTH (1) and (2) are "three-block Frobenius energies of a reindexed matrix"; the
question is whether the two reindexed matrices are fixed-invertible images of one another pointwise.
</task>

<output_contract>
1. VERDICT on concern #1/#2: is (b) pointwise-true or only germ-true? State your confidence and the
   single load-bearing reason. If pointwise, sketch why `prod(framedParamsPivot(split w))` is a fixed
   invertible image of `prod(A w)−B`; if germ-only, say so plainly.
2. The single cheapest discriminating test (explicit small L=2 case) to settle it, with the exact numbers
   to compute.
3. Module-placement recommendation (inline vs new module), one line.
4. Risk-ranked list of the 5 sub-lemmas with a realistic Lean LoC estimate each; name the one most likely
   to sink the tide.
5. If (b) is germ-only: the minimal honest fallback (what `sorry` statement to leave, precisely named).
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE from the structure I gave vs what you are INFERRING/guessing. The L=2
product structure and the placement of `Pπ` on the last factor are the load-bearing facts; reason from
them. Flag any step where you are assuming a property of `framedParamsPivot` I did not state.
</grounding_rules>
