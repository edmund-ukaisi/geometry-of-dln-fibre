# Witness tide — finding: the a.e.-positivity target `∃ w, achieverUfun w ≠ 0` is FALSE for ~19% of M

**Seat:** lean-formaliser (witness tide). **Date:** 2026-06-27. Branch: worktree off
`expedition/aoyagi-full` (merged, baseline green). **No Lean committed** (the witness I would build is
either wrong, or — for a substantial class of `M` — proves a FALSE statement). This note is the handback.

## TL;DR

The brief's target `∃ w : Fin N → ℝ, achieverUfun M hL hN w ≠ 0` (which would close `Ubound` ∀M, `2≤L`)
is **TRUE for 285/351 M but provably FALSE for 66/351 (≈19%) M with `minAdm ≥ 1`** — those where the
achiever rank-drops sit only at the boundary layers. For those M, `achieverUfun ≡ 0` (rigorously, not
numerically), so the rate-side `Ubound` (a.e.-positivity of `Ufun`) is unattainable via the achiever
chart `phiFlatStructV`. The certificate's "VALIDATED, NO research wall" was validated only on dead-leaf
interior-drop cases; it missed (a) the live-leaf majority and (b) this degenerate class.

## What is solid (verified)

1. **The banked reduction is correct.** `achieverUfun w = ∑∑ (Hmat 0 i j)²` (the ℝ telescope chain at
   `w p`), via `achieverUfun_eq_eval` + `eval_UPolyGen` + `VvalGen_eq_sqSumHmat0`. So `≠ 0 ⟺ Hmat 0 ≠ 0`
   at `w`. `Hmat 0` is built by `Chain.Hmat_succ`: `Hmat s = B_s·Hmat(s+1) + E_s·suffix(s+1)`, `Hmat L =
   Rfin L = 0`. The decoder `genBlkFlatStruct` has `Rfin ≡ 0` and no boundary-`L−1` lift (`Wblk(L)=0`).

2. **The 285 interior-drop cases: witness EXISTS, clean construction (exhaustively validated).**
   When some GenBlk boundary `p ∈ [1, L−1]` has a nonempty E-block (`r_p = Text p − Text(p+1) ≥ 1` and
   `c_p = Wext p − Text(p+1) ≥ 1`): pivot `E_p` at the bottom-right `(0,0)` of `Rmat_p`, and carriers
   `W_b(0, colPath b) = 1` for `b ∈ [p, L−1]`, where `colPath` tracks the surviving column of `suffix(b+1)`
   down to `suffix L = I` (`colPath L = 0`; after a carrier at `b`, the surviving row becomes `Text(b+1)`,
   so the next-up carrier reads column `Text(b+1)`). This gives `Hmat 0 ≠ 0`. **Exhaustively verified `Hmat
   0 ≠ 0` over ALL 285 such M** (`M ∈ {1,2,3}^{L+1}`, `L ∈ {2,3,4}`, `minAdm ≥ 1`), in an exact-arithmetic
   model that reproduces the prior sympy cert on `M=(3,3,1,3)`. The carrier COLUMNS are NOT uniformly `0`
   (the certificate's "carriers at (0,0)" is wrong for the live leaf — e.g. `M=(2,2,3,2)` needs `W` at
   column 1). This is the corrected `rowPath`/`colPath` the cert's skeleton anticipated; the Lean is the
   bounded downward induction (`Finset.sum_eq_single` over the banked entry laws + the dependent-`Fin`
   cast kernel).

3. **The 66 boundary-drop cases: `achieverUfun ≡ 0`, RIGOROUSLY (theorem FALSE).** When NO interior
   boundary `p ∈ [1, L−1]` has a nonempty E-block — equivalently `Text` is flat on `[1, L−1]` (every
   interior `r_p = 0`) — then every interior `Rmat_p` (for `p < L`) has an empty E-block, so `Rmat_p = 0`;
   the leaf `Rmat_L` is never used (`C L = u·Rfin L = 0`). Hence every `E_chain p = Rmat_p · A_p = 0`, and
   `Hmat L = Rfin L = 0`, so `Hmat s = B_s · Hmat(s+1) = … = 0` for all `s`. Thus `Hmat 0 ≡ 0`
   UNCONDITIONALLY (independent of `K/X/N/W`), i.e. `achieverUfun ≡ 0`. This is a direct structural
   consequence of `Rfin ≡ 0` + flat-interior-`Text`, NOT a numerical artifact. Exhaustive count: exactly
   66/351 `minAdm≥1` cases. Examples: `(1,2,1)`, `(2,1,1)`, `(3,2,1)`, `(2,2,1,1)`, `(1,2,2,1)`.

   **Root cause (the index mismatch).** The chain has length `L`, but the achiever path `tStar : Fin L`
   carries its rank-drop-to-`0` at index `L−1` (the `admPred` last-rank condition), and the chain leaf is
   `Text L = tach (L−1) = tStar (L−2)` — so the FINAL drop `tStar(L−2) → tStar(L−1)=0` falls OFF the
   chain's leaf (there is no `Text (L+1)`). When ALL of `minAdm` comes from boundary-layer drops (first
   layer, or the off-chain last drop), the chain sees no E-block, and `achieverUfun ≡ 0`.

## Consequence for the brief

The brief's claim that this witness "completes the rate-side `NodeAchieverChart` fields ∀M (2≤L)" is
**incorrect**. `NodeAchieverChart.Ubound` requires `Ufun > 0` a.e.; with `Ufun = achieverUfun` and the
chart `phi = phiFlatStructV` (the banked achiever-path instantiation), this FAILS for the 66 boundary-drop
M (`achieverUfun ≡ 0` means `Ufun > 0` holds on a NULL set, and `routeMCore ∘ phi ≡ 0` means `phi` maps
into the zero-loss locus — a degenerate chart). The rate side is NOT completable ∀M via this chart.

## Recommended triage (controller)

This is a CHART-CONSTRUCTION / SCOPE gap, not a witness-finding gap. Options, in rough order:
- **(A) Scope the target.** State + prove the witness only for the 285 interior-drop M (an explicit,
  checkable hypothesis: `∃ p ∈ [1, L−1], r_p ≥ 1 ∧ c_p ≥ 1`), and handle the 66 boundary-drop M with a
  separate (different) chart — analogous to how `L=1` rides `DeepestBaseL1`. The boundary-drop class is
  exactly "achiever drops rank only at the first/last layer"; these likely want a pure-radial or
  single-layer blow-up, not the Schur-frame chain chart.
- **(B) Fix the chart/decoder.** The off-chain last-drop (`tStar(L−1)=0` at chain index L+1) suggests the
  achiever chain is built one boundary too short, or the decoder should carry a nonzero leaf residual
  (`Rfin ≠ 0`) for the last-layer drop. Re-deriving `phiFlatStructV`/`genBlkFlatStruct` so the last drop is
  represented would make `achieverUfun` non-degenerate — but this re-opens a banked, reviewed construction.
- **(C) pen-and-paper re-cert.** Hand the corrected colPath construction (case-1) + this degeneracy
  (case-2) to pen-and-paper to re-derive the FULL ∀M achiever chart and re-validate EXHAUSTIVELY over
  `{1,2,3}^{L+1}` BEFORE the next Lean tide (the prior cert validated only 4 hand-picked cases and
  mis-modeled the live leaf via a nonzero `Rfin` the actual decoder lacks).

The banked reduction (`UPolyGen_ne_zero_of_witness`, `achieverUbound`, `achieverUfun_eq_eval`,
`Hmat0_eval`, `eval_UPolyGen`, `VvalGen_eq_sqSumHmat0`) is all correct and will consume a corrected
witness for the in-scope M once the scope/chart question is settled.

## Numerics

Exact-arithmetic models + the exhaustive scans are in `scripts/` of this thread (the validated
GenBlk-indexed model matches the cert sympy on `(3,3,1,3)`). The 66-case characterization is rigorous (the
structural `Rmat_interior = 0 ⟹ Hmat 0 = 0` argument above), independently of the numerics.
