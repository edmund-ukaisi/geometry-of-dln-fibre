import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitRawGenMove
import DLNFibre.DLN.RLCT.Validate.DeepestPsiHraw0Gen
import DLNFibre.DLN.RLCT.Validate.DeepestChainUnitGerm
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2

/-!
# `DeepestPsiHderiv0Gen` — `hderiv0` for `psiSplitRawGen` (#120 `hstep2`, Producer 1)

The **general-`L` strict Fréchet derivative at the split origin** of the joint move `psiSplitRawGen`
(`DeepestPsiSplitRawGen`): the deviation `q ↦ psiSplitRawGen q − q` has strict derivative `0` at `0`
(equivalently `D(psiSplitRawGen)(0) = id`). This is the Producer-1 `hderiv0` that the
`DeepestPsiFlatCutGen` cutoff plumbing (`hasStrictFDerivAt_deepestPsiCutRaw_zero`,
`hasStrictFDerivAt_deepestPsiFlatCut`) consumes (the second diffeo-triple component; `hraw0` is
`psiSplitRawGen_zero`).

The general-`L` mirror of the L=2 `hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero`
(`DeepestDiffeoBridgeL2Conj`), routed through the moved-chain `movedC` rather than the L=2 explicit
Schur blocks:

* **(a) payload lens** — `psiSplitRawGen q − q = packed(gaugeΔ q, coreΔ q)` via linearity of
  `regGaugeSlotCLE`/`paramsEquivFlatCLE` + the banked read-backs (`gaugeReadX_psiSplitRawGen`, …);
* **(b) read-recovery** — `gaugeΔ`/`coreΔ` are `forcedDecode(frame)(movedC − C)` (the reads of `q`
  itself recover `decode(C − corM)`, the `(★)` identity read-recovery);
* **(c) degree-2 germ** — `HasStrictFDerivAt (q ↦ movedC(chain(framedParamsPivot q)) − C) 0 0`,
  blockwise via the entry keystones (`hasStrictFDerivAt_matrix_triple_mul_entry_zero`, …): every
  block of `movedC − C` is a product with two factors vanishing at the origin (`(C 0)₂₁ = 0`,
  `(partProd 0)₁₂ = 0`, `blockSchur(corM) = 0`, `wHatAccum(0) = 0`);
* **(d) compose** the strict-deriv-`0` of `gaugeΔ`/`coreΔ` through the fixed CLEs into `hderiv0`.

## Status (WIP)
The target `hasStrictFDerivAt_psiSplitDeltaGen_zero` is **proven modulo two `sorry` sub-lemmas**
(`hasStrictFDerivAt_psiSplitGaugeDeltaGen_zero`,
`hasStrictFDerivAt_paramsEquivFlatCLE_psiSplitCoreDeltaGen_zero`).

Landed + axiom-clean: pieces (a) [`psiSplitDeltaGen_eq_payload`] and (d) [the target's proof], the
pair-mul keystone, and **the whole of piece (c)** —
* value-at-origin collapse (`genChain_zero_*`, `genPartProd_zero_*`, `gen{BlockSchur,Kcoup,SchurTilde,
  VDown,UNorm,NMix}_zero`, `genPartProd_zero_eq_corM`, `genWHatAccum_zero`,
  `genBlockSchurPartProd_sub_wHatAccum_zero`, `gen{DeltaV0,UpEdit,MovedY,MovedZ}_zero`);
* smoothness (`contDiffAt_ringInverse_entry`, `gen{Chain,PartProd,BlockSchur,VDown,UNorm,Kcoup,NMix,
  InvNMix,SchurTilde,InvC11,InvPartProd11,BlockSchurPartProd,UpEdit,MovedY,WHatAccum,HTermLC,DeltaV0,
  MovedZ}_contDiffAt`);
* the four `movedC(C q) Z0edit − C q` germ blocks strict-deriv `0` at the origin
  (`hasStrictFDerivAt_gen{UpEdit,HTermLC,DeltaV0,MovedZsub,MovedTsub}_entry_zero`).

Remaining = **piece (b) only** (bounded recovery plumbing, no math wall): the two `sorry` sub-lemmas.
Each `gaugeΔ`/`coreΔ` entry equals `forcedDecode(frame_s)(movedC − C)`_block, reduced to a piece-(c)
germ block — interior via `deepestChain_framedParamsPivot_blocks_of_frame_one` (needs `Pf s = 1 ∧
Qf s = 1`), boundary via the banked `deepestChain_framedParamsPivot_firstLayer`/`_lastLayer` +
`forcedDecodeLeft/Right_*Frame_mul` (★). The two sub-lemmas + the target will gain the `Pf`/`Qf`
structural hypotheses of `psiSplitRawGen_deepestChain_hmove` (`hL2`, `hQf0`, `hPfL`, `hPunit`, `hQunit`,
`hPtri`, `hP22`, `hQtri`, `hQ22`, `hInterior`).
-/

open Matrix Topology
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## A pair-multiplication strict-derivative keystone

The companion of the banked `hasStrictFDerivAt_matrix_triple_mul_entry_zero`: for a product of TWO
matrix families where BOTH factors vanish (value) at the point, the product entry has strict
derivative `0` (each scalar summand `A i k · B k j` is `f·g` with `f x = g x = 0`, so `D(f·g) x =
f x • g' + g x • f' = 0`). -/

section MatrixEntryDerivGen
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `(A·B)_{ij}` strict-`fderiv`-`0`: BOTH factors `A_{i·}`, `B_{·j}` vanish (value) at `x`. -/
theorem hasStrictFDerivAt_matrix_mul_entry_zero_of_both_zero
    {m n p : Type*} [Fintype n]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X} (i : m) (j : p)
    (hA : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i k) x)
    (hB : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y k j) x)
    (hA0 : ∀ k, A x i k = 0) (hB0 : ∀ k, B x k j = 0) :
    HasStrictFDerivAt (fun y => (A y * B y) i j) (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ k : n, HasStrictFDerivAt (fun y => A y i k * B y k j) (0 : X →L[ℝ] ℝ) x := by
    intro k
    have hAd : HasStrictFDerivAt (fun y => A y i k) (fderiv ℝ (fun y => A y i k) x) x :=
      (hA k).hasStrictFDerivAt (by simp)
    have hBd : HasStrictFDerivAt (fun y => B y k j) (fderiv ℝ (fun y => B y k j) x) x :=
      (hB k).hasStrictFDerivAt (by simp)
    have hm := hAd.mul hBd
    rw [hA0 k, hB0 k] at hm
    simpa using hm
  have hsum := HasStrictFDerivAt.sum (u := (Finset.univ : Finset n)) (fun k _ => hterm k)
  rw [show (fun y => (A y * B y) i j) = ∑ k : n, (fun y => A y i k * B y k j) from by
    funext y; rw [Matrix.mul_apply, Finset.sum_apply]]
  simpa using hsum

end MatrixEntryDerivGen

/-! ## Piece (a) — the payload lens

`psiSplitRawGen q − q` decomposes through the packing CLEs into the read-deltas
`psiSplitGaugeDeltaGen`/`psiSplitCoreDeltaGen` (mirror of `psiSplitDeltaL2CoreConj_eq_payload`). The
deltas are the reads of `psiSplitRawGen q` minus the reads of `q`. -/

/-- The gauge read-delta: `reads(psiSplitRawGen q) − reads(q)` on the reg/gauge slots. -/
noncomputable def psiSplitGaugeDeltaGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) : RegGaugeIdx H r → ℝ :=
  regGaugeSlotEquiv H r hr hL ((psiSplitRawGen H r hr hL J Pf Qf q).1,
      (psiSplitRawGen H r hr hL J Pf Qf q).2.2)
    - regGaugeSlotEquiv H r hr hL (q.1, q.2.2)

/-- The core read-delta: `paramsEquivFlat.symm` reads of `psiSplitRawGen q` minus those of `q`. -/
noncomputable def psiSplitCoreDeltaGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params (deepestM H r) :=
  (paramsEquivFlat (deepestM H r)).symm (psiSplitRawGen H r hr hL J Pf Qf q).2.1
    - (paramsEquivFlat (deepestM H r)).symm q.2.1

/-- The encoded core read-delta is the flat core-slot difference. -/
theorem paramsEquivFlatCLE_psiSplitCoreDeltaGen_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    paramsEquivFlatCLE (deepestM H r) (psiSplitCoreDeltaGen H r hr hL J Pf Qf q)
      = (psiSplitRawGen H r hr hL J Pf Qf q).2.1 - q.2.1 := by
  rw [psiSplitCoreDeltaGen, map_sub, paramsEquivFlatCLE_coe,
    (paramsEquivFlat (deepestM H r)).apply_symm_apply,
    (paramsEquivFlat (deepestM H r)).apply_symm_apply]

/-- **Piece (a): the payload lens.** `psiSplitRawGen q − q` is the packed read-deltas. -/
theorem psiSplitDeltaGen_eq_payload (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    psiSplitRawGen H r hr hL J Pf Qf q - q
      = (((regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)).1,
          (paramsEquivFlatCLE (deepestM H r) (psiSplitCoreDeltaGen H r hr hL J Pf Qf q),
            ((regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)).2)) := by
  have hcore := paramsEquivFlatCLE_psiSplitCoreDeltaGen_eq H r hr hL J Pf Qf q
  have hgg : (regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)
      = ((psiSplitRawGen H r hr hL J Pf Qf q).1, (psiSplitRawGen H r hr hL J Pf Qf q).2.2)
        - (q.1, q.2.2) := by
    rw [psiSplitGaugeDeltaGen, map_sub, regGaugeSlotCLE_symm_coe,
      (regGaugeSlotEquiv H r hr hL).symm_apply_apply,
      (regGaugeSlotEquiv H r hr hL).symm_apply_apply]
  rw [hcore]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [Prod.fst_sub, hgg, Prod.fst_sub]
  · rfl
  · rw [Prod.snd_sub, Prod.snd_sub, hgg, Prod.snd_sub]

/-! ## Piece (c) prep — the base chain at the split origin, and `Ring.inverse` smoothness

At `q = 0` the framed chain is the corner `corM = fromBlocks 1 0 0 0` on every layer `< L`
(`framedParamsPivot_zero_eq_corner` + `deepestChain_corner_eq_corM`), so all the moved-chain data
(`blockSchur`, `Kcoup`, `uNorm`, `vDown`, `nMix`, `wHatAccum`, `deltaV0`, …) collapses. Smoothness
`q` is the banked `contDiff_deepestChain_framedParamsPivot_entry` / `contDiff_partProd_entry`. -/

/-- Entrywise `ContDiffAt` of `Ring.inverse (M q)` where `det ≠ 0` (via `Ring.inverse = (·)⁻¹`). -/
theorem contDiffAt_ringInverse_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : Type*} [Fintype n] [DecidableEq n] {M : X → Matrix n n ℝ} {x : X}
    (hM : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => M y i j) x) (hdet : (M x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Ring.inverse (M y) i j) x := by
  have heq : (fun y => Ring.inverse (M y) i j) = fun y => (M y)⁻¹ i j := by
    funext y; rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [heq]; exact contDiffAt_matrix_inv_entry_of_det_ne_zero_at hM hdet i j

/-- The base chain at the split origin is the corner `corM` on every layer `< L`. -/
theorem genChain_zero_eq_corM (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (k : ℕ) (hk : k < L) :
    deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 :=
  deepestChain_corner_eq_corM H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k hk
    (framedParamsPivot_zero_eq_corner H r hr hL J hJfront Pf Qf k hk)

/-- The base chain's down-block vanishes at the origin (corner for `k < L`, tail otherwise). -/
theorem genChain_zero_toBlocks₂₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₂₁ = 0 := by
  rcases lt_or_ge k L with hk | hk
  · rw [genChain_zero_eq_corM H r hr hL J hJfront Pf Qf k hk]
    exact Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  · exact deepestChain_tail_toBlocks₂₁ H r hr _ k (not_lt.mpr hk)

/-- `(C 0 k)₁₁ = 1` (corner for `k < L`, tail-identity for `k ≥ L`). -/
theorem genChain_zero_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₁₁
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  rcases lt_or_ge k L with hk | hk
  · rw [genChain_zero_eq_corM H r hr hL J hJfront Pf Qf k hk]
    exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _
  · exact deepestChain_tail_toBlocks₁₁ H r hr _ k (not_lt.mpr hk)

/-- `(C 0 k)₁₂ = 0` (corner, `k < L`). -/
theorem genChain_zero_toBlocks₁₂ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L) :
    (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₁₂ = 0 := by
  rw [genChain_zero_eq_corM H r hr hL J hJfront Pf Qf k hk]
  exact Matrix.toBlocks_fromBlocks₁₂ _ _ _ _

/-- `(C 0 k)₂₂ = 0` (corner for `k < L`, tail for `k ≥ L`). -/
theorem genChain_zero_toBlocks₂₂ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₂₂ = 0 := by
  rcases lt_or_ge k L with hk | hk
  · rw [genChain_zero_eq_corM H r hr hL J hJfront Pf Qf k hk]
    exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _
  · exact deepestChain_tail_toBlocks₂₂ H r hr _ k (not_lt.mpr hk)

/-- `(partProd (C 0) k)₁₁ = 1` (`k ≤ L`; induction, the `(C 0 ·)₂₁ = 0` kills the mixed term). -/
theorem genPartProd_zero_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L) :
    (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k).toBlocks₁₁
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  induction k with
  | zero => rw [show partProd _ 0 = 1 from rfl, toBlocks₁₁_one]
  | succ n ih =>
    have hn : n < L := by omega
    rw [show partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (n + 1)
        = partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) n
          * deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) n from rfl,
      toBlocks₁₁_mul, ih (by omega), genChain_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf n,
      genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf n, Matrix.mul_zero, add_zero,
      Matrix.one_mul]

/-- `(partProd (C 0) k)₁₂ = 0` (`k ≤ L`; the corner `(C 0 ·)₁₂ = (C 0 ·)₂₂ = 0`). -/
theorem genPartProd_zero_toBlocks₁₂ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L) :
    (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k).toBlocks₁₂ = 0 := by
  cases k with
  | zero => rw [show partProd _ 0 = 1 from rfl, toBlocks₁₂_one]
  | succ n =>
    have hn : n < L := by omega
    rw [show partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (n + 1)
        = partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) n
          * deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) n from rfl,
      toBlocks₁₂_mul, genChain_zero_toBlocks₁₂ H r hr hL J hJfront Pf Qf n hn,
      genChain_zero_toBlocks₂₂ H r hr hL J hJfront Pf Qf n, Matrix.mul_zero, Matrix.mul_zero,
      add_zero]

/-! ### The moved-chain data collapses at the origin -/

/-- `blockSchur (C 0 k) = 0` (down-block `(C 0 k)₂₁ = 0` kills the correction; `(C 0 k)₂₂ = 0`). -/
theorem genBlockSchur_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k) = 0 := by
  rw [blockSchur, genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf k, Matrix.zero_mul,
    Matrix.zero_mul, sub_zero, genChain_zero_toBlocks₂₂ H r hr hL J hJfront Pf Qf k]

/-- `Kcoup (C 0) k = 0` (the down-block `(C 0 k)₂₁ = 0` is the left factor). -/
theorem genKcoup_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k = 0 := by
  rw [Kcoup, genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf k, Matrix.zero_mul, Matrix.zero_mul]

/-- `schurTilde (C 0) k = 0` (`= (1 − Kcoup)·blockSchur` and `blockSchur = 0`). -/
theorem genSchurTilde_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k = 0 := by
  rw [schurTilde, genBlockSchur_zero H r hr hL J hJfront Pf Qf k, Matrix.mul_zero]

/-- `vDown (C 0) k = 0` (the down-block is the left factor). -/
theorem genVDown_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k = 0 := by
  rw [vDown, genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf k, Matrix.zero_mul]

/-- `uNorm (C 0) k = 0` (`k ≤ L`; the `(partProd)₁₂ = 0` is the right factor). -/
theorem genUNorm_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L) :
    uNorm (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k = 0 := by
  rw [uNorm, genPartProd_zero_toBlocks₁₂ H r hr hL J hJfront Pf Qf k hk, Matrix.mul_zero]

/-- `nMix (C 0) k = 1` (`k ≤ L`; `= 1 + uNorm·vDown` and `uNorm = 0`). -/
theorem genNMix_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L) :
    nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
  rw [nMix, genUNorm_zero H r hr hL J hJfront Pf Qf k hk, Matrix.zero_mul, add_zero]

/-! ### Entrywise `ContDiffAt` of the moved-chain data at the origin

All built from the banked chain/partProd entry smoothness
(`contDiff_deepestChain_framedParamsPivot_entry`, `contDiff_partProd_entry`) via the product/inverse
combinators; the inverses use `det = 1 ≠ 0` at `0`. -/

/-- Chain entries are `ContDiffAt` at `0` (banked global `ContDiff`). -/
theorem genChain_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin r ⊕ Fin (deepestChainWidth H k - r))
    (j : Fin r ⊕ Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k i j) 0 :=
  (contDiff_deepestChain_framedParamsPivot_entry H r hr hL J Pf Qf k i j).contDiffAt

/-- `partProd` entries are `ContDiffAt` at `0`. -/
theorem genPartProd_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin r ⊕ Fin (deepestChainWidth H 0 - r)) (j : Fin r ⊕ Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 :=
  (contDiff_partProd_entry H r hr hL J Pf Qf k i j).contDiffAt

/-- `blockSchur (C q k)` entries are `ContDiffAt` at `0`. -/
theorem genBlockSchur_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q =>
        blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k) i j) 0 := by
  have hCk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q) 0 :=
    genChain_contDiffAt H r hr hL J Pf Qf k
  have hdet :
      ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₁₁).det ≠ 0 := by
    rw [genChain_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf k, Matrix.det_one]; exact one_ne_zero
  have heq : (fun q =>
        blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k) i j)
      = fun q => (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₂ i j
        - ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₁
          * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
          * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂) i j := by
    funext q; rw [blockSchur, Matrix.sub_apply]
  rw [heq]
  refine (hCk (Sum.inr i) (Sum.inr j)).sub ?_
  refine contDiffAt_matrix_mul_entry (fun a b => ?_)
    (fun a b => hCk (Sum.inl a) (Sum.inr b)) i j
  exact contDiffAt_matrix_mul_entry (fun c d => hCk (Sum.inr c) (Sum.inl d))
    (fun c d => contDiffAt_ringInverse_entry (fun p q => hCk (Sum.inl p) (Sum.inl q)) hdet c d) a b

/-- `vDown (C q) k` entries are `ContDiffAt` at `0`. -/
theorem genVDown_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  have hCk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q) 0 :=
    genChain_contDiffAt H r hr hL J Pf Qf k
  have hdet :
      ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₁₁).det ≠ 0 := by
    rw [genChain_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf k, Matrix.det_one]; exact one_ne_zero
  unfold vDown
  exact contDiffAt_matrix_mul_entry (fun a b => hCk (Sum.inr a) (Sum.inl b))
    (fun a b => contDiffAt_ringInverse_entry (fun p q => hCk (Sum.inl p) (Sum.inl q)) hdet a b) i j

/-- `uNorm (C q) k` entries are `ContDiffAt` at `0` (`k ≤ L`, for the `(partProd)₁₁` inverse). -/
theorem genUNorm_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L)
    (i : Fin r) (j : Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => uNorm (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  have hPk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q) 0 :=
    genPartProd_contDiffAt H r hr hL J Pf Qf k
  have hdet : ((partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k).toBlocks₁₁).det
      ≠ 0 := by
    rw [genPartProd_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf k hk, Matrix.det_one]; exact one_ne_zero
  unfold uNorm
  exact contDiffAt_matrix_mul_entry
    (fun a b => contDiffAt_ringInverse_entry (fun p q => hPk (Sum.inl p) (Sum.inl q)) hdet a b)
    (fun a b => hPk (Sum.inl a) (Sum.inr b)) i j

/-- `Kcoup (C q) k` entries are `ContDiffAt` at `0` (`k < L`, for the `(partProd (k+1))₁₁` inverse). -/
theorem genKcoup_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L)
    (i j : Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  have hCk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q) 0 :=
    genChain_contDiffAt H r hr hL J Pf Qf k
  have hPk1 : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) (k + 1) p q) 0 :=
    genPartProd_contDiffAt H r hr hL J Pf Qf (k + 1)
  have hPk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q) 0 :=
    genPartProd_contDiffAt H r hr hL J Pf Qf k
  have hdet :
      ((partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (k + 1)).toBlocks₁₁).det
        ≠ 0 := by
    rw [genPartProd_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf (k + 1) (by omega), Matrix.det_one]
    exact one_ne_zero
  unfold Kcoup
  refine contDiffAt_matrix_mul_entry (fun a b => ?_) (fun a b => hPk (Sum.inl a) (Sum.inr b)) i j
  exact contDiffAt_matrix_mul_entry (fun c d => hCk (Sum.inr c) (Sum.inl d))
    (fun c d => contDiffAt_ringInverse_entry (fun p q => hPk1 (Sum.inl p) (Sum.inl q)) hdet c d) a b

/-- `nMix (C q) k` entries are `ContDiffAt` at `0` (`k ≤ L`). -/
theorem genNMix_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  simp only [nMix, Matrix.add_apply]
  refine contDiffAt_const.add ?_
  exact contDiffAt_matrix_mul_entry (fun a b => genUNorm_contDiffAt H r hr hL J hJfront Pf Qf k hk a b)
    (fun a b => genVDown_contDiffAt H r hr hL J hJfront Pf Qf k a b) i j

/-- `Ring.inverse (nMix (C q) k)` entries are `ContDiffAt` at `0` (`k ≤ L`; `nMix 0 = 1`). -/
theorem genInvNMix_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Ring.inverse (nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) i j)
        0 := by
  have hdet : (nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k).det ≠ 0 := by
    rw [genNMix_zero H r hr hL J hJfront Pf Qf k hk, Matrix.det_one]; exact one_ne_zero
  exact contDiffAt_ringInverse_entry
    (fun p q => genNMix_contDiffAt H r hr hL J hJfront Pf Qf k hk p q) hdet i j

/-- `schurTilde (C q) k` entries are `ContDiffAt` at `0` (`k < L`, through `Kcoup`). -/
theorem genSchurTilde_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  unfold schurTilde
  refine contDiffAt_matrix_mul_entry (fun a b => ?_)
    (fun a b => genBlockSchur_contDiffAt H r hr hL J hJfront Pf Qf k a b) i j
  have hsub : (fun q => ((1 : Matrix (Fin (deepestChainWidth H k - r))
          (Fin (deepestChainWidth H k - r)) ℝ)
        - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) a b)
      = fun q => (1 : Matrix (Fin (deepestChainWidth H k - r))
          (Fin (deepestChainWidth H k - r)) ℝ) a b
        - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k a b := by
    funext q; rw [Matrix.sub_apply]
  rw [hsub]
  exact contDiffAt_const.sub (genKcoup_contDiffAt H r hr hL J hJfront Pf Qf k hk a b)

/-- `Ring.inverse (C q k)₁₁` entries are `ContDiffAt` at `0`. -/
theorem genInvC11_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
        i j) 0 := by
  have hCk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q) 0 :=
    genChain_contDiffAt H r hr hL J Pf Qf k
  have hdet :
      ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) k).toBlocks₁₁).det ≠ 0 := by
    rw [genChain_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf k, Matrix.det_one]; exact one_ne_zero
  exact contDiffAt_ringInverse_entry (fun p q => hCk (Sum.inl p) (Sum.inl q)) hdet i j

/-- `Ring.inverse (partProd (C q) k)₁₁` entries are `ContDiffAt` at `0` (`k ≤ L`). -/
theorem genInvPartProd11_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Ring.inverse
        (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k).toBlocks₁₁ i j) 0 := by
  have hPk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q) 0 :=
    genPartProd_contDiffAt H r hr hL J Pf Qf k
  have hdet : ((partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k).toBlocks₁₁).det
      ≠ 0 := by
    rw [genPartProd_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf k hk, Matrix.det_one]; exact one_ne_zero
  exact contDiffAt_ringInverse_entry (fun p q => hPk (Sum.inl p) (Sum.inl q)) hdet i j

/-- `blockSchur (partProd (C q) k)` entries are `ContDiffAt` at `0` (`k ≤ L`). -/
theorem genBlockSchurPartProd_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L)
    (i : Fin (deepestChainWidth H 0 - r)) (j : Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k)
        i j) 0 := by
  have hPk : ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q) 0 :=
    genPartProd_contDiffAt H r hr hL J Pf Qf k
  have hdet : ((partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k).toBlocks₁₁).det
      ≠ 0 := by
    rw [genPartProd_zero_toBlocks₁₁ H r hr hL J hJfront Pf Qf k hk, Matrix.det_one]; exact one_ne_zero
  have heq : (fun q =>
        blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) i j)
      = fun q => (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k).toBlocks₂₂ i j
        - ((partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k).toBlocks₂₁
          * Ring.inverse (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k).toBlocks₁₁
          * (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k).toBlocks₁₂) i j := by
    funext q; rw [blockSchur, Matrix.sub_apply]
  rw [heq]
  refine (hPk (Sum.inr i) (Sum.inr j)).sub ?_
  refine contDiffAt_matrix_mul_entry (fun a b => ?_) (fun a b => hPk (Sum.inl a) (Sum.inr b)) i j
  exact contDiffAt_matrix_mul_entry (fun c d => hPk (Sum.inr c) (Sum.inl d))
    (fun c d => contDiffAt_ringInverse_entry (fun p q => hPk (Sum.inl p) (Sum.inl q)) hdet c d) a b

/-- `upEdit (C q) k` entries are `ContDiffAt` at `0` (`k < L`). -/
theorem genUpEdit_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L)
    (i : Fin r) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => upEdit (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  unfold upEdit
  refine contDiffAt_matrix_mul_entry (fun a b => ?_) (fun a b => ?_) i j
  · exact contDiffAt_matrix_mul_entry
      (fun c d => genInvNMix_contDiffAt H r hr hL J hJfront Pf Qf k (le_of_lt hk) c d)
      (fun c d => genUNorm_contDiffAt H r hr hL J hJfront Pf Qf k (le_of_lt hk) c d) a b
  · have hsub : (fun q =>
          (blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k)
            - schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) a b)
        = fun q => blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k) a b
          - schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k a b := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    exact (genBlockSchur_contDiffAt H r hr hL J hJfront Pf Qf k a b).sub
      (genSchurTilde_contDiffAt H r hr hL J hJfront Pf Qf k hk a b)

/-- `movedY (C q) k` entries are `ContDiffAt` at `0` (`k < L`). -/
theorem genMovedY_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L)
    (i : Fin r) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  have heq : (fun q => movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j)
      = fun q => (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂ i j
        + upEdit (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j := by
    funext q; rw [movedY, Matrix.add_apply]
  rw [heq]
  exact (genChain_contDiffAt H r hr hL J Pf Qf k (Sum.inl i) (Sum.inr j)).add
    (genUpEdit_contDiffAt H r hr hL J hJfront Pf Qf k hk i j)

/-- `wHatAccum (C q) k` entries are `ContDiffAt` at `0` (`k ≤ L`; induction on the prefix). -/
theorem genWHatAccum_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    ∀ (k : ℕ), k ≤ L → ∀ (i : Fin (deepestChainWidth H 0 - r)) (j : Fin (deepestChainWidth H k - r)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q => wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) 0 := by
  intro k
  induction k with
  | zero =>
    intro _ i j
    have heq : (fun q => wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) 0 i j)
        = fun _ => (1 : Matrix (Fin (deepestChainWidth H 0 - r))
            (Fin (deepestChainWidth H 0 - r)) ℝ) i j := rfl
    rw [heq]; exact contDiffAt_const
  | succ n ih =>
    intro hk i j
    have hn : n < L := by omega
    have heq : (fun q => wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (n + 1) i j)
        = fun q => (wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n
            * ((1 : Matrix (Fin (deepestChainWidth H n - r)) (Fin (deepestChainWidth H n - r)) ℝ)
              - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n)
            * schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n) i j := rfl
    rw [heq]
    refine contDiffAt_matrix_mul_entry (fun a b => ?_)
      (fun a b => genSchurTilde_contDiffAt H r hr hL J hJfront Pf Qf n hn a b) i j
    refine contDiffAt_matrix_mul_entry (fun c d => ih (by omega) c d) (fun c d => ?_) a b
    have hsub : (fun q => ((1 : Matrix (Fin (deepestChainWidth H n - r))
            (Fin (deepestChainWidth H n - r)) ℝ)
          - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n) c d)
        = fun q => (1 : Matrix (Fin (deepestChainWidth H n - r))
            (Fin (deepestChainWidth H n - r)) ℝ) c d
          - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n c d := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    exact contDiffAt_const.sub (genKcoup_contDiffAt H r hr hL J hJfront Pf Qf n hn c d)

/-- `hTermLC (C q) j` entries are `ContDiffAt` at `0` (`j < L`). -/
theorem genHTermLC_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (j : ℕ) (hj : j < L)
    (i : Fin (deepestChainWidth H 0 - r)) (b : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => hTermLC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j i b) 0 := by
  unfold hTermLC
  refine contDiffAt_matrix_mul_entry (fun a c => ?_)
    (fun a c => genInvPartProd11_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) a c) i b
  refine contDiffAt_matrix_mul_entry (fun a' c' => ?_)
    (fun a' c' => genInvNMix_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) a' c') a c
  refine contDiffAt_matrix_mul_entry (fun a'' c'' => ?_)
    (fun a'' c'' => genVDown_contDiffAt H r hr hL J hJfront Pf Qf j a'' c'') a' c'
  have hsub : (fun q =>
        (blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
          - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j) a'' c'')
      = fun q =>
        blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j) a'' c''
        - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j a'' c'' := by
    funext q; rw [Matrix.sub_apply]
  rw [hsub]
  exact (genBlockSchurPartProd_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) a'' c'').sub
    (genWHatAccum_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) a'' c'')

/-- `deltaV0 (C q) L` entries are `ContDiffAt` at `0`. -/
theorem genDeltaV0_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (i : Fin (deepestChainWidth H 0 - r)) (b : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L i b) 0 := by
  have heq : (fun q => deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L i b)
      = fun q => ∑ j ∈ Finset.range L,
          hTermLC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j i b := by
    funext q; rw [deltaV0, Matrix.sum_apply]
  rw [heq]
  exact ContDiffAt.sum (fun j hj =>
    genHTermLC_contDiffAt H r hr hL J hJfront Pf Qf j (Finset.mem_range.mp hj) i b)

/-- `movedZ (C q) (Z0edit0 (C q) L) k` entries are `ContDiffAt` at `0`. -/
theorem genMovedZ_contDiffAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin (deepestChainWidth H k - r)) (b : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
        (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k i b) 0 := by
  cases k with
  | zero =>
    have heq : (fun q => movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) 0 i b)
        = fun q => (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₂₁ i b
          + (deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L
            * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₁₁) i b := by
      funext q
      show (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) i b = _
      rw [Z0edit0, Matrix.add_apply]
    rw [heq]
    exact (genChain_contDiffAt H r hr hL J Pf Qf 0 (Sum.inr i) (Sum.inl b)).add
      (contDiffAt_matrix_mul_entry (fun a c => genDeltaV0_contDiffAt H r hr hL J hJfront Pf Qf a c)
        (fun a c => genChain_contDiffAt H r hr hL J Pf Qf 0 (Sum.inl a) (Sum.inl c)) i b)
  | succ n =>
    have heq : (fun q => movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) (n + 1) i b)
        = fun q =>
          (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (n + 1)).toBlocks₂₁ i b := rfl
    rw [heq]; exact genChain_contDiffAt H r hr hL J Pf Qf (n + 1) (Sum.inr i) (Sum.inl b)

/-! ### Value lemmas for the `hTermLC` germ (the `(blockSchur(partProd) − wHatAccum)` factor) -/

/-- `partProd (C 0) (m+1) = corM` (`m + 1 ≤ L`; each factor is `corM`, and `corM · corM = corM`). -/
theorem genPartProd_zero_eq_corM (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    ∀ (m : ℕ), m + 1 ≤ L →
      partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (m + 1)
        = Matrix.fromBlocks 1 0 0 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [show partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) 1
        = partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) 0
          * deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) 0 from rfl,
      show partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) 0 = 1 from rfl,
      Matrix.one_mul, genChain_zero_eq_corM H r hr hL J hJfront Pf Qf 0 (by omega)]
  | succ n ih =>
    intro hm
    rw [show partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (n + 1 + 1)
        = partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (n + 1)
          * deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0) (n + 1) from rfl,
      ih (by omega), genChain_zero_eq_corM H r hr hL J hJfront Pf Qf (n + 1) (by omega),
      Matrix.fromBlocks_multiply]
    simp

/-- `wHatAccum (C 0) (m+1) = 0` (`schurTilde (C 0) · = 0` is the right factor). -/
theorem genWHatAccum_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (m : ℕ) :
    wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (m + 1) = 0 := by
  rw [show wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) (m + 1)
      = wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) m
        * (1 - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) m)
        * schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) m from rfl,
    genSchurTilde_zero H r hr hL J hJfront Pf Qf m, Matrix.mul_zero]

/-- `blockSchur (partProd (C 0) j) − wHatAccum (C 0) j = 0` (`j ≤ L`): `j = 0` both are `1`; `j ≥ 1`
both are `0`. The `(bS(partProd) − Ŵ)` factor of `hTermLC` vanishes at the origin. -/
theorem genBlockSchurPartProd_sub_wHatAccum_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (j : ℕ) (hj : j ≤ L) :
    blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j = 0 := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [blockSchur_partProd_zero,
      show wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) 0 = 1 from rfl,
      sub_self]
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [genWHatAccum_zero H r hr hL J hJfront Pf Qf m, sub_zero,
      genPartProd_zero_eq_corM H r hr hL J hJfront Pf Qf m (by omega), blockSchur,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.zero_mul, Matrix.zero_mul,
      sub_zero]

/-- `deltaV0 (C 0) L = 0` (each `hTermLC` summand has the `vDown (C 0) · = 0` factor). -/
theorem genDeltaV0_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) L = 0 := by
  rw [deltaV0]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [hTermLC, genVDown_zero H r hr hL J hJfront Pf Qf j, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.zero_mul]

/-- `upEdit (C 0) k = 0` (`k ≤ L`; the `uNorm (C 0) = 0` factor). -/
theorem genUpEdit_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k ≤ L) :
    upEdit (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k = 0 := by
  rw [upEdit, genUNorm_zero H r hr hL J hJfront Pf Qf k hk, Matrix.mul_zero, Matrix.zero_mul]

/-- `movedY (C 0) k = 0` (`k < L`; `(C 0 k)₁₂ = 0` and `upEdit (C 0) k = 0`). -/
theorem genMovedY_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L) :
    movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) k = 0 := by
  rw [movedY, genChain_zero_toBlocks₁₂ H r hr hL J hJfront Pf Qf k hk,
    genUpEdit_zero H r hr hL J hJfront Pf Qf k (le_of_lt hk), add_zero]

/-- `movedZ (C 0) (Z0edit0 (C 0) L) k = 0` (`(C 0)₂₁ = 0` and `deltaV0 (C 0) = 0`). -/
theorem genMovedZ_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) :
    movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0))
      (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) L) k = 0 := by
  cases k with
  | zero =>
    show Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) L = 0
    rw [Z0edit0, genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf 0,
      genDeltaV0_zero H r hr hL J hJfront Pf Qf, Matrix.zero_mul, add_zero]
  | succ n => exact genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf (n + 1)

/-! ## Pieces (b)+(c) — the read-deltas have strict derivative `0`

Both read-deltas equal `forcedDecode(frame)(movedC − C)` (piece (b), the `(★)` read-recovery)
and vanish to second order at the origin (piece (c), the moved-chain germ). -/

/-- **(c) germ, ₁₂ block.** `upEdit (C q) k` entries have strict derivative `0` (`k < L`): the product
`(inv(nMix)·uNorm)·(blockSchur − schurTilde)` has both factors vanishing at the origin. -/
theorem hasStrictFDerivAt_genUpEdit_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L)
    (i : Fin r) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    HasStrictFDerivAt
      (fun q => upEdit (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  unfold upEdit
  refine hasStrictFDerivAt_matrix_mul_entry_zero_of_both_zero i j (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)
  · exact contDiffAt_matrix_mul_entry
      (fun d e => genInvNMix_contDiffAt H r hr hL J hJfront Pf Qf k (le_of_lt hk) d e)
      (fun d e => genUNorm_contDiffAt H r hr hL J hJfront Pf Qf k (le_of_lt hk) d e) i c
  · exact (genBlockSchur_contDiffAt H r hr hL J hJfront Pf Qf k c j).sub
      (genSchurTilde_contDiffAt H r hr hL J hJfront Pf Qf k hk c j)
  · rw [genUNorm_zero H r hr hL J hJfront Pf Qf k (le_of_lt hk), Matrix.mul_zero, Matrix.zero_apply]
  · rw [genBlockSchur_zero H r hr hL J hJfront Pf Qf k,
      genSchurTilde_zero H r hr hL J hJfront Pf Qf k, sub_self, Matrix.zero_apply]

/-- **(c) germ, `hTermLC` summand.** `hTermLC (C q) j` entries have strict derivative `0` (`j < L`):
`(bS(partProd) − Ŵ)·vDown·inv(nMix)·inv(partProd₁₁)` has its two left factors vanishing. -/
theorem hasStrictFDerivAt_genHTermLC_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (j : ℕ) (hj : j < L)
    (i : Fin (deepestChainWidth H 0 - r)) (b : Fin r) :
    HasStrictFDerivAt
      (fun q => hTermLC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j i b)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have hA0 : blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j = 0 :=
    genBlockSchurPartProd_sub_wHatAccum_zero H r hr hL J hJfront Pf Qf j (le_of_lt hj)
  have hAB0 : (blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      * vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j = 0 := by
    rw [hA0, Matrix.zero_mul]
  have hABC0 : ((blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      * vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j)
      * Ring.inverse (nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf 0)) j) = 0 := by
    rw [hAB0, Matrix.zero_mul]
  have hAB : ∀ (d : Fin r), HasStrictFDerivAt
      (fun q => ((blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
          - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
        * vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j) i d)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := fun d =>
    hasStrictFDerivAt_matrix_mul_entry_zero_of_both_zero i d
      (fun e => (genBlockSchurPartProd_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) i e).sub
        (genWHatAccum_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) i e))
      (fun e => genVDown_contDiffAt H r hr hL J hJfront Pf Qf j e d)
      (fun e => by rw [hA0, Matrix.zero_apply])
      (fun e => by rw [genVDown_zero H r hr hL J hJfront Pf Qf j, Matrix.zero_apply])
  have hABC : ∀ (c : Fin r), HasStrictFDerivAt
      (fun q => (((blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
            - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
          * vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
        * Ring.inverse (nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)) i c)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := fun c =>
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i c hAB
      (fun d => by rw [hAB0, Matrix.zero_apply])
      (fun d => genInvNMix_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) d c)
  unfold hTermLC
  exact hasStrictFDerivAt_matrix_mul_entry_of_left_zero i b hABC
    (fun c => by rw [hABC0, Matrix.zero_apply])
    (fun c => genInvPartProd11_contDiffAt H r hr hL J hJfront Pf Qf j (le_of_lt hj) c b)

/-- **(c) germ, `deltaV0`.** `deltaV0 (C q) L` entries have strict derivative `0` (a finite sum of
the `hTermLC` germs). -/
theorem hasStrictFDerivAt_genDeltaV0_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (i : Fin (deepestChainWidth H 0 - r)) (b : Fin r) :
    HasStrictFDerivAt
      (fun q => deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L i b)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L i b)
      = ∑ j ∈ Finset.range L,
          (fun q => hTermLC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j i b) := by
    funext q; rw [deltaV0, Matrix.sum_apply, Finset.sum_apply]
  rw [heq]
  have hsum := HasStrictFDerivAt.sum (u := Finset.range L) (fun j hj =>
    hasStrictFDerivAt_genHTermLC_entry_zero H r hr hL J hJfront Pf Qf j (Finset.mem_range.mp hj) i b)
  simpa using hsum

/-- **(c) germ, ₂₁ block.** `(movedZ (C q) (Z0edit0 …) k − (C q k)₂₁)` entries have strict derivative
`0`: at `k = 0` it is `deltaV0 · (C 0)₁₁` (the `deltaV0` germ), and it is `0` at `k ≥ 1`. -/
theorem hasStrictFDerivAt_genMovedZsub_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (i : Fin (deepestChainWidth H k - r)) (b : Fin r) :
    HasStrictFDerivAt (fun q => (movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₁) i b)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  cases k with
  | zero =>
    have heq : (fun q => (movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
            (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) 0
          - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₂₁) i b)
        = fun q => (deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L
            * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₁₁) i b := by
      funext q
      show ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₂₁
          + deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L
            * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₁₁
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₂₁) i b = _
      rw [add_sub_cancel_left]
    rw [heq]
    exact hasStrictFDerivAt_matrix_mul_entry_of_left_zero i b
      (fun c => hasStrictFDerivAt_genDeltaV0_entry_zero H r hr hL J hJfront Pf Qf i c)
      (fun c => by rw [genDeltaV0_zero H r hr hL J hJfront Pf Qf, Matrix.zero_apply])
      (fun c => genChain_contDiffAt H r hr hL J Pf Qf 0 (Sum.inl c) (Sum.inl b))
  | succ n =>
    have heq : (fun q => (movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
            (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) (n + 1)
          - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (n + 1)).toBlocks₂₁) i b)
        = fun _ => (0 : ℝ) := by
      funext q
      show ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (n + 1)).toBlocks₂₁
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (n + 1)).toBlocks₂₁) i b = _
      rw [sub_self, Matrix.zero_apply]
    rw [heq]; exact hasStrictFDerivAt_const _ _

/-- **(c) germ, ₂₂ block.** `(movedT (C q) (Z0edit0 …) k − (C q k)₂₂)` entries have strict derivative
`0` (`k < L`): via `movedT − (C)₂₂ = movedZ·inv·movedY − Kcoup·blockSchur − (C)₂₁·inv·(C)₁₂`, each
summand a product with vanishing outer/paired factors. -/
theorem hasStrictFDerivAt_genMovedTsub_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ) (hk : k < L)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    HasStrictFDerivAt (fun q => (movedT (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₂) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have hid : ∀ q, movedT (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₂
      = movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
            (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
          * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
          * movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k
        - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k
          * blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k)
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₁
          * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
          * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂ := by
    intro q
    have hC22 : (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₂
        = blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k)
          + (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₁
            * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
            * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂ := by
      rw [blockSchur]; abel
    rw [movedT, schurTilde, hC22, Matrix.sub_mul, Matrix.one_mul]; abel
  have heq : (fun q => (movedT (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
        - (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₂) i j)
      = fun q => (movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
              (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
            * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
            * movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) i j
          - (Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k
            * blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k)) i j
          - ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₁
            * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
            * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂) i j := by
    funext q; rw [hid q, Matrix.sub_apply, Matrix.sub_apply]
  rw [heq]
  have ha : HasStrictFDerivAt (fun q => (movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
        * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
        * movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_triple_mul_entry_zero i j
      (fun a b => genMovedZ_contDiffAt H r hr hL J hJfront Pf Qf k a b)
      (fun a b => genInvC11_contDiffAt H r hr hL J hJfront Pf Qf k a b)
      (fun a b => genMovedY_contDiffAt H r hr hL J hJfront Pf Qf k hk a b)
      (fun a b => by rw [genMovedZ_zero H r hr hL J hJfront Pf Qf k, Matrix.zero_apply])
      (fun a b => by rw [genMovedY_zero H r hr hL J hJfront Pf Qf k hk, Matrix.zero_apply])
  have hb : HasStrictFDerivAt (fun q => (Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k
        * blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k)) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_zero_of_both_zero i j
      (fun c => genKcoup_contDiffAt H r hr hL J hJfront Pf Qf k hk i c)
      (fun c => genBlockSchur_contDiffAt H r hr hL J hJfront Pf Qf k c j)
      (fun c => by rw [genKcoup_zero H r hr hL J hJfront Pf Qf k, Matrix.zero_apply])
      (fun c => by rw [genBlockSchur_zero H r hr hL J hJfront Pf Qf k, Matrix.zero_apply])
  have hc : HasStrictFDerivAt (fun q => ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₂₁
        * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
        * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_triple_mul_entry_zero i j
      (fun a b => genChain_contDiffAt H r hr hL J Pf Qf k (Sum.inr a) (Sum.inl b))
      (fun a b => genInvC11_contDiffAt H r hr hL J hJfront Pf Qf k a b)
      (fun a b => genChain_contDiffAt H r hr hL J Pf Qf k (Sum.inl a) (Sum.inr b))
      (fun a b => by rw [genChain_zero_toBlocks₂₁ H r hr hL J hJfront Pf Qf k, Matrix.zero_apply])
      (fun a b => by rw [genChain_zero_toBlocks₁₂ H r hr hL J hJfront Pf Qf k hk, Matrix.zero_apply])
  simpa using (ha.sub hb).sub hc

/-- **Pieces (b)+(c), gauge slot.** The gauge read-delta has strict derivative `0` at the origin. -/
theorem hasStrictFDerivAt_psiSplitGaugeDeltaGen_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    HasStrictFDerivAt (psiSplitGaugeDeltaGen H r hr hL J Pf Qf)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (RegGaugeIdx H r → ℝ)) 0 := by
  sorry

/-- **Pieces (b)+(c) for the core slot.** The encoded core read-delta has strict derivative `0`. -/
theorem hasStrictFDerivAt_paramsEquivFlatCLE_psiSplitCoreDeltaGen_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    HasStrictFDerivAt
      (fun q => paramsEquivFlatCLE (deepestM H r) (psiSplitCoreDeltaGen H r hr hL J Pf Qf q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  sorry

/-! ## The target -/

/-- **`hderiv0` — the general-`L` strict Fréchet derivative of the joint move at the split origin.**
The deviation `q ↦ psiSplitRawGen q − q` has strict derivative `0` at `0`. Piece (d): the payload
lens decomposes the delta into the two read-deltas, each with strict derivative `0`; compose through
the fixed packing CLEs (`regGaugeSlotCLE.symm`, `paramsEquivFlatCLE`) and `prodMk`. -/
theorem hasStrictFDerivAt_psiSplitDeltaGen_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    HasStrictFDerivAt (fun q => psiSplitRawGen H r hr hL J Pf Qf q - q)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
  have heq : (fun q => psiSplitRawGen H r hr hL J Pf Qf q - q)
      = fun q => (((regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)).1,
          (paramsEquivFlatCLE (deepestM H r) (psiSplitCoreDeltaGen H r hr hL J Pf Qf q),
            ((regGaugeSlotCLE H r hr hL).symm
              (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)).2)) := by
    funext q; exact psiSplitDeltaGen_eq_payload H r hr hL J Pf Qf q
  rw [heq]
  have hrg : HasStrictFDerivAt
      (fun q => (regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
        ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))) 0 := by
    have hcle := ((regGaugeSlotCLE H r hr hL).symm.toContinuousLinearMap).hasStrictFDerivAt
      (x := psiSplitGaugeDeltaGen H r hr hL J Pf Qf 0)
    have hcomp := hcle.comp 0
      (hasStrictFDerivAt_psiSplitGaugeDeltaGen_zero H r hr hL J hJfront Pf Qf)
    simpa using hcomp
  have hcore := hasStrictFDerivAt_paramsEquivFlatCLE_psiSplitCoreDeltaGen_zero H r hr hL J hJfront
    Pf Qf
  have h1 : HasStrictFDerivAt
      (fun q => ((regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)).1)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
    have := (ContinuousLinearMap.fst ℝ (Fin (deepestNReg H r) → ℝ)
      (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp 0 hrg
    simpa using this
  have h3 : HasStrictFDerivAt
      (fun q => ((regGaugeSlotCLE H r hr hL).symm (psiSplitGaugeDeltaGen H r hr hL J Pf Qf q)).2)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (ContinuousLinearMap.snd ℝ (Fin (deepestNReg H r) → ℝ)
      (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp 0 hrg
    simpa using this
  exact h1.prodMk (hcore.prodMk h3)

end DLNFibre.DLN.RLCT
