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

/-! ## Pieces (b)+(c) — the read-deltas have strict derivative `0`

Both read-deltas equal `forcedDecode(frame)(movedC − C)` (piece (b), the `(★)` read-recovery)
and vanish to second order at the origin (piece (c), the moved-chain germ). -/

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
