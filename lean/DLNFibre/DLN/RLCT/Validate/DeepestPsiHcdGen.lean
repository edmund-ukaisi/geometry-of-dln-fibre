import DLNFibre.DLN.RLCT.Validate.DeepestPsiHderiv0Gen

/-!
# `DeepestPsiHcdGen` — `hcd` for `psiSplitRawGen` (#120 `hstep2`, Producer 1, leaf 3/3)

The **general-`L` smoothness leaf** of the Producer-1 diffeo triple: the deviation
`q ↦ psiSplitRawGen q − q` is `ContDiffAt ℝ ⊤` at every point of a bump support around the split
origin — the `hcd` input `contDiff_deepestPsiFlatCut` (`DeepestPsiFlatCutGen`) consumes for
`deepest_diffeo_bridge_gen_assembled`. Complements `hraw0` (`psiSplitRawGen_zero`) and `hderiv0`
(`hasStrictFDerivAt_psiSplitDeltaGen_zero`).

Unlike `hderiv0`'s banked entry smoothness — which holds only **at the origin** (its `hdet` inputs
are discharged by "value-at-0 = identity, det 1 ≠ 0") — `hcd` needs the smoothness at a **general**
point `q₀` in a neighbourhood of `0`. This module rebuilds the smoothness ladder at general `q₀`,
carrying the invertibility bundle `psiInvBundle` (chain-corner / partProd-corner / pivot-mix dets
nonzero at `q₀`, all `= 1` at the origin), then:

* **(i)** general-`q` twins of the 18 entry lemmas (`gen*_contDiffAt_at`), each a transcription of
  the banked at-`0` lemma with `0 → q₀` and `hdet` from the bundle; the chain/partProd entries are
  globally `ContDiff` so their twins are free;
* **(ii)** the top-level assembly `psiTargetD → forcedDecode → psiReadBlk → psiSplitRawGen` at
  general `q₀` (never built, even at `0`);
* **(iii)** the invertibility region is a neighbourhood of `0` (dets continuous, `= 1` at `0`), and a
  bump with support in it discharges the consumer's `∀ q ∈ tsupport χ` shape.

No `sorry` / `axiom` / `native_decide`.
-/

open Matrix Topology
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## The invertibility bundle at a general split point -/

/-- **The invertibility bundle at `q₀`.** The chain-corner `(C q₀ k)₁₁`, the partial-product corner
`(partProd (C q₀) k)₁₁`, and the pivot-mix `nMix (C q₀) k` all have nonzero determinant, for every
`k`. All three are `1` at the split origin (`genChain_zero_toBlocks₁₁`, `genPartProd_zero_toBlocks₁₁`,
`genNMix_zero`), so the bundle holds at `0` and — by continuity — on a neighbourhood of it. This is
the general-`q` replacement for `hderiv0`'s per-lemma "det = 1 at `0`" facts. -/
def psiInvBundle (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₀ : DeepestSplit H r (deepestNGauge H r)) : Prop :=
  (∀ k, ((deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q₀) k).toBlocks₁₁).det ≠ 0)
  ∧ (∀ k, ((partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q₀)) k).toBlocks₁₁).det
      ≠ 0)
  ∧ (∀ k, (nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q₀)) k).det ≠ 0)

/-! ## (i) General-`q` twins of the entry smoothness lemmas

Each mirrors the banked at-`0` lemma in `DeepestPsiHderiv0Gen`, with `0 → q₀` and the `hdet` input
supplied by the bundle. The chain/partProd entries are globally `ContDiff`, so their twins specialise
the global lemma at `q₀`. -/

/-- Chain entries are `ContDiffAt` at any `q₀` (global `ContDiff`). -/
theorem genChain_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (i : Fin r ⊕ Fin (deepestChainWidth H k - r))
    (j : Fin r ⊕ Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k i j) q₀ :=
  (contDiff_deepestChain_framedParamsPivot_entry H r hr hL J Pf Qf k i j).contDiffAt

/-- `partProd` entries are `ContDiffAt` at any `q₀` (global `ContDiff`). -/
theorem genPartProd_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (i : Fin r ⊕ Fin (deepestChainWidth H 0 - r)) (j : Fin r ⊕ Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ :=
  (contDiff_partProd_entry H r hr hL J Pf Qf k i j).contDiffAt

/-- `blockSchur (C q k)` entries are `ContDiffAt` at `q₀` (bundle: `(C q₀ k)₁₁` det `≠ 0`). -/
theorem genBlockSchur_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k) i j) q₀ := by
  have hCk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q') q₀ :=
    fun p q' => genChain_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.1 k
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

/-- `vDown (C q) k` entries are `ContDiffAt` at `q₀` (bundle: `(C q₀ k)₁₁` det `≠ 0`). -/
theorem genVDown_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => vDown (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  have hCk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q') q₀ :=
    fun p q' => genChain_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.1 k
  unfold vDown
  exact contDiffAt_matrix_mul_entry (fun a b => hCk (Sum.inr a) (Sum.inl b))
    (fun a b => contDiffAt_ringInverse_entry (fun p q => hCk (Sum.inl p) (Sum.inl q)) hdet a b) i j

/-- `uNorm (C q) k` entries are `ContDiffAt` at `q₀` (bundle: `(partProd q₀ k)₁₁` det `≠ 0`). -/
theorem genUNorm_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin r) (j : Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => uNorm (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  have hPk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q') q₀ :=
    fun p q' => genPartProd_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.2.1 k
  unfold uNorm
  exact contDiffAt_matrix_mul_entry
    (fun a b => contDiffAt_ringInverse_entry (fun p q => hPk (Sum.inl p) (Sum.inl q)) hdet a b)
    (fun a b => hPk (Sum.inl a) (Sum.inr b)) i j

/-- `Kcoup (C q) k` entries are `ContDiffAt` at `q₀` (bundle: `(partProd q₀ (k+1))₁₁` det `≠ 0`). -/
theorem genKcoup_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i j : Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  have hCk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q') q₀ :=
    fun p q' => genChain_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hPk1 : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) (k + 1) p q') q₀ :=
    fun p q' => genPartProd_contDiffAt_at H r hr hL J Pf Qf (k + 1) q₀ p q'
  have hPk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q') q₀ :=
    fun p q' => genPartProd_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.2.1 (k + 1)
  unfold Kcoup
  refine contDiffAt_matrix_mul_entry (fun a b => ?_) (fun a b => hPk (Sum.inl a) (Sum.inr b)) i j
  exact contDiffAt_matrix_mul_entry (fun c d => hCk (Sum.inr c) (Sum.inl d))
    (fun c d => contDiffAt_ringInverse_entry (fun p q => hPk1 (Sum.inl p) (Sum.inl q)) hdet c d) a b

/-- `nMix (C q) k` entries are `ContDiffAt` at `q₀`. -/
theorem genNMix_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  simp only [nMix, Matrix.add_apply]
  refine contDiffAt_const.add ?_
  exact contDiffAt_matrix_mul_entry
    (fun a b => genUNorm_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b)
    (fun a b => genVDown_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b) i j

/-- `Ring.inverse (nMix (C q) k)` entries are `ContDiffAt` at `q₀` (bundle: `nMix q₀ k` det `≠ 0`). -/
theorem genInvNMix_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Ring.inverse (nMix (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) i j)
        q₀ := by
  have hdet := hq₀.2.2 k
  exact contDiffAt_ringInverse_entry
    (fun p q => genNMix_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ p q) hdet i j

/-- `schurTilde (C q) k` entries are `ContDiffAt` at `q₀`. -/
theorem genSchurTilde_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  unfold schurTilde
  refine contDiffAt_matrix_mul_entry (fun a b => ?_)
    (fun a b => genBlockSchur_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b) i j
  have hsub : (fun q => ((1 : Matrix (Fin (deepestChainWidth H k - r))
          (Fin (deepestChainWidth H k - r)) ℝ)
        - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) a b)
      = fun q => (1 : Matrix (Fin (deepestChainWidth H k - r))
          (Fin (deepestChainWidth H k - r)) ℝ) a b
        - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k a b := by
    funext q; rw [Matrix.sub_apply]
  rw [hsub]
  exact contDiffAt_const.sub (genKcoup_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b)

/-- `Ring.inverse (C q k)₁₁` entries are `ContDiffAt` at `q₀` (bundle: `(C q₀ k)₁₁` det `≠ 0`). -/
theorem genInvC11_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
        i j) q₀ := by
  have hCk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x) k p q') q₀ :=
    fun p q' => genChain_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.1 k
  exact contDiffAt_ringInverse_entry (fun p q => hCk (Sum.inl p) (Sum.inl q)) hdet i j

/-- `Ring.inverse (partProd (C q) k)₁₁` entries are `ContDiffAt` at `q₀`
(bundle: `(partProd q₀ k)₁₁` det `≠ 0`). -/
theorem genInvPartProd11_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => Ring.inverse
        (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k).toBlocks₁₁ i j)
        q₀ := by
  have hPk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q') q₀ :=
    fun p q' => genPartProd_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.2.1 k
  exact contDiffAt_ringInverse_entry (fun p q => hPk (Sum.inl p) (Sum.inl q)) hdet i j

/-- `blockSchur (partProd (C q) k)` entries are `ContDiffAt` at `q₀`
(bundle: `(partProd q₀ k)₁₁` det `≠ 0`). -/
theorem genBlockSchurPartProd_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H 0 - r)) (j : Fin (deepestChainWidth H k - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k)
        i j) q₀ := by
  have hPk : ∀ p q', ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf x)) k p q') q₀ :=
    fun p q' => genPartProd_contDiffAt_at H r hr hL J Pf Qf k q₀ p q'
  have hdet := hq₀.2.1 k
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

/-- `upEdit (C q) k` entries are `ContDiffAt` at `q₀`. -/
theorem genUpEdit_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin r) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => upEdit (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  unfold upEdit
  refine contDiffAt_matrix_mul_entry (fun a b => ?_) (fun a b => ?_) i j
  · exact contDiffAt_matrix_mul_entry
      (fun c d => genInvNMix_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ c d)
      (fun c d => genUNorm_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ c d) a b
  · have hsub : (fun q =>
          (blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k)
            - schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) a b)
        = fun q => blockSchur (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k) a b
          - schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k a b := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    exact (genBlockSchur_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b).sub
      (genSchurTilde_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b)

/-- `movedY (C q) k` entries are `ContDiffAt` at `q₀`. -/
theorem genMovedY_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin r) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  have heq : (fun q => movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j)
      = fun q => (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₂ i j
        + upEdit (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j := by
    funext q; rw [movedY, Matrix.add_apply]
  rw [heq]
  exact (genChain_contDiffAt_at H r hr hL J Pf Qf k q₀ (Sum.inl i) (Sum.inr j)).add
    (genUpEdit_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ i j)

/-- `wHatAccum (C q) k` entries are `ContDiffAt` at `q₀` (induction on the prefix). -/
theorem genWHatAccum_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀) :
    ∀ (k : ℕ) (i : Fin (deepestChainWidth H 0 - r)) (j : Fin (deepestChainWidth H k - r)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q => wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j) q₀ := by
  intro k
  induction k with
  | zero =>
    intro i j
    have heq : (fun q => wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) 0 i j)
        = fun _ => (1 : Matrix (Fin (deepestChainWidth H 0 - r))
            (Fin (deepestChainWidth H 0 - r)) ℝ) i j := rfl
    rw [heq]; exact contDiffAt_const
  | succ n ih =>
    intro i j
    have heq : (fun q => wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (n + 1) i j)
        = fun q => (wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n
            * ((1 : Matrix (Fin (deepestChainWidth H n - r)) (Fin (deepestChainWidth H n - r)) ℝ)
              - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n)
            * schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n) i j := rfl
    rw [heq]
    refine contDiffAt_matrix_mul_entry (fun a b => ?_)
      (fun a b => genSchurTilde_contDiffAt_at H r hr hL J Pf Qf n q₀ hq₀ a b) i j
    refine contDiffAt_matrix_mul_entry (fun c d => ih c d) (fun c d => ?_) a b
    have hsub : (fun q => ((1 : Matrix (Fin (deepestChainWidth H n - r))
            (Fin (deepestChainWidth H n - r)) ℝ)
          - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n) c d)
        = fun q => (1 : Matrix (Fin (deepestChainWidth H n - r))
            (Fin (deepestChainWidth H n - r)) ℝ) c d
          - Kcoup (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) n c d := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    exact contDiffAt_const.sub (genKcoup_contDiffAt_at H r hr hL J Pf Qf n q₀ hq₀ c d)

/-- `hTermLC (C q) j` entries are `ContDiffAt` at `q₀`. -/
theorem genHTermLC_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (j : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H 0 - r)) (b : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => hTermLC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j i b) q₀ := by
  unfold hTermLC
  refine contDiffAt_matrix_mul_entry (fun a c => ?_)
    (fun a c => genInvPartProd11_contDiffAt_at H r hr hL J Pf Qf j q₀ hq₀ a c) i b
  refine contDiffAt_matrix_mul_entry (fun a' c' => ?_)
    (fun a' c' => genInvNMix_contDiffAt_at H r hr hL J Pf Qf j q₀ hq₀ a' c') a c
  refine contDiffAt_matrix_mul_entry (fun a'' c'' => ?_)
    (fun a'' c'' => genVDown_contDiffAt_at H r hr hL J Pf Qf j q₀ hq₀ a'' c'') a' c'
  have hsub : (fun q =>
        (blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j)
          - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j) a'' c'')
      = fun q =>
        blockSchur (partProd (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j) a'' c''
        - wHatAccum (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j a'' c'' := by
    funext q; rw [Matrix.sub_apply]
  rw [hsub]
  exact (genBlockSchurPartProd_contDiffAt_at H r hr hL J Pf Qf j q₀ hq₀ a'' c'').sub
    (genWHatAccum_contDiffAt_at H r hr hL J Pf Qf q₀ hq₀ j a'' c'')

/-- `deltaV0 (C q) L` entries are `ContDiffAt` at `q₀`. -/
theorem genDeltaV0_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H 0 - r)) (b : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L i b) q₀ := by
  have heq : (fun q => deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L i b)
      = fun q => ∑ j ∈ Finset.range L,
          hTermLC (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) j i b := by
    funext q; rw [deltaV0, Matrix.sum_apply]
  rw [heq]
  exact ContDiffAt.sum (fun j _ =>
    genHTermLC_contDiffAt_at H r hr hL J Pf Qf j q₀ hq₀ i b)

/-- `movedZ (C q) (Z0edit0 (C q) L) k` entries are `ContDiffAt` at `q₀`. -/
theorem genMovedZ_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H k - r)) (b : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
        (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k i b) q₀ := by
  cases k with
  | zero =>
    have heq : (fun q => movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) 0 i b)
        = fun q => (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₂₁ i b
          + (deltaV0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L
            * (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) 0).toBlocks₁₁) i b := by
      funext q
      change (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) i b = _
      rw [Z0edit0, Matrix.add_apply]
    rw [heq]
    exact (genChain_contDiffAt_at H r hr hL J Pf Qf 0 q₀ (Sum.inr i) (Sum.inl b)).add
      (contDiffAt_matrix_mul_entry
        (fun a c => genDeltaV0_contDiffAt_at H r hr hL J Pf Qf q₀ hq₀ a c)
        (fun a c => genChain_contDiffAt_at H r hr hL J Pf Qf 0 q₀ (Sum.inl a) (Sum.inl c)) i b)
  | succ n =>
    have heq : (fun q => movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
          (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) (n + 1) i b)
        = fun q =>
          (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) (n + 1)).toBlocks₂₁ i b := rfl
    rw [heq]; exact genChain_contDiffAt_at H r hr hL J Pf Qf (n + 1) q₀ (Sum.inr i) (Sum.inl b)

/-- `movedT (C q) (Z0edit0 (C q) L) k` entries are `ContDiffAt` at `q₀`
(`schurTilde + movedZ · (C k)₁₁⁻¹ · movedY`; the last two never banked even at `0`). -/
theorem genMovedT_contDiffAt_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (k : ℕ)
    (q₀ : DeepestSplit H r (deepestNGauge H r))
    (hq₀ : psiInvBundle H r hr hL J Pf Qf q₀)
    (i : Fin (deepestChainWidth H k - r)) (j : Fin (deepestChainWidth H (k + 1) - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => movedT (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
        (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k i j) q₀ := by
  have heq : (fun q => movedT (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
        (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k i j)
      = fun q => schurTilde (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k i j
        + (movedZ (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q))
            (Z0edit0 (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) L) k
          * Ring.inverse (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q) k).toBlocks₁₁
          * movedY (deepestChain H r hr (framedParamsPivot H r hr hL J Pf Qf q)) k) i j := by
    funext q; rw [movedT, Matrix.add_apply]
  rw [heq]
  refine (genSchurTilde_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ i j).add ?_
  refine contDiffAt_matrix_mul_entry (fun a b => ?_)
    (fun a b => genMovedY_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ a b) i j
  exact contDiffAt_matrix_mul_entry
    (fun c d => genMovedZ_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ c d)
    (fun c d => genInvC11_contDiffAt_at H r hr hL J Pf Qf k q₀ hq₀ c d) a b

end DLNFibre.DLN.RLCT
