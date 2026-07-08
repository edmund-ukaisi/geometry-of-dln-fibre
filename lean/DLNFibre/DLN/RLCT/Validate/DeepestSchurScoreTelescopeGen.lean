import DLNFibre.DLN.RLCT.Validate.DeepestHsub3regGen
import DLNFibre.DLN.RLCT.Validate.DeepestLDUReadback
import DLNFibre.DLN.RLCT.Validate.DeepestFramedChainDecode

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSchurScoreTelescopeGen` — the general-`L` Schur→Score telescope
(#120 `hstep2`, Producer 3)

The general-`L` analog of the banked L=2 `prod_deepestM_eq_schur_ldu_readback`
(`DeepestLDUReadback`): the reduced-core product `prod (deepestM H r) C` over a tuple `C` whose
reindexed layers read back as the **moved Schur cores** `blockSchur (movedC (deepestChain … (decode x))
(Z0edit0 …) s)` equals the Score `(1,1)`-Schur integrand over the framed reindexed product
`reindex(endpointP0 · (prod(decode x) − B) · endpointQL)`.

## The telescope (route, all banked except the two thin bridges here)

* the product of moved Schur cores telescopes to the abstract chain Schur:
  `prod (deepestM H r) C = prodSchurCore (deepestChain … (decode x)) Z0 L`
  (`prod_deepestM_eq_prodSchurCore_of_readback`, a reduced-core `finCongr` fold bridge) then
  `prodSchurCore_eq_blockSchur_partProd` (`DeepestPsiSplitGenMoved`, the banked Invariant B);
* `reindex_prod_eq_partProd` (`DeepestFinBridgeGen`) rewrites `blockSchur (partProd …)` to the unframed
  Schur of `reindex (rThr 0) (deepestChainCol L) (prod (decode x))`;
* the endpoint pivot-column reconciliation (`deepestChainCol L` ↔ `pivotThresholdSplit … J` at
  `J = frontEmbed`) via the banked `pivotFront_toBlocks·_eq_chainCol` + the missing
  `pivotFront_toBlocks₂₂_eq_chainCol` supplied here;
* `score_eq_unframedSchur_prodDecode_gen` (the general-`L` copy of the banked L=2 frame-strip + corner
  identity `score_eq_unframedSchur_prodDecode`, whose body never used `L = 2`) ties the unframed Schur to
  the Score integrand.

Mirrors the L=2 template `prod_deepestM_eq_schur_ldu_readback`. Pure `Matrix`/`Ring`/`Equiv` algebra over
`ℝ`; no `deepestSplit` analysis, no `psiSplitRawGen` differentiability (independent of Producer 1). The
frame-triangular / pivot / chain-invertibility facts (which hold near the deepest point) enter as explicit
hypotheses, matching the L=2 template.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Sublemma 1 — the general-`L` frame-strip + corner Score identity

Verbatim general-`L` copy of the banked `score_eq_unframedSchur_prodDecode` (`DeepestLDUReadback`), whose
proof body never used its `hL2 : L = 2` hypothesis (it only invoked the general
`framedSchur_eq_unframedSchur_L2` + `rcore_eq_schur_of_corner_split`). The Score `(1,1)`-Schur integrand
(over the framed `prod(decode x) − B`, pivot `(M₁₁+1)⁻¹`) equals the unframed `(1,1)`-Schur complement of
`reindex(prod (decode x))` over its own `(1,1)`-block pivot. -/
theorem score_eq_unframedSchur_prodDecode_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hP22 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₂₂ = 1)
    (hQ22 : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₂ = 1)
    (x : Fin (flatDim H) → ℝ)
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hP11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H 0) (hr 0)) (endpointP0 H hL Pf)).toBlocks₁₁)
    (hQ11inv : Invertible (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (endpointQL H hL Qf)).toBlocks₁₁)
    (hMid11inv : Invertible (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
              * endpointQL H hL Qf)).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                * endpointQL H hL Qf)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (prod H ((paramsEquivFlat H).symm x))).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (prod H ((paramsEquivFlat H).symm x))).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₁)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (prod H ((paramsEquivFlat H).symm x))).toBlocks₁₂ := by
  set eR := rThresholdSplit r (H 0) (hr 0) with heR
  set eC := pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J with heC
  set P0 := endpointP0 H hL Pf with hP0
  set QL := endpointQL H hL Qf with hQL
  set Mid := prod H ((paramsEquivFlat H).symm x) with hMid
  have hcorner : Matrix.reindex eR eC (P0 * Mid * QL)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex eR eC (P0 * (Mid - B) * QL) := by
    have hsplitprod : P0 * Mid * QL = P0 * B * QL + P0 * (Mid - B) * QL := by
      rw [Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
    rw [hsplitprod]
    have hadd : Matrix.reindex eR eC (P0 * B * QL + P0 * (Mid - B) * QL)
        = Matrix.reindex eR eC (P0 * B * QL) + Matrix.reindex eR eC (P0 * (Mid - B) * QL) := by
      ext i j; simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
    rw [hadd, hS3b]
  rw [rcore_eq_schur_of_corner_split (P0 * (Mid - B) * QL) (P0 * Mid * QL) eR eC hcorner]
  letI := hP11inv; letI := hQ11inv; letI := hMid11inv
  exact framedSchur_eq_unframedSchur_L2 H r hr hL J P0 QL Mid hPtri hQtri hP22 hQ22
    hP11inv hQ11inv hMid11inv

/-! ## Sublemma 2 — the missing `₂₂` pivot-front / `deepestChainCol` column reconciliation

The `{22}` residual block of the pivot-front reindex is the `deepestChainCol L` one with its `inr`
columns relabelled by the reduced-width `finCongr` (`H (Fin.last L) − r = deepestChainWidth H L − r`).
Mirror of the banked `pivotFront_toBlocks₁₂_eq_chainCol` (both read `inr` columns). -/
theorem pivotFront_toBlocks₂₂_eq_chainCol (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))) (prod H A)).toBlocks₂₂
      = ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (deepestChainCol H r hr L (Nat.lt_succ_self L)) (prod H A)).toBlocks₂₂).submatrix id
          (finCongr (by rw [deepestChainWidth_last])) := by
  funext i j
  simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, id_eq]
  congr 1

/-! ## Sublemma 3 — the reduced-core fold bridge

The `Fin`-side bridge from the reduced-core DLN product `prod (deepestM H r) C` (an unblocked `L`-factor
`prodAux` fold over the `Fin (H · − r)` widths) to the abstract product of moved Schur cores
`prodSchurCore (deepestChain … A) Z0 L`, GIVEN the per-layer readback `hC` (each reindexed reduced-core
layer `C s` equals the moved Schur core `blockSchur (movedC …)`). Mirrors `reindex_prodAux_eq_partProd`
(`DeepestFinBridgeGen`) but on UNBLOCKED reduced-core matrices — the reindex is a pure `finCongr` width
relabel `H · − r ↔ deepestChainWidth · − r`. -/

/-- The reduced-width bridge at an arbitrary index `k ≤ L`: `deepestM H r ⟨k,·⟩ = deepestChainWidth H k − r`
(from `H_eq_deepestChainWidth`). -/
theorem deepestM_eq_chainWidth_sub (H : Fin (L + 1) → ℕ) (r : ℕ) (k : ℕ) (hk : k < L + 1) :
    deepestM H r ⟨k, hk⟩ = deepestChainWidth H k - r := by
  show H ⟨k, hk⟩ - r = deepestChainWidth H k - r
  rw [H_eq_deepestChainWidth H k hk]

/-- The reduced-width bridge at the literal row index `0` (`deepestChainWidth H 0 = H 0`, `rfl`); its
`Fin (deepestM H r 0)` domain matches `prodAux`'s row exactly (unlike the `⟨0, ·⟩` form). -/
theorem deepestM_zero_eq_chainWidth_sub (H : Fin (L + 1) → ℕ) (r : ℕ) :
    deepestM H r 0 = deepestChainWidth H 0 - r := rfl

/-- **The reduced-core fold bridge (all prefix lengths).** For every prefix `k ≤ L`, the reindexed
running reduced-core product equals the abstract moved-Schur-core product `prodSchurCore … k`. Induction
on `k`: base `reindex e e 1 = 1`; the succ-step peels the last layer (`prodAux_succ` +
`reindex_mul_split_gen`), matches the layer via `hC` + the `finCongr`-composition collapse. -/
theorem reindex_prodAux_deepestM_eq_prodSchurCore (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) (C : Params (deepestM H r))
    (hC : ∀ s : Fin L,
      Matrix.reindex (finCongr (chainWidth_castSucc_sub H r s)) (finCongr (chainWidth_succ_sub H r s))
          (C s)
        = blockSchur (movedC (deepestChain H r hr A) (Z0edit0 (deepestChain H r hr A) L) (s : ℕ))) :
    ∀ (k : ℕ) (hk : k < L + 1),
      Matrix.reindex (finCongr (deepestM_zero_eq_chainWidth_sub H r))
          (finCongr (deepestM_eq_chainWidth_sub H r k hk)) (prodAux (deepestM H r) C k hk)
        = prodSchurCore (deepestChain H r hr A) (Z0edit0 (deepestChain H r hr A) L) k := by
  intro k
  induction k with
  | zero =>
      intro hk
      have h1 : prodAux (deepestM H r) C 0 hk
          = (1 : Matrix (Fin (deepestM H r 0)) (Fin (deepestM H r 0)) ℝ) := rfl
      have h2 : prodSchurCore (deepestChain H r hr A) (Z0edit0 (deepestChain H r hr A) L) 0
          = (1 : Matrix (Fin (deepestChainWidth H 0 - r)) (Fin (deepestChainWidth H 0 - r)) ℝ) := rfl
      rw [h1, h2, Matrix.reindex_apply]
      exact Matrix.submatrix_one_equiv _
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : H (⟨k, hk'⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).castSucc) := rfl
      have e2 : H (⟨k + 1, hk⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).succ) := rfl
      rw [prodAux_succ (deepestM H r) C k hk rfl rfl,
        reindex_mul_split_gen (finCongr (deepestM_zero_eq_chainWidth_sub H r))
          (finCongr (deepestM_eq_chainWidth_sub H r k hk')) (finCongr (deepestM_eq_chainWidth_sub H r (k+1) hk)),
        ih hk']
      rw [show prodSchurCore (deepestChain H r hr A) (Z0edit0 (deepestChain H r hr A) L) (k + 1)
          = prodSchurCore (deepestChain H r hr A) (Z0edit0 (deepestChain H r hr A) L) k
            * blockSchur (movedC (deepestChain H r hr A) (Z0edit0 (deepestChain H r hr A) L) k) from rfl]
      congr 1
      rw [← hC ⟨k, hkL⟩]
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
      congr 1

end DLNFibre.DLN.RLCT
