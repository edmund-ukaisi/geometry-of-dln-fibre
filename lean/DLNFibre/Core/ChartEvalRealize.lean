/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartEvalGaugeCommute
import DLNFibre.Core.EndBaseChangeSweep
import DLNFibre.Core.RankNormalFormDim

/-!
# `DLNFibre.Core.ChartEvalRealize` — the chart-evaluation lemma proper (Ψ descent, seam A linchpin)

The route-(b) chart-evaluation lemma (thread 31, Codex `chart-eval-lemma-answer`): the target-side
chart-point evaluation of the Ψ comorphism is `aeval` at the **evaluated-gauge translate** of the
fibre point `B`:

> `evalAway s B hs (chartPsiAeval p)
>     = aeval (canonicalCoord (baseChange (evalGauge (schurEval s) endpointGauge⁻¹) B)) p`.

This is ONE `MvPolynomial.algHom_ext` chaining the tower decomposition `evalAway_comp_chartPsiTower`
(seam A.3) and the gauge-evaluation commute `aevalTower_gaugeSub` (seam A.4); per generator
`evalAway (chartPsiSub x) = canonicalCoord (baseChange (evalGauge …) B) x`.

The **geometric realization** the descent rides: that evaluated-gauge translate
`A := baseChange (evalGauge (schurEval s) endpointGauge⁻¹) B` lies in the rank-exactly-`r` product
locus `Σ^r`, because `B ∈ fibre (normalForm)` (rank `r` by `rank_normalForm`) and the homogeneous
sweep `mem_productRankLocus_iff_mem_sweep` carries any translate of a rank-`r` fibre into `Σ^r`.

## Main results
- `rank_normalForm` — `(normalForm p q r hp hq).rank = r` (the rank-`r` normal form has rank `r`).
- `chartEvalGauge_smul_mem_productRankLocus` — `A ∈ Σ^r` (the realization).
- `evalAway_chartPsiAeval` — the chart-evaluation lemma proper.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **Rank of the rank-`r` normal form.** `(normalForm p q r hp hq).rank = r`: the normal form
`diag(I_r, 0)` is the block matrix `fromBlocks 1 0 0 0` reindexed by the pivot split, whose rank is
`rank (1 : Fin r) + rank 0 = r` (`rank_fromBlocks_zero_offdiag` + `rank_one`), preserved by the
reindexing (`rank_submatrix` along the `finSplit` equivs). -/
theorem rank_normalForm (p q r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (normalForm (k := k) p q r hp hq).rank = r := by
  rw [normalForm, Matrix.rank_submatrix, Matrix.rank_fromBlocks_zero_offdiag,
    Matrix.rank_one, Matrix.rank_zero, Fintype.card_fin, add_zero]

/-- **The evaluated-gauge translate of a fibre point lies in `Σ^r`.** For a fibre point
`B ∈ fibre (normalForm)` and any base-change datum `P`, the translate `baseChange P B` is in the
rank-exactly-`r` product locus: it is a translate of the rank-`r` fibre `fibre (normalForm)`, and
the homogeneous sweep `mem_productRankLocus_iff_mem_sweep` (`N ≥ 1`, `rank normalForm = r`) puts
every such translate in `Σ^r`. The geometric realization the Ψ descent rides. -/
theorem chartEvalGauge_smul_mem_productRankLocus (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : BaseChangeGroup (k := k) d)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq)) :
    baseChange P B ∈ productRankLocus d r := by
  rw [mem_productRankLocus_iff_mem_sweep d Fin.last_pos.ne
    (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq) (rank_normalForm _ _ _ hp hq)]
  exact ⟨P, B, hB, rfl⟩

variable (k) in
/-- **The chart-evaluation lemma proper** (route-(b) linchpin). The target-side chart-point
evaluation `evalAway s B hs` of the Ψ comorphism `chartPsiAeval p` is `aeval` at the
evaluated-gauge translate of the fibre point `B`:

> `evalAway s B hs (chartPsiAeval p)
>     = aeval (canonicalCoord (baseChange (evalGauge (schurEval s) endpointGauge⁻¹) B)) p`.

By `MvPolynomial.algHom_ext`: per generator `x`, `evalAway (chartPsiSub x)` chains the tower
decomposition (A.3, `evalAway_comp_chartPsiTower`) and the gauge-evaluation commute (A.4,
`aevalTower_gaugeSub`) to the `x`-coordinate of the evaluated-gauge translate `baseChange (evalGauge
(schurEval s) endpointGauge⁻¹) B`. -/
theorem evalAway_chartPsiAeval (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurVar (d 0) (d (Fin.last (N + 1))) r → k)
    (B : Tuple (k := k) d) (hB : B ∈ fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    (hs : eval s (detSchurS (d 0) (d (Fin.last (N + 1))) r) ≠ 0)
    (p : MvPolynomial (RepCoord d) k) :
    evalAway k d r hp hq s B hB hs (chartPsiAeval k d r hp hq p)
      = aeval (canonicalCoord d
          (baseChange (evalGauge (d 0) (d (Fin.last (N + 1))) r
            (schurEval (d 0) (d (Fin.last (N + 1))) r s hs)
            (endpointGauge (k := k) d r hp hq)⁻¹) B)) p := by
  -- both sides are `MvPolynomial (RepCoord d) k →ₐ[k] k`; compare on generators via `algHom_ext`.
  have key : (evalAway k d r hp hq s B hB hs).comp (chartPsiAeval k d r hp hq)
      = (aeval (canonicalCoord d
          (baseChange (evalGauge (d 0) (d (Fin.last (N + 1))) r
            (schurEval (d 0) (d (Fin.last (N + 1))) r s hs)
            (endpointGauge (k := k) d r hp hq)⁻¹) B)) :
            MvPolynomial (RepCoord d) k →ₐ[k] k) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [AlgHom.comp_apply, chartPsiAeval, aeval_X, chartPsiSub, aeval_X]
    -- `evalAway (chartPsiTower (gaugeSub (endpointGauge⁻¹) x))`: the tower decomposition (A.3)
    -- turns `evalAway ∘ chartPsiTower` into `aevalTower schurEval (canonicalCoord B)`.
    have htower := evalAway_comp_chartPsiTower (k := k) d r hp hq s B hB hs
    rw [show evalAway k d r hp hq s B hB hs
          (chartPsiTower k d r hp hq (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ x))
        = (evalAway k d r hp hq s B hB hs).comp (chartPsiTower k d r hp hq)
            (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹ x) from rfl, htower]
    -- now `aevalTower schurEval (canonicalCoord B) (gaugeSub (endpointGauge⁻¹) x)`: A.4 commute.
    -- LHS becomes a `baseChange` entry; RHS reduces to `canonicalCoord A x` (`aeval_X` + `simp`).
    rw [aevalTower_gaugeSub]
    exact (canonicalCoord_apply _ x).symm
  exact AlgHom.congr_fun key p

end DLNFibre.Core
