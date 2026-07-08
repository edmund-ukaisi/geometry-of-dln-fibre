import DLNFibre.DLN.RLCT.Validate.D1GeBlockProd
import DLNFibre.DLN.RLCT.Validate.D1GeCommonPivot

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeSchurTelescope` — the asymmetric general-`L` Schur telescope

Piece (iii), algebraic core (rungs 1–3 of the corner-elimination chart ladder). The **asymmetric**
Schur-product telescope: the `(1,1)`-Schur complement of the `L`-layer block product factors as an
ordered product of per-layer reduced factors, using ONLY the partial-product (prefix) pivots — never
a per-layer pivot. This is what lets the general-`L` chart avoid the `hLayer` hypotheses of the
symmetric `schur_product_ldu_rec` (which piece (i) does not supply; those would need Cauchy–Binet).

The asymmetric two-factor brick is `Core.schur_product_factor`
(`Sch(A0·A1) = (W − Z⅟X Y)·(V − U⅟M11 M12)`, needing `[Invertible X]` + `[Invertible M11]` — left
pivot and the product pivot, NOT the right factor's own pivot).

* `prefixPivotDomGen` (rung 1) — the pivot domain: at an optimal `v`, a common pivot `ι` (piece (i))
  making EVERY partial-product block pivot `(partProd (genChain …) k).toBlocks₁₁` invertible; from
  `exists_common_pivot_gen` (piece i) with `genPartProd_toBlocks₁₁` (piece ii).
* `redFactorGen` (rung 2 support) — the per-layer reduced factor `R_k` (rel. to the product pivot).
* `blockSchur_partProd_succ_asym` (rung 2) — the asymmetric single-step:
  `blockSchur (partProd C (k+1)) = blockSchur (partProd C k) · R_k`, from the two prefix pivots.
* `blockSchur_partProd_asym_fold` (rung 3) — the telescope `blockSchur (partProd C L) = ∏ R_k`.

Pure `Matrix`/`Ring` algebra over `ℝ`. The chart map `schurChartRawGen` + inverse + `ContDiff` +
(rungs 4–8) are downstream.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Rung 1 — the partial-product pivot domain (from pieces (i) + (ii)) -/

/-- **Rung 1 — the prefix-pivot domain.** At an optimal `v` (`prod H v = B`, `B.rank = r`), the
pivot `ι` of `exists_common_pivot_gen` (piece i) makes EVERY partial-product block pivot invertible:
`((partProd (genChain …) k).toBlocks₁₁).det ≠ 0` for all `k ≤ L`. This is the `hPart` (partial-
pivot) gate the asymmetric telescope needs, obtained by composing piece (i)'s prefix-minor `det ≠ 0`
with piece (ii)'s `genPartProd_toBlocks₁₁` (block corner = prefix minor). -/
theorem prefixPivotDomGen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (v : Params H) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hopt : prod H v = B) (hB : B.rank = r) :
    ∃ (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)),
      ∀ (k : ℕ) (_hk : k < L + 1),
        ((partProd (genChain H r hr ι hι v) k).toBlocks₁₁).det ≠ 0 := by
  obtain ⟨ι, hι, hdet⟩ := exists_common_pivot_gen H r v B hopt hB
  refine ⟨ι, hι, fun k hk => ?_⟩
  rw [genPartProd_toBlocks₁₁ H r hr ι hι v k hk]
  exact hdet ⟨k, hk⟩

end DLNFibre.DLN.RLCT
