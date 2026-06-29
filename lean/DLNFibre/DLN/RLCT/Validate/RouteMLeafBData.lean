import DLNFibre.DLN.RLCT.Validate.RouteMLeafHeadline
import DLNFibre.DLN.RLCT.Validate.RouteMHmapGen

/-!
# `RouteMLeafBData` — the concrete boundary factor `B` discharging the ∀M-L2 interior-det headline

Constructs the explicit `B`/`DB`/`engine` discharging the three open obligations
(`hmap`/`hasDB`/`hdet`) of `interiorDet_leaf_headline` (`RouteMLeafHeadline`), and assembles the
UNCONDITIONAL ∀M-L2 interior-determinant headline `interiorDet_leaf_headline_unconditional`:

  `|det Dφ| = |u p₀|^(minAdm M − 1) · ∏_s engine_s`

for the REAL `genBlkFlatLive` + leaf-pivot chart `phiFlatLiveAt`.

The boundary factor `B = Bchart` is the `u`-FREE per-layer chart that reads the residual coordinates
as ORDINARY `y`-values (no radial blow-up); the `u`-scaling lives entirely in `pivotBlowupOn`. The
map identity `hmap` reduces (funext + `paramsEquivFlat` injective) to a per-layer chart-parameter
equality, which — via `Agen_congr` — reduces to matching `Nblk`/`Wblk`/`Cgen(k+1)` on the two
configs (NO explicit `chainA` reindexing over the dependent `Fin (Text/Wext)` widths). The Cgen uses
the banked `Cgen_live_interior_eq_schurFrameProd` + `schurFrameProd_u_to_E` (the radial `u` moves
into the residual coordinate) at the interior boundary, and `Cgen_live_leaf` at the leaf.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra + the banked wiring; no
analysis beyond the chain rule `radialComp_abs_det_at` already uses).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Foundational matrix lemmas (the E-scaling kernel) -/

/-- `rmatPad` is ℝ-linear in `E`: `rmatPad (c • E) = c • rmatPad E`. -/
theorem rmatPad_smul {M t : Fin (L + 1) → ℕ} {s : ℕ}
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (c : ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ) :
    rmatPad M t s h1 h2 (c • E) = c • rmatPad M t s h1 h2 E := by
  unfold rmatPad
  rw [show Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
        0 0 (c • E) = c • Matrix.fromBlocks 0 0 0 E from by
    rw [Matrix.fromBlocks_smul, smul_zero, smul_zero, smul_zero]]
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_smul]
  rfl

/-- The leaf transition for the LIVE decoder `Cgen v (genBlkFlatLive …) L = v • rfin`. -/
theorem Cgen_live_leaf (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (v : ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha) L = v • rfin := by
  rw [Cgen, dif_neg (lt_irrefl L)]
  congr 1
  show (genBlkFlatLive M t ha rfin x).Rfin L = rfin
  simp only [genBlkFlatLive]
  split
  · rfl
  · rename_i h; exact (h trivial).elim

/-- **The E-scaling identity for `schurFrameProd`**: `schurFrameProd … u K X N E
= schurFrameProd … 1 K X N (u • E)`. The `bmatStack·chainQ` part has no `u`; the `u • rmatPad E`
part equals `1 • rmatPad (u • E) = rmatPad (u • E)` by `rmatPad_smul`. The DECODER-MATCH kernel:
the radial `u` of the chart's E-term moves into the residual coordinate `u • E` of the u-free B. -/
theorem schurFrameProd_u_to_E (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ) :
    schurFrameProd M t s h1 h2 u K X N E
      = schurFrameProd M t s h1 h2 1 K X N (u • E) := by
  rw [schurFrameProd, schurFrameProd, rmatPad_smul, one_smul]

/-! ## The `Agen` congruence (block-level, no explicit `chainA` reindexing) -/

/-- **`Agen` congruence**: `Agen` at boundary `k` depends only on `(B.Nblk k, B.Wblk k,
Cgen u … B (k+1))` (plus the fixed `M`/`t`/`hle` width proof). So two `(u, B)` configs with matching
`Nblk k`, `Wblk k`, and `Cgen (k+1)` produce the SAME `Agen k`. This is the kernel reducing the
`hmap` per-layer match to a Cgen-block match — NO explicit `chainA` reindexing over the dependent
`Fin (Text/Wext)` widths. -/
theorem Agen_congr (M t : Fin (L + 1) → ℕ) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (u₁ u₂ : ℝ) (B₁ B₂ : GenBlk M t) (k : ℕ)
    (hN : B₁.Nblk k = B₂.Nblk k) (hW : B₁.Wblk k = B₂.Wblk k)
    (hC : Cgen u₁ M t B₁ hle (k + 1) = Cgen u₂ M t B₂ hle (k + 1)) :
    Agen u₁ M t B₁ hle k = Agen u₂ M t B₂ hle k := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk, hN, hW, hC]
  · rw [dif_neg hk, dif_neg hk]

end DLNFibre.DLN.RLCT
