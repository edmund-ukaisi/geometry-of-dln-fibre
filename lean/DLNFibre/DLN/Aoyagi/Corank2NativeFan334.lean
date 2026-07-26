import DLNFibre.DLN.Aoyagi.Corank2NativeShear334
import DLNFibre.DLN.Aoyagi.ImageTreeCover

/-!
# `DLN.Aoyagi.Corank2NativeFan334` — the born-native (3,3,4) fan + the flat leaf family + `hcover`

The born-native fan (elder-pinned shape (b), `assembly-extraction.md` §3): a 3-node `FanTree` whose
node 1 carries the per-pivot native shears `nativeSel` over the outer center `{0,1,2,3,4,5,6,7,20}`,
and whose nodes 2, 3 keep the fixed inner block-blow-up structure `bbA0` (center `{0..7}`) / `bbA1`
(center `{1,5,6,7}`) with `id` shears. Leaves = pivot-paths (`9 × 8 × 4 = 288`).

This module delivers the (A)-seat cover side:
- `nativeFan` — the explicit 3-node fan; `nativeFan_covers` — it `Covers (r ↦ r + 2r²) · 1` (each
  node-1 native shear box-contains at `C = 2` via `nativeSel_covers`; the two id nodes trivially).
- `gFlat` / `gFin` — the ONE flat leaf family (a leaf composite per pivot-path; `Fin numCharts`
  indexed via `idxEquiv`) that BOTH `hcover` and the later `hentry` (the (B) seat) ride —
  W1: cover-charts and value-charts are not split.
- `native_hcover` — `volume (ball 0 1 \ ⋃ c, gFin c '' domFin c) = 0`: the leaf composites cover a
  nbhd of `0` FULLY (`ball 0 1 ⊆ closedBall 0 1 ⊆ leafImages = ⋃ c, gFin c '' domFin c`), so the
  uncovered set is empty — the `hcover` field of `rlctAt_coreGen334_ge_four_of_survivor_entries`.
  (A full cover discharges the up-to-null `hcover` directly, so the `{X=0}` hole never bites.)
- structural fields of the family: differentiability, compact domains.

## Scope
- IN: the fan, its `Covers`, the flat family, `native_hcover` + differentiability + compactness.
- OUT: `hentry` (the (B) seat); the per-leaf `jac`/`unit`/`divisorMin` + a.e.-injectivity (the (C)
  seat).
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
open DLNFibre.DLN.Aoyagi.LeafCoverTiling

namespace DLNFibre.DLN.Aoyagi.NativeFan334

/-! ## §1 — the fan and its cover -/

/-- Node-1 outer center (the 9 A0-dominant pivot slots). -/
abbrev S1 : Finset (Fin 21) := {0, 1, 2, 3, 4, 5, 6, 7, 20}
/-- Node-2 center (`bbA0`: the `E`-block). -/
abbrev S2 : Finset (Fin 21) := {0, 1, 2, 3, 4, 5, 6, 7}
/-- Node-3 center (`bbA1`: the `α`-block). -/
abbrev S3 : Finset (Fin 21) := {1, 5, 6, 7}

/-- The box-inflation `r ↦ r + 2r²` (the two-product shear slots force `C = 2`). -/
def fInfl : ℝ → ℝ := fun r => r + 2 * r ^ 2

/-- The leaf-box radius: the threefold `fInfl (max · 1)` propagation from radius `1`, so the leaf
`Covers` clause is `subset_rfl`. -/
def leafR : ℝ := fInfl (max (fInfl (max (fInfl (max 1 1)) 1)) 1)

/-- **The born-native (3,3,4) fan.** Node 1: outer center `S1`, per-pivot native shear `nativeSel`.
Nodes 2, 3: centers `S2`/`S3`, `id` shears (the fixed inner `bbA0`/`bbA1` block blow-ups). Leaves:
`closedBall 0 leafR`. -/
noncomputable def nativeFan : FanTree 21 :=
  FanTree.node S1 (by decide) nativeSel (fun _ =>
    FanTree.node S2 (by decide) (fun _ => id) (fun _ =>
      FanTree.node S3 (by decide) (fun _ => id) (fun _ =>
        FanTree.leaf (closedBall 0 leafR))))

/-- **The fan covers** `closedBall 0 1` under `fInfl = r ↦ r + 2r²`: node 1's native shears
box-contain at `C = 2` (`nativeSel_covers`), the two id nodes trivially, the leaf `subset_rfl`. -/
theorem nativeFan_covers : FanTree.Covers fInfl nativeFan 1 := by
  refine ⟨fun p hp => ?_, fun p _ => ⟨fun q _ => ?_, fun q _ => ⟨fun s _ => ?_, fun s _ => ?_⟩⟩⟩
  · exact nativeSel_covers p hp
  · simp only [Set.image_id]
    refine closedBall_subset_closedBall ?_
    simp only [fInfl]; exact le_add_of_nonneg_right (by positivity)
  · simp only [Set.image_id]
    refine closedBall_subset_closedBall ?_
    simp only [fInfl]; exact le_add_of_nonneg_right (by positivity)
  · exact subset_rfl

/-- The closed unit ball is covered by the fan's leaf-chart images. -/
theorem closedBall_one_subset_leafImages :
    closedBall (0 : Fin 21 → ℝ) 1 ⊆ nativeFan.leafImages :=
  FanTree.covers_subset nativeFan nativeFan_covers

/-! ## §2 — the flat leaf family (`gFlat` / `gFin`) + the flatten of `leafImages` -/

/-- The leaf index: a pivot-path `(p1, p2, p3)` through the three centers (`9 × 8 × 4 = 288`). -/
abbrev Idx : Type := {p // p ∈ S1} × {p // p ∈ S2} × {p // p ∈ S3}

/-- **The leaf composite** for a pivot-path: node 1 `blockBlowupMap S1 p1 ∘ nativeSel p1`, node 2
`blockBlowupMap S2 p2 ∘ id`, node 3 `blockBlowupMap S3 p3 ∘ id` — the born-native chart of that
leaf. -/
noncomputable def gFlat (idx : Idx) : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  (blockBlowupMap S1 idx.1.1 ∘ nativeSel idx.1.1) ∘
    ((blockBlowupMap S2 idx.2.1.1 ∘ id) ∘ (blockBlowupMap S3 idx.2.2.1 ∘ id))

/-- Each leaf composite is differentiable (block blow-ups + the native shear + `id`). -/
theorem differentiable_gFlat (idx : Idx) : Differentiable ℝ (gFlat idx) := by
  refine ((differentiable_blockBlowupMap _ _).comp (nativeSel_differentiable _)).comp
    (((differentiable_blockBlowupMap _ _).comp differentiable_id).comp
      ((differentiable_blockBlowupMap _ _).comp differentiable_id))

/-- **The flatten**: the fan's leaf-chart images are the leaf composites over the pivot-paths,
`leafImages ⊆ ⋃ idx, gFlat idx '' closedBall 0 leafR` (a chase peeling the three node unions). -/
theorem leafImages_subset_flat :
    nativeFan.leafImages ⊆ ⋃ idx : Idx, gFlat idx '' closedBall 0 leafR := by
  intro x hx
  simp only [nativeFan, FanTree.leafImages_node, FanTree.leafImages_leaf, Set.mem_iUnion,
    Set.mem_image, Function.comp_apply, id_eq, exists_prop] at hx
  obtain ⟨p1, hp1, y2, ⟨p2, hp2, y3, ⟨p3, hp3, z, hz, hzeq⟩, hy2eq⟩, hxeq⟩ := hx
  refine Set.mem_iUnion.mpr ⟨(⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩), z, hz, ?_⟩
  simp only [gFlat, Function.comp_apply, id_eq]
  rw [hzeq, hy2eq, hxeq]

/-- The number of leaf charts (`= 288`, `Fintype.card Idx`). -/
noncomputable def numCharts : ℕ := Fintype.card Idx

/-- The `Fin numCharts ≃ Idx` reindexing (the flat family is `Fin`-indexed for the contract). -/
noncomputable def idxEquiv : Fin numCharts ≃ Idx := (Fintype.equivFin Idx).symm

/-- **The flat `Fin`-indexed leaf family** — the ONE family carrying both `hcover` and (later)
`hentry`. -/
noncomputable def gFin (c : Fin numCharts) : (Fin 21 → ℝ) → (Fin 21 → ℝ) := gFlat (idxEquiv c)

/-- The per-leaf domain (the common leaf box `closedBall 0 leafR`, compact). -/
def domFin (_ : Fin numCharts) : Set (Fin 21 → ℝ) := closedBall 0 leafR

theorem differentiable_gFin (c : Fin numCharts) : Differentiable ℝ (gFin c) :=
  differentiable_gFlat (idxEquiv c)

theorem isCompact_domFin (c : Fin numCharts) : IsCompact (domFin c) := isCompact_closedBall 0 leafR

theorem numCharts_pos : 0 < numCharts :=
  Fintype.card_pos_iff.mpr ⟨(⟨20, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩)⟩

/-! ## §3 — `hcover`: the leaf family covers a neighbourhood of `0` (fully, hence up-to-null) -/

/-- **`hcover` (the (A)-seat deliverable).** `volume (ball 0 1 \ ⋃ c, gFin c '' domFin c) = 0` — the
born-native leaf family covers a neighbourhood of `0`. The cover is FULL (`ball 0 1 ⊆ ⋃ c`), via the
fan `Covers` + the flatten + the `Fin`-reindex, so the uncovered set is empty (a fortiori null): the
`hcover` field of `rlctAt_coreGen334_ge_four_of_survivor_entries`. -/
theorem native_hcover :
    volume (ball (0 : Fin 21 → ℝ) 1 \ ⋃ c, gFin c '' domFin c) = 0 := by
  have hsub : ball (0 : Fin 21 → ℝ) 1 ⊆ ⋃ c, gFin c '' domFin c := by
    have h3 : (⋃ idx : Idx, gFlat idx '' closedBall 0 leafR) = ⋃ c, gFin c '' domFin c := by
      rw [show (⋃ c, gFin c '' domFin c)
            = ⋃ c, gFlat (idxEquiv c) '' closedBall 0 leafR from rfl]
      exact (idxEquiv.surjective.iUnion_comp (fun idx => gFlat idx '' closedBall 0 leafR)).symm
    calc ball (0 : Fin 21 → ℝ) 1 ⊆ closedBall 0 1 := ball_subset_closedBall
      _ ⊆ nativeFan.leafImages := closedBall_one_subset_leafImages
      _ ⊆ ⋃ idx : Idx, gFlat idx '' closedBall 0 leafR := leafImages_subset_flat
      _ = ⋃ c, gFin c '' domFin c := h3
  rw [Set.diff_eq_empty.mpr hsub, measure_empty]

/-- `ball 0 1` is a neighbourhood of `0` (the `hU` field). -/
theorem ball_one_mem_nhds : ball (0 : Fin 21 → ℝ) 1 ∈ nhds (0 : Fin 21 → ℝ) :=
  ball_mem_nhds 0 one_pos

-- Forced axiom gate: the fan + cover deliverables rest only on `[propext, Classical.choice,
-- Quot.sound]`. Force-elaborates (no stale-olean masking of a `sorryAx`; lean/CLAUDE.md caveat).
#assert_banked_clean_batch [nativeFan_covers, closedBall_one_subset_leafImages,
  leafImages_subset_flat, native_hcover, differentiable_gFin, isCompact_domFin, numCharts_pos]

end DLNFibre.DLN.Aoyagi.NativeFan334
