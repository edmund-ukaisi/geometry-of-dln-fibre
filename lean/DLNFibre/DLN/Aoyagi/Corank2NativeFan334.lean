import DLNFibre.DLN.Aoyagi.Corank2NativePerm334
import DLNFibre.DLN.Aoyagi.ImageTreeCover

/-!
# `DLN.Aoyagi.Corank2NativeFan334` — the WHOLE-CONJUGATE born-native (3,3,4) fan + `hcover`

The **value-correct** born-native fan (the whole loss-symmetry conjugate `g_c = σ⁻¹ ∘ gWrap ∘ σ`,
pnp double-certified `rlct ≥ 4` / `divisorMin ≥ 8` on all 288 — `whole_conjugate_all288.out`). The
prior §2-shear-only fan (`bb(C1,p2)`/`bb(C2,p3)` at the FIXED canonical centres, node-1 = shear only)
was cover-fit but VALUE-broken (the survivor landed on an A1-spectator). The fix conjugates EVERY
atom, which decomposes into DIRECT atoms (`blockBlowupMap_conj`, elder-confirmed W3-clean):

`g_c = bb(σC0,σ20) ∘ [native shear] ∘ [native perm] ∘ bb(σC1,σp2) ∘ bb(σC2,σp3)`

where `σC0 = C0` (the loss symmetry fixes the 9 A0 slots), so node-1 centre stays `S1` with pivot
`σ20 = p1`; the native shear/perm are `nativeChart1` (`Corank2NativePerm334`); and the node-2/node-3
centres are the PERMUTED `σ(C1)`/`σ(C2)` (p1-dependent), given as DIRECT native Finsets
(`sigmaC1Fs`/`sigmaC2Fs`, `whole_conjugate_all288.out §[1]`). The DEF uses these direct atoms; the
σ-conjugate identity is the description (`blockBlowupMap_conj` + the numerical 288/288 cross-check).

This module delivers the (A-rework) cover side:
- `nativeFan` — the explicit whole-conjugate 3-node fan (node-1 shear `nativeChart1`, node-2/node-3 at
  permuted centres, `id` shears); `nativeFan_covers` — it `Covers fInfl · 1` (node-1 composite shear
  box-contains at `C = 2` via `nativeChart1_covers`; the id nodes trivially — the permuted centres do
  not touch the `Covers` clauses, which are center-blind).
- `gFlat` / `gFin` — the ONE flat leaf family (a leaf composite per pivot-path, `Fin numCharts`
  indexed) that BOTH `hcover` and the later `hentry` (the (B) seat) ride. The leaf index is the
  DEPENDENT `Σ p1, σC1(p1) × σC2(p1)` (`= 288`, the ACTUAL whole-conjugate leaf set).
- `native_hcover` — `volume (ball 0 1 \ ⋃ c, gFin c '' domFin c) = 0`: the leaf composites cover a
  nbhd of `0` FULLY, so the uncovered set is empty (a fortiori null).

## Scope
- IN: the whole-conjugate fan, its `Covers`, the flat family, `native_hcover` + differentiability +
  compactness; the `blockBlowupMap_conj` characterization.
- OUT: `hentry` (the (B) seat); the per-leaf `jac`/`unit`/`divisorMin`/`ek₀`/`k0` (the (C) seat,
  `Corank2NativeValue334`).
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
open DLNFibre.DLN.Aoyagi.LeafCoverTiling

namespace DLNFibre.DLN.Aoyagi.NativeFan334

/-! ## §0 — the decomposition characterization: conj of a blow-up = blow-up at the permuted centre -/

/-- **`blockBlowupMap_conj` (the elder-named characterization).** The `σ`-conjugate of the block
blow-up at `(C, p)` IS the DIRECT block blow-up at the PERMUTED centre `(σ C, σ p)`:
`σ⁻¹ ∘ blockBlowupMap C p ∘ σ = blockBlowupMap (σ C) (σ p)` (`σ` a coordinate permutation). This is
the value-fidelity witness for the whole-conjugate fan's node-2/node-3 atoms: the DEF below uses the
direct RHS at the native centres, and this lemma proves it equals the σ-conjugate description. -/
theorem blockBlowupMap_conj {D : ℕ} (σ : Equiv.Perm (Fin D)) (C : Finset (Fin D)) (p : Fin D) :
    (fun w t ↦ blockBlowupMap C p (fun k ↦ w (σ k)) (σ.symm t))
      = blockBlowupMap (C.image σ) (σ p) := by
  funext w t
  simp only [blockBlowupMap]
  by_cases htp : σ.symm t = p
  · have ht : t = σ p := by rw [← htp, Equiv.apply_symm_apply]
    rw [if_pos htp, if_pos ht]
  · have ht : t ≠ σ p := fun h ↦ htp (by rw [h, Equiv.symm_apply_apply])
    rw [if_neg htp, if_neg ht]
    by_cases hC : σ.symm t ∈ C
    · have ht' : t ∈ C.image σ := by
        rw [Finset.mem_image]; exact ⟨σ.symm t, hC, Equiv.apply_symm_apply σ t⟩
      rw [if_pos hC, if_pos ht', Equiv.apply_symm_apply]
    · have ht' : t ∉ C.image σ := by
        rw [Finset.mem_image]; rintro ⟨a, ha, rfl⟩
        exact hC (by rwa [Equiv.symm_apply_apply])
      rw [if_neg hC, if_neg ht', Equiv.apply_symm_apply]

/-! ## §1 — the fan (with permuted node-2/node-3 centres) and its cover -/

/-- Node-1 outer center (the 9 A0-dominant pivot slots; `σC0 = C0` is fixed by the loss symmetry). -/
abbrev S1 : Finset (Fin 21) := {0, 1, 2, 3, 4, 5, 6, 7, 20}

/-- **The permuted node-2 centre `σ(C1)`** per dominant pivot `p1` (`whole_conjugate_all288.out §[1]`;
default `C1 = {0..7}` off the 9 dominants — the canonical `p1 = 20` value). DIRECT native Finsets. -/
def sigmaC1Fs (p : Fin 21) : Finset (Fin 21) :=
  if p = 0 then ({1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))
  else if p = 1 then ({0, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))
  else if p = 2 then ({0, 1, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))
  else if p = 3 then ({0, 1, 2, 4, 5, 6, 7, 20} : Finset (Fin 21))
  else if p = 4 then ({0, 1, 2, 3, 5, 6, 7, 20} : Finset (Fin 21))
  else if p = 5 then ({0, 1, 2, 3, 4, 6, 7, 20} : Finset (Fin 21))
  else if p = 6 then ({0, 1, 2, 3, 4, 5, 7, 20} : Finset (Fin 21))
  else if p = 7 then ({0, 1, 2, 3, 4, 5, 6, 20} : Finset (Fin 21))
  else ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21))

/-- **The permuted node-3 centre `σ(C2)`** per dominant pivot `p1` (`whole_conjugate_all288.out §[1]`;
default `C2 = {1,5,6,7}` off the 9 dominants). DIRECT native Finsets. -/
def sigmaC2Fs (p : Fin 21) : Finset (Fin 21) :=
  if p = 0 then ({1, 3, 5, 7} : Finset (Fin 21))
  else if p = 1 then ({2, 3, 6, 20} : Finset (Fin 21))
  else if p = 2 then ({1, 5, 6, 7} : Finset (Fin 21))
  else if p = 3 then ({0, 1, 5, 7} : Finset (Fin 21))
  else if p = 4 then ({1, 3, 5, 7} : Finset (Fin 21))
  else if p = 5 then ({2, 3, 6, 20} : Finset (Fin 21))
  else if p = 6 then ({1, 5, 7, 20} : Finset (Fin 21))
  else if p = 7 then ({0, 2, 3, 20} : Finset (Fin 21))
  else ({1, 5, 6, 7} : Finset (Fin 21))

theorem sigmaC1Fs_nonempty (p : Fin 21) : (sigmaC1Fs p).Nonempty := by
  simp only [sigmaC1Fs]; split_ifs <;> decide

theorem sigmaC2Fs_nonempty (p : Fin 21) : (sigmaC2Fs p).Nonempty := by
  simp only [sigmaC2Fs]; split_ifs <;> decide

/-- The box-inflation `r ↦ r + 2r²` (the two-product shear slots force `C = 2`). -/
def fInfl : ℝ → ℝ := fun r => r + 2 * r ^ 2

/-- The leaf-box radius: the threefold `fInfl (max · 1)` propagation from radius `1`, so the leaf
`Covers` clause is `subset_rfl`. -/
def leafR : ℝ := fInfl (max (fInfl (max (fInfl (max 1 1)) 1)) 1)

/-- **The whole-conjugate born-native (3,3,4) fan.** Node 1: outer center `S1`, per-pivot composite
native shear `nativeChart1` (native shear ∘ native perm). Node 2: PERMUTED center `sigmaC1Fs p1`,
`id` shear. Node 3: PERMUTED center `sigmaC2Fs p1`, `id` shear. Leaves: `closedBall 0 leafR`. -/
noncomputable def nativeFan : FanTree 21 :=
  FanTree.node S1 (by decide) nativeChart1 (fun p1 =>
    FanTree.node (sigmaC1Fs p1) (sigmaC1Fs_nonempty p1) (fun _ => id) (fun _ =>
      FanTree.node (sigmaC2Fs p1) (sigmaC2Fs_nonempty p1) (fun _ => id) (fun _ =>
        FanTree.leaf (closedBall 0 leafR))))

/-- **The fan covers** `closedBall 0 1` under `fInfl = r ↦ r + 2r²`: node 1's composite shears
box-contain at `C = 2` (`nativeChart1_covers`), the two id nodes trivially (the permuted centres do
not enter the center-blind `Covers` shear clauses), the leaf `subset_rfl`. -/
theorem nativeFan_covers : FanTree.Covers fInfl nativeFan 1 := by
  refine ⟨fun p hp => ?_, fun p _ => ⟨fun q _ => ?_, fun q _ => ⟨fun s _ => ?_, fun s _ => ?_⟩⟩⟩
  · exact nativeChart1_covers p hp
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

/-! ## §2 — the flat leaf family (`gFlat` / `gFin`) over the DEPENDENT whole-conjugate index -/

/-- The leaf index: a whole-conjugate pivot-path — `p1 ∈ S1`, `p2 ∈ σC1(p1)`, `p3 ∈ σC2(p1)` (the
node-2/node-3 pivots range over the PERMUTED centres, so the index is DEPENDENT; `= 288`). -/
abbrev Idx : Type :=
  Σ p1 : {p // p ∈ S1}, {p // p ∈ sigmaC1Fs p1.1} × {p // p ∈ sigmaC2Fs p1.1}

/-- **The whole-conjugate leaf composite** for a pivot-path: node 1
`blockBlowupMap S1 p1 ∘ nativeChart1 p1`, node 2 `blockBlowupMap (σC1 p1) p2 ∘ id`, node 3
`blockBlowupMap (σC2 p1) p3 ∘ id` — the value-correct whole-conjugate chart of that leaf. -/
noncomputable def gFlat (idx : Idx) : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  (blockBlowupMap S1 idx.1.1 ∘ nativeChart1 idx.1.1) ∘
    ((blockBlowupMap (sigmaC1Fs idx.1.1) idx.2.1.1 ∘ id) ∘
      (blockBlowupMap (sigmaC2Fs idx.1.1) idx.2.2.1 ∘ id))

/-- Each leaf composite is differentiable (block blow-ups + the composite native shear + `id`). -/
theorem differentiable_gFlat (idx : Idx) : Differentiable ℝ (gFlat idx) := by
  refine ((differentiable_blockBlowupMap _ _).comp (nativeChart1_differentiable _)).comp
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
  refine Set.mem_iUnion.mpr ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩, z, hz, ?_⟩
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
  Fintype.card_pos_iff.mpr ⟨⟨⟨20, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩⟩

/-! ## §3 — `hcover`: the leaf family covers a neighbourhood of `0` (fully, hence up-to-null) -/

/-- **`hcover` (the (A-rework) deliverable).** `volume (ball 0 1 \ ⋃ c, gFin c '' domFin c) = 0` — the
whole-conjugate leaf family covers a neighbourhood of `0`. FULL cover (`ball 0 1 ⊆ ⋃ c`) via the fan
`Covers` + the flatten + the `Fin`-reindex, so the uncovered set is empty (a fortiori null). -/
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
#assert_banked_clean_batch [blockBlowupMap_conj, nativeFan_covers, closedBall_one_subset_leafImages,
  leafImages_subset_flat, native_hcover, differentiable_gFin, isCompact_domFin, numCharts_pos]

end DLNFibre.DLN.Aoyagi.NativeFan334
