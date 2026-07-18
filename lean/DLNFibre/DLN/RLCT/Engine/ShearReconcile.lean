import DLNFibre.DLN.RLCT.Engine.PivotCoverFold

/-!
# `DLNFibre.DLN.RLCT.Engine.ShearReconcile` — the shear reconciliation lemma (rung 3)

The gauge verdict (`cert-shear-gauge.md`) is **(A) ψ-COMPOSED**: Aoyagi's per-step chart is
`chartMap = ψ ∘ β`, where `β` is the monomial pivot blow-up and `ψ` is the variable-dependent
unipotent `Q`/`P` shear (pp.17-18) — a nontrivial per-node bounded homeomorphism that MOVES
coordinates (so the `LeafPullback` squeeze cannot absorb it; `det Dψ = 1` for the unipotent part, so
the Jacobian battery was blind). Lemma-1 ideal-invariance absorbs the gauge for the RLCT VALUE, but
the geometric COVER needs the actual `ψ ∘ β` chart — which is precisely why this lemma exists.

The coverage fold is already gauge-agnostic (`leafPathImages`/`ownCovers_branch` take arbitrary
`localSub`s; the pivot geometry enters only at the per-node `hnode`). So the reconciliation is a
ψ-composed variant of `node_pivotCover_of_atom`: with the per-node shear `ψ` a homeomorphism, a
cover of `V₀` transports to a cover of `ψ '' V₀` (`ownCover_transport`), and the ψ-composed edges'
image union is `ψ` applied to the pure-pivot union. (Per-edge shears glue to the single per-node
`ψ` on the sector overlaps, so single-`ψ` is the right model — a per-node bounded homeomorphism.)
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **Cover transport through a homeomorphism**: a homeomorphism `ψ` carries an open-neighbourhood
cover of `V₀` by `S` to one of `ψ '' V₀` by `ψ '' S`. The one geometric fact the ψ-composed chart
needs (cert-shear-gauge: "a homeomorphism carries a cover of V to a cover of ψ''V"). -/
theorem ownCover_transport (ψ : Params M ≃ₜ Params M) {V₀ S : Set (Params M)}
    (h : ∃ U : Set (Params M), IsOpen U ∧ V₀ ⊆ U ∧ U ⊆ S) :
    ∃ U : Set (Params M), IsOpen U ∧ ψ '' V₀ ⊆ U ∧ U ⊆ ψ '' S := by
  obtain ⟨U, hUopen, hV, hUS⟩ := h
  exact ⟨ψ '' U, ψ.isOpen_image.mpr hUopen, Set.image_mono hV, Set.image_mono hUS⟩

/-- **The ψ-composed per-node atom bridge** (the shear reconciliation, PROVEN). Same contract as
`node_pivotCover_of_atom` but each edge's `localSub = ψ ∘ (q-conjugated pivotChart)` for a per-node
bounded shear `ψ : Params M ≃ₜ Params M` (Aoyagi's `Q`/`P` clears; `ψ ≠ id` in general —
`cert-shear-gauge` (A)); `V` sits in the `ψ`-image of the open center-slab. `hnode` holds: the
pure-pivot slab cover (via the rung-1 atom) transports through `ψ`. Pure case is `ψ = .refl`. -/
theorem node_pivotCover_of_atom_sheared {edges : List (Edge M)} {V : Set (Params M)}
    {childRegion : Edge M → Set (Params M)} {d : ℕ} {E : Type*} [TopologicalSpace E]
    (hd : 0 < d) {R : ℝ} (hR : 0 < R) (q : Params M ≃ₜ (Fin d → ℝ) × E)
    (ψ : Params M ≃ₜ Params M) (pivotOf : Edge M → Fin d)
    (hbij : ∀ i : Fin d, ∃ e ∈ edges, pivotOf e = i)
    (hloc : ∀ e ∈ edges, ∀ w : Params M,
      e.subst.localSub w = ψ (q.symm (Prod.map (pivotChart (pivotOf e)) id (q w))))
    (hdom : ∀ e ∈ edges, childRegion e = q ⁻¹' (pivotChartDom (pivotOf e) R ×ˢ Set.univ))
    (hV : V ⊆ ψ '' (q ⁻¹' ((Set.univ.pi fun _ => Set.Ioo (-R) R) ×ˢ Set.univ))) :
    ∃ U : Set (Params M), IsOpen U ∧ V ⊆ U ∧
        U ⊆ ⋃ e ∈ edges, e.subst.localSub '' childRegion e := by
  refine ⟨ψ '' (q ⁻¹' ((Set.univ.pi fun _ => Set.Ioo (-R) R) ×ˢ Set.univ)), ?_, hV, ?_⟩
  · exact ψ.isOpen_image.mpr (q.isOpen_preimage.mpr
      ((isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).prod isOpen_univ))
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [Set.mem_preimage, Set.mem_prod] at hw
    have hcube : (q w).1 ∈ cubeBox d R := by
      rw [cubeBox, Set.mem_pi]
      intro k _
      have hk := hw.1 k (Set.mem_univ k)
      rw [Set.mem_Ioo] at hk
      exact Set.mem_Icc.mpr ⟨le_of_lt hk.1, le_of_lt hk.2⟩
    rw [← iUnion_pivotChart_image_eq_cubeBox hd (le_of_lt hR), Set.mem_iUnion] at hcube
    obtain ⟨i, u, hu, hpc⟩ := hcube
    obtain ⟨e, he, hei⟩ := hbij i
    rw [Set.mem_iUnion₂]
    refine ⟨e, he, q.symm (u, (q w).2), ?_, ?_⟩
    · rw [hdom e he, Set.mem_preimage, Homeomorph.apply_symm_apply, Set.mem_prod]
      exact ⟨by rw [hei]; exact hu, Set.mem_univ _⟩
    · rw [hloc e he, Homeomorph.apply_symm_apply, hei]
      simp only [Prod.map_apply, id_eq, hpc]
      rw [← Prod.mk.eta (p := q w), Homeomorph.symm_apply_apply]

end DLNFibre.DLN.RLCT.Engine
