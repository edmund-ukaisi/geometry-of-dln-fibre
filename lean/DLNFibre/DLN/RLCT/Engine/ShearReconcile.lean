import DLNFibre.DLN.RLCT.Engine.PivotCoverFold

/-!
# `DLNFibre.DLN.RLCT.Engine.ShearReconcile` — the shear reconciliation lemma (rung 3)

**RETIRE NOTE (2026-07-19, ψ adjudication `threads/15-psi-adjudication/cert-psi-mix.md`).** The
single-per-node-ψ MODEL described below is REFUTED for a mixed Case-1 node: the `u`-pivot carries `ψ=id`
and the `d`-pivots `ψ=Schur` (and distinct `d`-pivots carry conjugate-not-equal gauges), so no common `ψ`
factors the node, and modelling the mix as a per-edge TARGET gauge opens a fundamental interior cover gap.
The adopted route is **R-b (source reparameterization)**: `localSub_e = β̃_e = β_e ∘ α_e^{-1}` with the
det-1 gauge in the SOURCE, so chart IMAGES equal the pure-β images and the cover is the **pure**
`node_pivotCover_of_atom`. Under R-b `node_pivotCover_of_atom_sheared` is used ONLY at `ψ = .refl` (it
remains a sound generalization of the pure atom; only its "single ψ covers a mixed node" reading is dead).
The docstring below is kept for provenance; read it through this note.

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

/-! ## R-b source-reparameterization atoms (the adopted route, `cert-psi-mix.md` §R-b)

Under R-b the per-edge chart is `β̃_e = β_e ∘ α_e⁻¹` with the det-1 gauge `α_e` in the SOURCE. Two
atoms coverage owes (this file, field-home-independent):
* the **domain-reparam identity** — `β̃_e '' (α_e '' D) = β_e '' D` (any bijection `α_e`); it makes the
  R-b cover reduce to the PURE `node_pivotCover_of_atom` (chart images unchanged);
* the **elementary Schur shear** `α_d` (`α_u = .refl`) — the concrete det-1 SOURCE gauge; the det-1
  Jacobian atom lands next (`cert-psi-mix` §R-b: `|det Dα| = 1` keeps the monomial Jacobian unchanged).
-/

/-- **The domain-reparameterization identity** (the R-b cover reduction): post-composing the pure chart
`β` with the SOURCE gauge inverse `α.symm` and applying it to the gauged domain `α '' D` recovers the
pure image `β '' D` — the gauge does NOT move the covering set. Any bijection `α`; the det-1 shape of the
concrete gauge is not needed here. This is why R-b's per-node cover is the pure `node_pivotCover_of_atom`
(`⋃_e β̃_e '' (α_e '' D_e) = ⋃_e β_e '' D_e`). -/
theorem reparam_image {X Y Z : Type*} (α : X ≃ Y) (β : X → Z) (D : Set X) :
    (β ∘ α.symm) '' (α '' D) = β '' D := by
  rw [Set.image_comp, α.symm_image_image]

variable {d : ℕ}

/-- **The elementary Schur shear** on `Fin d → ℝ`: shift coordinate `a` by `− x_b · x_c` (the inverse
Schur update in ratio coordinates, `cert-psi-mix` §R-b `α_d`; `a`, `b`, `c` the target/two source flat
indices). A polynomial self-map; its inverse adds the product back. -/
def elemShear (a b c : Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  Function.update x a (x a - x b * x c)

/-- The inverse of `elemShear` — add the product back. -/
def elemShearInv (a b c : Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  Function.update x a (x a + x b * x c)

/-- **The elementary Schur shear as a homeomorphism** (`α_d`; `α_u` is `Homeomorph.refl`). A polynomial
bijection with polynomial inverse — needs `a ≠ b`, `a ≠ c` so the shifted coordinate does not feed back
into the two sources. This is the concrete det-1 SOURCE gauge `α_e` the carrier carries; the det-1
Jacobian is the next atom. -/
def elemShearHomeomorph (a b c : Fin d) (hab : a ≠ b) (hac : a ≠ c) :
    (Fin d → ℝ) ≃ₜ (Fin d → ℝ) where
  toFun := elemShear a b c
  invFun := elemShearInv a b c
  left_inv := fun x => by
    funext k
    simp only [elemShear, elemShearInv]
    by_cases hk : k = a
    · subst hk
      simp only [Function.update_self, Function.update_of_ne hab.symm,
        Function.update_of_ne hac.symm]
      ring
    · simp only [Function.update_of_ne hk]
  right_inv := fun x => by
    funext k
    simp only [elemShear, elemShearInv]
    by_cases hk : k = a
    · subst hk
      simp only [Function.update_self, Function.update_of_ne hab.symm,
        Function.update_of_ne hac.symm]
      ring
    · simp only [Function.update_of_ne hk]
  continuous_toFun := by
    change Continuous (fun x : Fin d → ℝ => Function.update x a (x a - x b * x c))
    exact (continuous_id).update a
      ((continuous_apply a).sub ((continuous_apply b).mul (continuous_apply c)))
  continuous_invFun := by
    change Continuous (fun x : Fin d → ℝ => Function.update x a (x a + x b * x c))
    exact (continuous_id).update a
      ((continuous_apply a).add ((continuous_apply b).mul (continuous_apply c)))

end DLNFibre.DLN.RLCT.Engine
