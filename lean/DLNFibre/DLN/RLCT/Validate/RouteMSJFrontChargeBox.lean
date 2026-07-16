import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepCoverage
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceGluing
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellFrontChargeBinding

set_option linter.style.longLine false

/-!
# `RouteMSJFrontChargeBox` — G2: the front-charge box integral is finite (given per-cell `hfin`)

**Thread `genm-3abase` (aoyagi-full Stage 2), the terminal (3a) deep build, G2.** The coupled front-charge
box integral `∫_p frontChargeIntegrand M u c' p` (over `p = (z, A_cor) ∈ paramsBoxM(redChain u M) ×ˢ matBox`)
is finite, GIVEN the coupled per-cell finiteness `hfin` (item 4, the SVD/RRR-floor mountain — held for the
coupled-radial specialist). Assembly: the deep-rank atlas cover (`deepRankLE_eq_iUnion_cells`, banked)
pulled back through the deep-factor projection `p ↦ (paramsHeadSplit z).2` covers the box (`rank Z_deep ≤ M₂`
always, since `Z_deep` is `M₂×n` — no rank floor needed for COMPLETENESS), then `lintegral_lt_top_of_finite_cover`
(banked) glues the per-cell finiteness. NATIVE (the RRR-codim lower bound lives in `hfin`, no
`cited_aoyagi_dln`). Sorry-free with `hfin` the sole hypothesis (the isolated item-4 hole).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory DeepAtlas
open scoped ENNReal

variable {L : ℕ}

/-- The deep-factor projection `p ↦ (paramsHeadSplit z).2` (the deep layers of the reduced params). -/
noncomputable def projDeep (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) → Params (dropHead (redChain u M)) :=
  fun p => (paramsHeadSplit (redChain u M) p.1).2

/-- **The deep factor has rank `≤ M₂` always** (it is an `M₂×n` matrix; `rank ≤ #rows`). This makes the
deep-rank atlas cover at `s = M₂` exhaust the whole space — cover COMPLETENESS needs no rank floor (the RRR
floor is a per-cell EXPONENT fact, in `hfin`, not a cover fact). -/
theorem deepFactor_rank_le_rows (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (z : Params (redChain u M)) :
    (deeperFlagZdeep M u z).rank ≤ dropHead (redChain u M) 0 := by
  have h := (deeperFlagZdeep M u z).rank_le_card_height
  simpa using h.trans (le_of_eq (Fintype.card_fin _))

/-- **G2 — the front-charge box integral is finite, given the coupled per-cell finiteness.** The atlas
cover (deep-rank cells at `s = M₂ = dropHead(redChain u M) 0`, which exhaust the space) pulled back through
`projDeep` covers the box; `lintegral_lt_top_of_finite_cover` glues the per-cell `hfin`. `hfin` (item 4) is
the sole hypothesis — the coupled per-cell finiteness at the RRR floor `minAdm((u,)+deep)`, the specialist's
target. -/
theorem frontChargeBox_lt_top_of_hfin (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (hfin : ∀ i : CRIndex (dropHead (redChain u M)),
        ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
            ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
                le_rfl (dropHead (redChain u M) (Fin.last L)) i (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L))) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
          frontChargeIntegrand M u c' p < ⊤) :
    ∫⁻ p in paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1,
        frontChargeIntegrand M u c' p < ⊤ := by
  classical
  set box := paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1 with hbox
  set dcell : CRIndex (dropHead (redChain u M)) →
      Set (Params (dropHead (redChain u M))) :=
    fun i => deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L le_rfl
      (dropHead (redChain u M) (Fin.last L)) i (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L))) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)) with hdcell
  refine lintegral_lt_top_of_finite_cover (fun i => box ∩ projDeep M u ⁻¹' dcell i) box
    (frontChargeIntegrand M u c') ?_ hfin
  -- cover completeness: `box \ ⋃ (box ∩ projDeep⁻¹' dcell) = ∅`
  have hunion : (⋃ i, box ∩ projDeep M u ⁻¹' dcell i) = box := by
    rw [← Set.inter_iUnion]
    have hcov : (⋃ i, projDeep M u ⁻¹' dcell i) = Set.univ := by
      rw [← Set.preimage_iUnion]
      have hdeep : (⋃ i, dcell i)
          = {A : Params (dropHead (redChain u M)) |
              (prod (dropHead (redChain u M)) A).rank ≤ dropHead (redChain u M) 0} := by
        rw [hdcell, ← deepRankLE_eq_iUnion_cells]
      rw [hdeep]
      ext p
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact deepFactor_rank_le_rows M u p.1
    rw [hcov, Set.inter_univ]
  rw [hunion]; simp

/-- **coupledBox-G2 — the coupled-box integral is finite, given per-cell coupledBox finiteness.** IDENTICAL
atlas-cover gluing to `frontChargeBox_lt_top_of_hfin` (the cover completeness is integrand-independent), with
`coupledBoxIntegrand` (Γ kept on the box, coupling intact) in place of `frontChargeIntegrand`. This is the
HONEST coupled-route entry: the front-charge box is +∞ at EDGE cells (`a+b=ρ+1`) because step-2's Γ→univ
extension (`coupledBox_le_frontCharge` ∘ `corankBlock_morsePeel_setLE`) manufactures the divergent
`det(Q_bQ_bᵀ)^{−a/2}` charge, whereas the coupled box is FINITE per-cell at every rank sector. `hcell` splits
by cell AT THE FILL (not here): in-regime cells (`a+b≤ρ`) via `coupledBox_le_frontCharge` + item 4; edge cells
(`a+b=ρ+1`) via the corank-one edge brick (edgebrick's `edge_coupledBox_lt_top`). -/
theorem coupledBox_lt_top_of_cells (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (hcell : ∀ i : CRIndex (dropHead (redChain u M)),
        ∫⁻ p in (paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1)
            ∩ projDeep M u ⁻¹' (deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L
                le_rfl (dropHead (redChain u M) (Fin.last L)) i (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L))) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ))),
          coupledBoxIntegrand M u c' p < ⊤) :
    ∫⁻ p in paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1,
        coupledBoxIntegrand M u c' p < ⊤ := by
  classical
  set box := paramsBoxM (redChain u M) 1 ×ˢ matBox (M 1 - u) (M 2) 1 with hbox
  set dcell : CRIndex (dropHead (redChain u M)) →
      Set (Params (dropHead (redChain u M))) :=
    fun i => deepCell (dropHead (redChain u M)) (dropHead (redChain u M) 0) L le_rfl
      (dropHead (redChain u M) (Fin.last L)) i (fun _ => (1 : Matrix (Fin (dropHead (redChain u M) (Fin.last L))) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)) with hdcell
  refine lintegral_lt_top_of_finite_cover (fun i => box ∩ projDeep M u ⁻¹' dcell i) box
    (coupledBoxIntegrand M u c') ?_ hcell
  have hunion : (⋃ i, box ∩ projDeep M u ⁻¹' dcell i) = box := by
    rw [← Set.inter_iUnion]
    have hcov : (⋃ i, projDeep M u ⁻¹' dcell i) = Set.univ := by
      rw [← Set.preimage_iUnion]
      have hdeep : (⋃ i, dcell i)
          = {A : Params (dropHead (redChain u M)) |
              (prod (dropHead (redChain u M)) A).rank ≤ dropHead (redChain u M) 0} := by
        rw [hdcell, ← deepRankLE_eq_iUnion_cells]
      rw [hdeep]
      ext p
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact deepFactor_rank_le_rows M u p.1
    rw [hcov, Set.inter_univ]
  rw [hunion]; simp

/-- **The IN-REGIME per-cell dispatch (coupledBox ≤ frontCharge on any cell).** On any measurable cell `s`
where the two a.e.-`p` genericity facts hold (corank Gram PosDef `hGae`; pivot energy `>0` a.e.-`x` `hEtopae`),
the coupled-box integral is dominated by the front-charge integral (per-`p` step 2 `coupledBox_le_frontCharge`
under `lintegral_mono_ae`). So on IN-REGIME cells (`a+b≤ρ`), where item 4 gives `∫frontCharge over s < ⊤`,
`∫coupledBox over s < ⊤` follows. (On EDGE cells `a+b=ρ+1` the front-charge side is `+∞` — this dispatch is
NOT used there; edgebrick's coupledBox brick supplies `∫coupledBox over s < ⊤` directly.) -/
theorem coupledCell_le_frontCell (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (s : Set (Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)))
    (hc' : ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2 < c')
    (hGae : ∀ᵐ p ∂(volume.restrict s),
        ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
          * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).PosDef)
    (hEtopae : ∀ᵐ p ∂(volume.restrict s),
        ∀ᵐ x ∂(volume.restrict (outerDom u (M 0 - u) (M 1 - u) 1)),
          0 < frobSq (Matrix.of x.1.1
            * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
              + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                  * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id))) :
    ∫⁻ p in s, coupledBoxIntegrand M u c' p ≤ ∫⁻ p in s, frontChargeIntegrand M u c' p := by
  refine lintegral_mono_ae ?_
  filter_upwards [hGae, hEtopae] with p hG hEtop
  exact coupledBox_le_frontCharge M u c' p hc' hG hEtop

/-- **The INTERIOR-cell coupledBox slot (conversion from frontCharge finiteness).** Packages the interior
fill of `coupledBox_lt_top_of_cells`'s `hcell i`: given the front-charge cell finiteness (corankrec's
`coupled_hfin_cell_interior`, on interior cells `a+b≤ρ_i`) + the a.e.-`p` genericity on the cell, the
coupled-box cell integral is finite (`coupledCell_le_frontCell` + `lt_of_le_of_lt`). Thin by design — the
LOAD-BEARING content is (a) corankrec's `hfront` (frontCharge finiteness via ChargedRectSchurCore) and (b)
the `hGae` corank-Gram PosDef A.E. ON THE CELL, which needs the cell's own deep rank `ρ_i ≥ b` (the cell can
be null in the box, so the box-level `hGae_from_deepRank` does NOT restrict to it) — a deep-atlas fact.
`hEtopae` (pivot energy `>0`) restricts from the box (polynomial nonvanishing, null in any cell). -/
theorem coupledCell_interior_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (s : Set (Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ)))
    (hc' : ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2 < c')
    (hGae : ∀ᵐ p ∂(volume.restrict s),
        ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id
          * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)ᵀ).PosDef)
    (hEtopae : ∀ᵐ p ∂(volume.restrict s),
        ∀ᵐ x ∂(volume.restrict (outerDom u (M 0 - u) (M 1 - u) 1)),
          0 < frobSq (Matrix.of x.1.1
            * ((hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inl id
              + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                  * (hsQ M u (deeperFlagZdeep M u) p.1 p.2).submatrix Sum.inr id)))
    (hfront : ∫⁻ p in s, frontChargeIntegrand M u c' p < ⊤) :
    ∫⁻ p in s, coupledBoxIntegrand M u c' p < ⊤ :=
  lt_of_le_of_lt (coupledCell_le_frontCell M u c' s hc' hGae hEtopae) hfront

end DLNFibre.DLN.RLCT
