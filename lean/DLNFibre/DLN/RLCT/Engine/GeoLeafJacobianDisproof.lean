import DLNFibre.DLN.RLCT.Engine.GeoLeafJacobian

/-!
# `GeoLeafJacobianDisproof` — a machine-checked refutation of the GENERIC-`s` fold-Jacobian headline

`geoAtlas_fold_det` (`GeoLeafJacobian.lean`) is stated over a GENERIC `s : ConState L`, with no
hypothesis. This module witnesses that that generic form is FALSE (the honest scope is `conRoot`, per
finding-1 / cert): at a TERMINAL state `s` carrying an analytic (`t̃=0`) divisor of exponent ≥ 2, the
built tree is a single leaf with `chartMap = id`, so the LHS `|det D id w| = 1`, while the RHS
`∏ |z|^{divExp−1}` vanishes at `w = 0` (a positive power of `0`). `1 ≠ 0`.

This is a tripwire, NOT part of the engine — it exists only to pin the statement-level obstruction
surfaced by architect-t14. -/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

/-- **The counterexample state**: layer `= L` (terminal, `L ≤ layer`), one divisor of exponent `2` with
the all-zero profile (so `t̃ = 0`, analytic), everything else trivial. -/
def csWitness (L : ℕ) : ConState L :=
  ⟨L, 0, 1, fun _ => 2, fun _ _ => 0, 0, Fin.elim0, fun _ => (0, 0)⟩

/-- The witness state's single divisor is analytic (`t̃ = 0`). -/
theorem csWitness_divTilde_zero {L : ℕ} (hL : 0 < L) (k : Fin (csWitness L).numDiv) :
    (csWitness L).divTilde k = 0 := by
  simp only [ConState.divTilde, csWitness, tildeOf, dif_pos hL]
  exact Finset.inf'_const _ 0

/-- **The generic-`s` fold-Jacobian headline is FALSE**: for any `M` with a nonempty flat space and any
`L ≥ 1`, there is a state `s`, an atlas piece `c`, and a point `w` at which the headline's conclusion
fails. (The honest scope is `conRoot`, where `numDiv = 0` and the full fold blows up every divisor.) -/
theorem geoAtlas_fold_det_generic_false {L : ℕ} (M : Fin (L + 1) → ℕ)
    (hfd : 0 < flatDim M) (hL : 0 < L) :
    ∃ (s : ConState L) (c : LeafData M) (_hc : c ∈ geoAtlas (buildTree M (conOracle M) s)) (w : Params M),
      |(fderiv ℝ c.chartMap w).det|
        ≠ ∏ k : Fin c.numDiv, |paramsEquivFlat M w (c.divCoord k)| ^ (c.divExp k - 1) := by
  set s := csWitness L with hs
  -- `s` is terminal (`L ≤ s.layer`, since `s.layer = L`).
  have h1 : L ≤ s.layer := by rw [hs]; exact le_refl _
  have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos h1]
  -- The built tree is the single leaf `leafOfState M s`; unfold that leaf to an explicit,
  -- `leafOfState`-free structure `lstruct` (so the `Fin c.numDiv` index types carry no `leafOfState`).
  have hleaf : leafOfState M s =
      { numDiv := (t0Indices s).length, divExp := fun i => s.divExp ((t0Indices s).get i),
        cleared := s.cleared, divProfile := fun i => s.divProfile ((t0Indices s).get i),
        fullNumDiv := s.numDiv, fullDivExp := s.divExp, fullDivProfile := s.divProfile,
        numB := 0, bExp := Fin.elim0, bChain := by intro a _ _; exact a.elim0, chartMap := id,
        srcBox := ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1, resRank := 0,
        divCoord := fun i => birthFlatCoord M s ((t0Indices s).get i) hfd,
        resCoord := Fin.elim0 : LeafData M } := by
    rw [leafOfState, dif_pos hfd]
  have hbt : buildTree M (conOracle M) s = ResolutionTree.leaf (leafOfState M s) :=
    buildTree_terminal M (conOracle M) s (leafOfState M s) (leafOfState_rootLedger M s)
      (by rw [horacle]; rfl)
  rw [hleaf] at hbt
  -- `c` is that (explicit) leaf with `chartMap := id`.
  set c : LeafData M :=
      { numDiv := (t0Indices s).length, divExp := fun i => s.divExp ((t0Indices s).get i),
        cleared := s.cleared, divProfile := fun i => s.divProfile ((t0Indices s).get i),
        fullNumDiv := s.numDiv, fullDivExp := s.divExp, fullDivProfile := s.divProfile,
        numB := 0, bExp := Fin.elim0, bChain := by intro a _ _; exact a.elim0, chartMap := id,
        srcBox := ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) 1, resRank := 0,
        divCoord := fun i => birthFlatCoord M s ((t0Indices s).get i) hfd,
        resCoord := Fin.elim0 : LeafData M } with hc_def
  have hgeo : geoAtlas (buildTree M (conOracle M) s) = [c] := by
    rw [hbt]; rfl
  refine ⟨s, c, by rw [hgeo]; exact List.mem_singleton.mpr rfl, 0, ?_⟩
  -- LHS: `chartMap = id`, so the derivative determinant is `1`.
  have hlhs : |(fderiv ℝ c.chartMap (0 : Params M)).det| = 1 := by
    have hcm : c.chartMap = id := rfl
    rw [hcm, fderiv_id]
    rw [show (ContinuousLinearMap.id ℝ (Params M)).det
        = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
    simp [LinearMap.det_id]
  -- `c.numDiv = 1` (the single analytic divisor).
  have hnum : c.numDiv = 1 := by
    show (t0Indices s).length = 1
    have hmem : (⟨0, by rw [hs]; exact Nat.one_pos⟩ : Fin s.numDiv) ∈ t0Indices s :=
      (mem_t0Indices s _).mpr (csWitness_divTilde_zero hL _)
    have hle : (t0Indices s).length ≤ 1 := by
      have hle0 : (t0Indices s).length ≤ (List.finRange s.numDiv).length :=
        List.length_filter_le _ _
      rw [List.length_finRange] at hle0
      rw [hs] at hle0
      exact hle0
    have hpos : 0 < (t0Indices s).length := List.length_pos_of_mem hmem
    omega
  have hpos1 : 0 < c.numDiv := by rw [hnum]; exact Nat.one_pos
  -- The product is `0`: every factor has base `|z(0)| = 0` and index `0` has exponent `2-1 = 1 ≠ 0`.
  have hrhs : (∏ k : Fin c.numDiv, |paramsEquivFlat M (0 : Params M) (c.divCoord k)|
      ^ (c.divExp k - 1)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hpos1⟩ : Fin c.numDiv))
    have hexp : c.divExp ⟨0, hpos1⟩ = 2 := rfl
    have hz : paramsEquivFlat M (0 : Params M) (c.divCoord ⟨0, hpos1⟩) = 0 := by
      rw [← paramsEquivFlatLinear_coe]; simp
    rw [hexp, hz]; norm_num
  rw [hlhs, hrhs]; norm_num

end DLNFibre.DLN.RLCT.Engine
