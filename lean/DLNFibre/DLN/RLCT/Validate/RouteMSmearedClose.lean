import DLNFibre.DLN.RLCT.Validate.RouteMSmearedBoxSupply

/-!
# `RouteMSmearedClose` — the fully-unconditional smeared `hSmeared` ∀L (the spine slot)

Closes the two residuals between the banked smeared box supplier (`hSmeared_boxGen`,
`RouteMSmearedBoxSupply`) and the fully-unconditional boundary-smeared branch of the ∀M achiever
dispatch spine (`RouteMAchieverDispatch.routeMCore_box_diverges_achiever_spine`).

`hSmeared_boxGen` takes the STRUCTURAL DATA (`hrs`/`hr`/`hc`/`hN`/`p`/`hp` — deep split, positive
widths, ambient peel, pivot) + the width-`r` waist (`q`/`hMq`/`hwidth`) + the `minAdm` match as
hypotheses. Here that structural data is DERIVED ∀L from `BoundarySmeared M ∧ NoInteriorBothDrop M`
(with `1 ≤ minAdm M`), so no piece is carried as an open hypothesis:

* `r := deepRank M`; `s := deepRows M − deepRank M`. `hrs : r + s = M (deepLayerS).castSucc` holds
  since `M (deepLayerS).castSucc = M ⟨L−1⟩ = deepRows M` and `deepRank ≤ deepRows` (smeared).
* `0 < deepRank M` (`hr`) and `0 < M (Fin.last L)` (`hc`, via `deepLayerS_succ_width`) both follow
  from `1 ≤ minAdm M = deepRank M · M (Fin.last L)` (`minAdm_eq_deepRank_mul_last`, needs
  `NoInteriorBothDrop`).
* the waist (`q ≤ L−1`, `M ⟨q⟩ = deepRank M`, `∀ t < L, deepRank M ≤ Wext M t`) is `smeared_waist`
  (needs `NoInteriorBothDrop`). Its front-width bound at `t = 0` / `t = L−1` gives `hr0`/`hrL`.
* `routeMAmbient M > 0` (for the `n+1` peel) is `M 0 · M 1 > 0` — both `< L` for `2 ≤ L`, so
  `deepRank ≤ M 0, M 1` and `deepRank > 0` force them positive.
* the pivot `p := hN ▸ pivotCoordG …`, `hp` by the ambient round-trip cast (as at L=2).

This makes the SMEARED branch fully unconditional ∀L: `hSmeared_smearedClose` is exactly the shape
the WIDENED spine `hSmeared` slot consumes (`∀ _ : 2 ≤ L, BoundarySmeared M → NoInteriorBothDrop M →
BoxDiverges M c' ε`). Item-3 fidelity: every structural fact genuinely follows from
`BoundarySmeared ∧ NoInteriorBothDrop` (+ `1 ≤ minAdm`); nothing is assumed away.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `routeMAmbient M > 0` from two positive front widths -/

/-- **`routeMAmbient M > 0`** when the two deepest-front widths `M ⟨0⟩`, `M ⟨1⟩` are positive
(`2 ≤ L`, so `Fin L` has the index `0`, and the `s = 0` term `M ⟨0⟩ · M ⟨1⟩` of
`flatDim = ∑_s M(s.castSucc)·M(s.succ)` is positive). Widths are named as `Fin (L+1)` indices
`⟨0⟩`/`⟨1⟩` to sidestep the `(1 : Fin (L+1)).val = 1 % (L+1)` normalisation. -/
theorem routeMAmbient_pos_of_front (M : Fin (L + 1) → ℕ) (hL2 : 2 ≤ L)
    (hM0 : 0 < M (⟨0, by omega⟩ : Fin (L + 1))) (hM1 : 0 < M (⟨1, by omega⟩ : Fin (L + 1))) :
    0 < routeMAmbient M := by
  rw [routeMAmbient, flatDim_eq]
  have hLpos : 0 < L := by omega
  -- the `s = 0 : Fin L` summand
  have hz : (⟨0, hLpos⟩ : Fin L) ∈ (Finset.univ : Finset (Fin L)) := Finset.mem_univ _
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨(⟨0, hLpos⟩ : Fin L), hz, ?_⟩
  have hcast : M (⟨0, hLpos⟩ : Fin L).castSucc = M (⟨0, by omega⟩ : Fin (L + 1)) := by
    apply congrArg; apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
  have hsucc : M (⟨0, hLpos⟩ : Fin L).succ = M (⟨1, by omega⟩ : Fin (L + 1)) := by
    apply congrArg; apply Fin.ext; simp [Fin.succ]
  rw [hcast, hsucc]; exact Nat.mul_pos hM0 hM1

/-! ## The fully-unconditional smeared `hSmeared` ∀L -/

/-- **The fully-unconditional boundary-smeared `hSmeared` ∀L — the WIDENED spine slot.** For any
`M : Fin (L+1) → ℕ` with `1 ≤ minAdm M`, and any `c' ≥ ½·minAdm M`, `ε > 0`, the boundary-smeared
branch's achiever box-divergence holds in exactly the shape the dispatch spine's `hSmeared` slot
consumes:

  `(2 ≤ L) → BoundarySmeared M → NoInteriorBothDrop M → BoxDiverges M c' ε`.

All the structural data `hSmeared_boxGen` needs is DERIVED inside from `BoundarySmeared M`,
`NoInteriorBothDrop M`, and `1 ≤ minAdm M` (no open hypotheses beyond these). Drop-in for the
`hSmeared` parameter of `routeMCore_box_diverges_achiever_spine`. -/
theorem hSmeared_smearedClose (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    (2 ≤ L) → BoundarySmeared M → NoInteriorBothDrop M →
      ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  intro hL2 hsm hNo
  classical
  have hL : 0 < L := by omega
  -- the deep split `r + s = M (deepLayerS).castSucc = deepRows M`
  set r : ℕ := deepRank M with hrdef
  -- `M (deepLayerS hL).castSucc = deepRows M`
  have hcast_rows : M ((deepLayerS hL).castSucc) = deepRows M := by
    rw [deepLayerS_castSucc_width M hL, deepRows, Wext_apply M (L - 1) (by omega)]
  -- `deepRank ≤ deepRows` from BoundarySmeared, so the split closes
  have hle : deepRank M ≤ deepRows M := le_of_lt hsm.2
  set s : ℕ := deepRows M - deepRank M with hsdef
  have hrs : r + s = M ((deepLayerS hL).castSucc) := by
    rw [hcast_rows, hrdef, hsdef]; omega
  -- `minAdm = deepRank · M (last L)` (needs NoInteriorBothDrop)
  have hminadm_raw : minAdm M = deepRank M * M (Fin.last L) :=
    minAdm_eq_deepRank_mul_last M hL hNo
  -- `M (deepLayerS).succ = M (last L)`
  have hsucc_last : M ((deepLayerS hL).succ) = M (Fin.last L) := deepLayerS_succ_width M hL
  -- `0 < deepRank` (else minAdm = 0), and `0 < M (deepLayerS).succ` (= M last)
  have hr : 0 < r := by
    rw [hrdef]
    rcases Nat.eq_zero_or_pos (deepRank M) with h | h
    · exact absurd hpos (by rw [hminadm_raw, h, Nat.zero_mul]; omega)
    · exact h
  have hc : 0 < M ((deepLayerS hL).succ) := by
    rw [hsucc_last]
    rcases Nat.eq_zero_or_pos (M (Fin.last L)) with h | h
    · exact absurd hpos (by rw [hminadm_raw, h, Nat.mul_zero]; omega)
    · exact h
  -- the `minAdm` match `r · M (deepLayerS).succ = minAdm M`
  have hminadm : r * M ((deepLayerS hL).succ) = minAdm M := by
    rw [hrdef, hsucc_last, ← hminadm_raw]
  -- the width-`r` waist (needs NoInteriorBothDrop)
  obtain ⟨q, hq, hqL, hMq, hwidth⟩ := smeared_waist M hL hNo
  -- `hMq : M ⟨q, hq⟩ = deepRank M = r`
  have hMq' : M ⟨q, hq⟩ = r := by rw [hrdef]; exact hMq
  -- the front-width lower bounds at `t = 0` and `t = L − 1`
  have hr0 : r ≤ M 0 := by
    have := hwidth 0 hL
    rw [Wext_apply M 0 (by omega)] at this
    rw [hrdef]; simpa using this
  have hrL : r ≤ M (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
    have := hwidth (L - 1) (by omega)
    rw [Wext_apply M (L - 1) (by omega)] at this
    rw [hrdef]; exact this
  -- `hwidth` restated with `r`
  have hwidth' : ∀ t : ℕ, t < L → r ≤ Wext M t := by
    intro t ht; rw [hrdef]; exact hwidth t ht
  -- positive deepest-front widths ⟹ `routeMAmbient M > 0`, then peel `n + 1`
  have hM0 : 0 < M (⟨0, by omega⟩ : Fin (L + 1)) := by
    have h0 : r ≤ M (⟨0, by omega⟩ : Fin (L + 1)) := by
      have := hwidth 0 hL; rw [Wext_apply M 0 (by omega)] at this; rw [hrdef]; exact this
    exact lt_of_lt_of_le hr h0
  have hM1 : 0 < M (⟨1, by omega⟩ : Fin (L + 1)) := by
    have h1 : r ≤ M (⟨1, by omega⟩ : Fin (L + 1)) := by
      have := hwidth 1 (by omega); rw [Wext_apply M 1 (by omega)] at this; rw [hrdef]; exact this
    exact lt_of_lt_of_le hr h1
  have hambpos : 0 < routeMAmbient M := routeMAmbient_pos_of_front M hL2 hM0 hM1
  set n : ℕ := routeMAmbient M - 1 with hndef
  have hN : routeMAmbient M = n + 1 := by rw [hndef]; omega
  -- the pivot `p := hN ▸ pivotCoordG …`, with the ambient round-trip cast `hp`
  set p : Fin (n + 1) := (hN ▸ pivotCoordG M hL hrs hr hc : Fin (n + 1)) with hpdef
  have hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc := by
    rw [hpdef]
    have key : ∀ (N : ℕ) (hh : N = n + 1) (z : Fin N),
        (hh ▸ (hh ▸ z : Fin (n + 1)) : Fin N) = z := fun N hh z => by subst hh; rfl
    exact key (routeMAmbient M) hN _
  -- feed the box supplier
  exact hSmeared_boxGen M hL hrs hr hc hN p hp q hq hqL hMq' hr0 hrL hwidth' hminadm hpos c' hc' ε hε
    hL2 hsm

end DLNFibre.DLN.RLCT
