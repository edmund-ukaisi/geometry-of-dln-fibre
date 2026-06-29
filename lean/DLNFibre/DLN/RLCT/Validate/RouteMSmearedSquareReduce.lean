import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareL2
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedAchieverGeneral

/-!
# `RouteMSmearedSquareReduce` — the smeared branch reduces to the SQUARE case (`r = M 0`) at L=2

The closing wiring of the BOUNDARY-SMEARED branch of the R1-LOWER generic achiever leg. Two facts,
both at L=2:

* **The square reduction** `smeared_deepRank_eq_M0` — in the regime the dispatch spine actually
  invokes the smeared branch, `1 ≤ minAdm M ∧ BoundarySmeared M`, the deepest rank block is SQUARE:
  `deepRank M = M 0` (with `0 < deepRank M`, `0 < M 2`). Reason: at L=2 `InteriorDrop M ⟺ M 2 > 0 ∧
  deepRank M < M 0 ∧ deepRank M < M 1`; `BoundarySmeared` is `¬InteriorDrop ∧ deepRank < deepRows =
  M 1`, and `1 ≤ minAdm` forces `M 0, M 1, M 2 ≥ 1`, so `¬InteriorDrop ∧ deepRank < M 1 ∧ M 2 > 0`
  forces `deepRank ≥ M 0`; with `deepRank ≤ min(M 0, M 1) ≤ M 0` this gives `deepRank = M 0`. The
  NON-square smeared chart-builder is thereby UNNEEDED at L=2 (it never arises in the regime).

* **The chart builder** `smearedChart_of_square` / `smearedAchieverChart_L2` — assembles the banked
  fully-unconditional square box-divergence `routeMCore_smearedL2_square_uncond`
  into a `SmearedAchieverChart M` (the M-agnostic bundle of `RouteMSmearedAchieverGeneral`), feeding
  the spine's `hSmeared` via `hSmeared_of_smearedChart`.

This CLOSES `hSmeared` ∀M at L=2 — not merely reduces it. The heavy opaque-width machinery (the slot
equiv `slotEquiv`, the decode `decode_params`, `ψ` MP + measurable embedding, the radial `Rmap`, the
diagonal-dominance Gram det, the Varah field-A bound) is all banked sorry-free in
`RouteMSmearedDecodeL2` / `RouteMSmearedSquareL2`; this file is the reduction + the bundle assembly.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## The L=2 `InteriorDrop` / `minAdm` arithmetic (P1 — the square reduction) -/

/-- The reduced-chain leaf value at L=2: `minAdmRec (redChain t M) = t · M 2` (the `Fin 2` leaf
`(redChain t M) 0 · (redChain t M) 1`, with `redChain t M 0 = t`, `redChain t M 1 = M 2`). -/
theorem minAdmRec_redChain_L2 (t : ℕ) (M : Fin 3 → ℕ) :
    minAdmRec (redChain t M) = t * M 2 := by
  rw [minAdmRec_leaf, redChain_zero]; congr 1

/-- **`1 ≤ minAdm M` forces all three widths positive** at L=2: `0 < M 0`, `0 < M 1`, `0 < M 2`.
If any were `0`, an admissible `T` zeroes `Mval` (`T0 = 0` kills `M0`/`M1`; `T0 = min(M0,M1)` with
`M2 = 0` kills both factors), so `minAdm = 0`. -/
theorem widths_pos_of_minAdm (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M) :
    0 < M 0 ∧ 0 < M 1 ∧ 0 < M 2 := by
  -- unfold `minAdm` to the layer-peeling min over `t ∈ [0, min(M0,M1)]`
  rw [← minAdmRec_eq_minAdm, minAdmRec_succ_succ] at hpos
  set F : ℕ → ℕ := fun t => (M 0 - t) * (M 1 - t) + minAdmRec (redChain t M) with hF
  have hcell : ∀ t, F t = (M 0 - t) * (M 1 - t) + t * M 2 := fun t => by
    rw [hF]; simp only []; rw [minAdmRec_redChain_L2 t M]
  have hF0 : F 0 = M 0 * M 1 := by rw [hcell 0]; simp
  have hposInf : 1 ≤ (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp) F := hpos
  -- the `t = 0` cell witness: `inf' ≤ M 0 · M 1`
  have hmem0 : (0 : ℕ) ∈ Finset.range (min (M 0) (M 1) + 1) := by rw [Finset.mem_range]; omega
  have hle0 : (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp) F ≤ M 0 * M 1 := by
    rw [← hF0]; exact Finset.inf'_le _ hmem0
  -- the `t = min(M0,M1)` cell witness: block term `= 0`, so `inf' ≤ min(M0,M1)·M2`
  have hmemMin : min (M 0) (M 1) ∈ Finset.range (min (M 0) (M 1) + 1) := by
    rw [Finset.mem_range]; omega
  have hleMin : (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp) F
      ≤ (M 0 - min (M 0) (M 1)) * (M 1 - min (M 0) (M 1)) + min (M 0) (M 1) * M 2 := by
    rw [← hcell (min (M 0) (M 1))]; exact Finset.inf'_le _ hmemMin
  have hblk : (M 0 - min (M 0) (M 1)) * (M 1 - min (M 0) (M 1)) = 0 := by
    rcases Nat.le_total (M 0) (M 1) with h | h
    · have : M 0 - min (M 0) (M 1) = 0 := by omega
      rw [this, Nat.zero_mul]
    · have : M 1 - min (M 0) (M 1) = 0 := by omega
      rw [this, Nat.mul_zero]
  rw [hblk, Nat.zero_add] at hleMin
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (M 0) with h | h
    · have hprod : M 0 * M 1 = 0 := by rw [h]; ring
      omega
    · exact h
  · rcases Nat.eq_zero_or_pos (M 1) with h | h
    · have hprod : M 0 * M 1 = 0 := by rw [h]; ring
      omega
    · exact h
  · rcases Nat.eq_zero_or_pos (M 2) with h | h
    · have hprod : min (M 0) (M 1) * M 2 = 0 := by rw [h]; ring
      omega
    · exact h

/-- **The L=2 `InteriorDrop` characterization** `InteriorDrop M ⟺ 0 < M 2 ∧ deepRank M < M 0 ∧
deepRank M < M 1`. (`p = 1` is the only interior boundary; `Text(2) = deepRank`, `Text(1) = M 0`,
`Wext(1) = M 1`, `Wext(2) = M 2`.) -/
theorem interiorDrop_L2_iff (M : Fin 3 → ℕ) :
    InteriorDrop M ↔ (0 < M 2 ∧ deepRank M < M 0 ∧ deepRank M < M 1) := by
  have hWL : Wext M 2 = M 2 := Wext_apply M 2 (by omega)
  have hdeep : Text M (tach M) 2 = deepRank M := rfl
  have hText1 : Text M (tach M) 1 = M 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Text_succ M (tach M) 0 (by omega)]
    exact tach_mk_zero M (by omega)
  have hWext1 : Wext M 1 = M 1 := Wext_apply M 1 (by omega)
  rw [InteriorDrop]
  constructor
  · rintro ⟨hWLpos, p, hp1, hpL, hdrop, htail⟩
    -- `p < L = 2` and `1 ≤ p` force `p = 1` (the only interior boundary)
    have hp : p = 1 := by omega
    subst hp
    rw [hWL] at hWLpos
    rw [show (1 : ℕ) + 1 = 2 from rfl, hdeep, hText1] at hdrop
    have htb := htail 1 (le_refl 1) (by omega)
    rw [show (1 : ℕ) + 1 = 2 from rfl, hdeep, hWext1] at htb
    exact ⟨hWLpos, hdrop, htb⟩
  · rintro ⟨hM2, hlt0, hlt1⟩
    refine ⟨by rw [hWL]; exact hM2, 1, le_refl 1, by omega, ?_, ?_⟩
    · rw [show (1 : ℕ) + 1 = 2 from rfl, hdeep, hText1]; exact hlt0
    · intro b hb1 hbL
      have hb : b = 1 := by omega
      subst hb
      rw [show (1 : ℕ) + 1 = 2 from rfl, hdeep, hWext1]; exact hlt1

/-- **`deepRank M ≤ M 0`** at L=2 (the achiever rank is bounded by the front width, via the
`admBound 0 = min(M 0, M 1)` bound). -/
theorem deepRank_le_M0 (M : Fin 3 → ℕ) : deepRank M ≤ M 0 := by
  rw [deepRank]
  -- `Text M (tach M) 2 = Text(1+1) = tach M ⟨1⟩ = tStar M ⟨0⟩`
  rw [show Text M (tach M) 2 = Text M (tach M) (1 + 1) from rfl, Text_succ M (tach M) 1 (by omega)]
  rw [show (⟨1, by omega⟩ : Fin 3) = (⟨0 + 1, by omega⟩ : Fin (2 + 1)) from rfl,
    tach_mk_succ M 0 (by omega)]
  -- `tStar M ⟨0⟩ ≤ admBound M ⟨0⟩ = min (M 0) (M 1) ≤ M 0`
  obtain ⟨hbound, _, _⟩ := (Finset.mem_filter.1 (tStar_mem M)).2
  have hb := hbound (⟨0, by omega⟩ : Fin 2)
  rw [admBound, if_pos (rfl : (⟨0, by omega⟩ : Fin 2).val = 0)] at hb
  exact le_trans hb (min_le_left _ _)

/-- **The SQUARE reduction.** In the spine's smeared regime (`1 ≤ minAdm M ∧ BoundarySmeared M`),
the deepest rank block is square: `deepRank M = M 0`, with `0 < deepRank M` and `0 < M 2`. -/
theorem smeared_deepRank_eq_M0 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M) (hsm : BoundarySmeared M) :
    deepRank M = M 0 ∧ 0 < deepRank M ∧ 0 < M 2 := by
  obtain ⟨hM0, hM1, hM2⟩ := widths_pos_of_minAdm M hpos
  obtain ⟨hbdry, hlt⟩ := hsm
  -- `deepRows M = M 1` at L=2
  have hrows : deepRows M = M 1 := by
    rw [deepRows]; exact Wext_apply M (2 - 1) (by omega) |>.trans (by norm_num)
  rw [hrows] at hlt
  -- `¬InteriorDrop ∧ deepRank < M 1 ∧ 0 < M 2 ⟹ ¬(deepRank < M 0)` ⟹ `deepRank ≥ M 0`
  have hge : M 0 ≤ deepRank M := by
    by_contra hlt0
    rw [not_le] at hlt0
    exact hbdry ((interiorDrop_L2_iff M).mpr ⟨hM2, hlt0, hlt⟩)
  have hle := deepRank_le_M0 M
  exact ⟨le_antisymm hle hge, by omega, hM2⟩

/-! ## The chart builder (P2 — assemble the square box-divergence into `SmearedAchieverChart M`) -/

/-- **`minAdm M = M 0 · M 2` on the square slice** (`deepRank M = M 0`). The achiever path's leading
exponent is `tStar 0 = deepRank = M 0` and its last is `tStar 1 = 0`, so `Mval M (tStar M)`
collapses to `(M0−M0)(M1−M0) + (M0−0)(M2−0) = M0·M2`; `Mval (tStar) = minAdm` gives equality. -/
theorem minAdm_eq_M0_mul_M2 (M : Fin 3 → ℕ) (hr0 : deepRank M = M 0) : minAdm M = M 0 * M 2 := by
  have hstar0 : tStar M (⟨0, by omega⟩ : Fin 2) = M 0 := by
    have hd : deepRank M = tStar M (⟨0, by omega⟩ : Fin 2) := by
      rw [deepRank, show Text M (tach M) 2 = Text M (tach M) (1 + 1) from rfl,
        Text_succ M (tach M) 1 (by omega),
        show (⟨1, by omega⟩ : Fin 3) = (⟨0 + 1, by omega⟩ : Fin (2 + 1)) from rfl,
        tach_mk_succ M 0 (by omega)]
    rw [← hd, hr0]
  have hstar1 : tStar M (⟨1, by omega⟩ : Fin 2) = 0 := by
    obtain ⟨_, _, hlast⟩ := (Finset.mem_filter.1 (tStar_mem M)).2
    exact hlast (⟨1, by omega⟩ : Fin 2) (by norm_num)
  have hs0 : tStar M (0 : Fin 2) = M 0 := hstar0
  have hs1 : tStar M (1 : Fin 2) = 0 := hstar1
  have hmval : Mval M (tStar M) = (M 0 : ℤ) * (M 2 : ℤ) := by
    rw [Mval, Fin.sum_univ_two]
    have hM1 : M (0 : Fin 2).succ = M 1 := by congr 1
    have hM2 : M (1 : Fin 2).succ = M 2 := by congr 1
    have htp0 : tPrev M (tStar M) (0 : Fin 2) = (M 0 : ℤ) := by simp [tPrev]
    have htp1 : tPrev M (tStar M) (1 : Fin 2) = (M 0 : ℤ) := by
      rw [tPrev, if_neg (by decide)]
      have hidx : (⟨(1 : Fin 2).val - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
        apply Fin.ext; simp
      rw [show (Nat.cast (tStar M ⟨(1 : Fin 2).val - 1, by omega⟩) : ℤ)
          = (tStar M (0 : Fin 2) : ℤ) from by rw [hidx], hs0]
    rw [hM1, hM2, hs0, hs1, htp0, htp1]; push_cast; ring
  have heq := Mval_tStar_eq M
  rw [hmval] at heq
  have : (minAdm M : ℤ) = ((M 0 * M 2 : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast this

/-- **`routeMAmbient M > 0`** at L=2 with positive front widths (`flatDim ≥ M0·M1 ≥ 1`). Peels the
ambient into `n + 1`. -/
theorem routeMAmbient_pos (M : Fin 3 → ℕ) (hM0 : 0 < M 0) (hM1 : 0 < M 1) :
    0 < routeMAmbient M := by
  rw [routeMAmbient, flatDim_eq, Fin.sum_univ_two]
  have h0 : M (0 : Fin 2).castSucc * M (0 : Fin 2).succ = M 0 * M 1 := by congr 1
  rw [h0]; have : 0 < M 0 * M 1 := Nat.mul_pos hM0 hM1; omega

/-- Each conditioned box interval `condBoxWidth M hrs hr0 δ η m` (an `Icc`, either `[δ/2,δ]` or
`[−η,η]`) has positive Lebesgue measure for `δ, η > 0`. -/
theorem condBoxWidth_volume_pos {r s : ℕ} (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (m : Fin (routeMAmbient M)) :
    0 < (volume : Measure ℝ) (condBoxWidth M hrs hr0 δ η m) := by
  unfold condBoxWidth slotBox
  split
  · rw [Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  · rw [Real.volume_Icc, ENNReal.ofReal_pos]; linarith

set_option maxHeartbeats 400000 in
-- The structure assembly unifies ~16 fields against the dependent `condBoxWidth`/`Fin.insertNth`
-- ambient casts; the `whnf` cost of that field-type checking exceeds the default heartbeat budget.
/-- **The smeared chart from the square case.** For `M : Fin 3 → ℕ` in the spine's smeared regime, a
`SmearedAchieverChart M` built from the banked fully-unconditional square box-divergence. The
ε-independent maps are the generic `psiMap`/`Rmap`/`Dmap` (MP + embedding + radial det
`|u_p|^(r·M2−1)`); the pivot is the peeled `pivotCoord`, the radial exponent `r·M2 − 1`
(`= minAdm M − 1`, since `minAdm M = M0·M2 = r·M2` on the square slice). The per-ε data uses the
conditioned box `condBoxWidth` with radius `δ = min(ε/2, 1)`, width `η = δ/(4r+4s+4)`, margin
`γ = δ/4` — the margins
`(r−1)η + γ ≤ δ/2`, `η ≤ δ`, `η ≤ 1`, `s·((1/γ)η)·η ≤ δ` all hold; the analytic fields (field-A
containment, the peeled rate, `U`-positivity) are discharged from the banked `RouteMSmearedSquareL2`
components. -/
noncomputable def smearedChart_of_square (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M)
    (hsm : BoundarySmeared M) : SmearedAchieverChart M := by
  obtain ⟨hdeq, hdpos, hM2⟩ := smeared_deepRank_eq_M0 M hpos hsm
  obtain ⟨hM0, hM1, _⟩ := widths_pos_of_minAdm M hpos
  -- the square data: `r = deepRank = M0`, `s = M1 − r`
  set r : ℕ := deepRank M with hrdef
  have hr0 : r = M 0 := hdeq
  have hr : 0 < r := hdpos
  have hc : 0 < M 2 := hM2
  have hrM1 : r < M 1 := by
    have hlt := hsm.2
    have hrows : deepRows M = M 1 := by
      rw [deepRows]; exact (Wext_apply M (2 - 1) (by omega)).trans (by norm_num)
    rw [hrows] at hlt; exact hlt
  set s : ℕ := M 1 - r with hsdef
  have hrs : r + s = M 1 := by omega
  -- `minAdm = r · M2` on the square slice
  have hminAdm : minAdm M = r * M 2 := by
    have := minAdm_eq_M0_mul_M2 M (hrdef ▸ hr0)
    rw [this, hr0]
  -- peel the ambient into `n + 1`
  have hambpos : 0 < routeMAmbient M := routeMAmbient_pos M hM0 hM1
  set n : ℕ := routeMAmbient M - 1 with hndef
  have hN : routeMAmbient M = n + 1 := by rw [hndef]; omega
  refine
    { n := n
      hN := hN
      ψ := psiMap M hrs
      R := Rmap M hrs hr hc
      D := Dmap M hrs hr hc
      p := (hN ▸ pivotCoord M hrs hr hc : Fin (n + 1))
      h := r * M 2 - 1
      hmp := measurePreserving_psiMap M hrs
      hemb := measurableEmbedding_psiMap M hrs
      hexp := ?_
      data := ?_ }
  · -- `hexp`: `(r·M2 − 1 : ℝ) − 2·(minAdm/2) ≤ −1`, with `minAdm = r·M2`
    rw [hminAdm]
    have hge1 : 1 ≤ r * M 2 := by rw [← hminAdm]; exact hpos
    rw [Nat.cast_sub hge1]
    push_cast
    linarith
  · -- the per-ε δ-dependent data
    intro ε hε
    -- the round-trip cast `hN ▸ p = pivotCoord`
    have hp : (hN ▸ (hN ▸ pivotCoord M hrs hr hc : Fin (n + 1)) : Fin (routeMAmbient M))
        = pivotCoord M hrs hr hc := by
      have key : ∀ (N : ℕ) (hh : N = n + 1) (z : Fin N),
          (hh ▸ (hh ▸ z : Fin (n + 1)) : Fin N) = z := fun N hh z => by subst hh; rfl
      exact key (routeMAmbient M) hN _
    -- box widths
    set δ : ℝ := min (ε / 2) 1 with hδdef
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have h2δε : 2 * δ ≤ ε := by have : δ ≤ ε / 2 := min_le_left _ _; linarith
    set K : ℝ := 4 * r + 4 * s + 4 with hKdef
    set η : ℝ := δ / K with hηdef
    set γ : ℝ := δ / 4 with hγdef
    have hr0' : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hs0' : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    have hK4 : (4 : ℝ) ≤ K := by rw [hKdef]; linarith
    have hKpos : 0 < K := by linarith
    have hγpos : 0 < γ := by rw [hγdef]; linarith
    have hηpos : 0 ≤ η := by rw [hηdef]; positivity
    -- the four box margins
    have hη : η ≤ δ := by rw [hηdef, div_le_iff₀ hKpos]; nlinarith
    have hη1 : η ≤ 1 := by rw [hηdef, div_le_one hKpos]; nlinarith
    have hmargin : ((r - 1 : ℕ) : ℝ) * η + γ ≤ δ / 2 := by
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub hr]; push_cast; ring
      rw [hcast, hηdef, hγdef]
      have hKge : (4 : ℝ) * ((r : ℝ) - 1) ≤ K := by rw [hKdef]; linarith
      have key : ((r : ℝ) - 1) * (δ / K) ≤ δ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 4)]
        nlinarith [mul_nonneg hr0' hδ.le, hKge, hδ]
      linarith
    have hfieldA : (s : ℝ) * ((1 / γ) * η) * η ≤ δ := by
      rw [hηdef, hγdef]
      have h4 : (1 : ℝ) / (δ / 4) = 4 / δ := by field_simp
      rw [h4]
      have hKK : (4 : ℝ) * s ≤ K ^ 2 := by
        have h1 : (4 : ℝ) * s + 4 ≤ K := by rw [hKdef]; linarith
        nlinarith [h1, hs0']
      rw [show (s : ℝ) * (4 / δ * (δ / K)) * (δ / K) = 4 * s * δ / K ^ 2 from by field_simp]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hKK, hδ]
    -- the double-cast box collapse: `(fun k => box (hN ▸ k)) = condBoxWidth …`
    have hboxeq : (fun k : Fin (routeMAmbient M) =>
        condBoxWidth M hrs hr0 δ η (hN ▸ (hN ▸ k : Fin (n + 1)) : Fin (routeMAmbient M)))
          = condBoxWidth M hrs hr0 δ η :=
      funext (fun k => condBoxWidth_double_cast M hrs hr0 δ η hN k)
    -- the conditioned box (ambient) `= condBox pivotCoord (condBoxWidth) δ`
    have hcondeq : condBox (hN ▸ (hN ▸ pivotCoord M hrs hr hc : Fin (n + 1))
            : Fin (routeMAmbient M))
          (fun k => condBoxWidth M hrs hr0 δ η (hN ▸ (hN ▸ k : Fin (n + 1))
            : Fin (routeMAmbient M))) δ
        = condBox (pivotCoord M hrs hr hc) (condBoxWidth M hrs hr0 δ η) δ := by
      rw [hp, hboxeq]
    refine
      { δ := δ
        box := fun m => condBoxWidth M hrs hr0 δ η (hN ▸ m)
        Uy := fun y =>
          Uunit M hrs hr hc (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) (0 : ℝ) y))
        hδ := hδ
        hSpre := ?_
        hRderiv := ?_
        hRinj := ?_
        hRdet := ?_
        hboxmeas := ?_
        hboxmeasAll := ?_
        hboxpos := ?_
        hUmeas := ?_
        hRate := ?_
        hUpos := ?_ }
    · -- FIELD A: `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)` (via `cubeBox 2δ ⊆ cubeBox ε`)
      rw [hcondeq]
      refine fun u hu => cubeBox_mono h2δε ?_
      exact condBox_subset_preimage M hrs hr0 hr hc δ η γ hδ hγpos hη hη1 hηpos hmargin hfieldA hu
    · -- `R` has fderiv `D` on the box
      rw [hcondeq]
      exact fun u _ => Rmap_hasFDerivWithinAt M hrs hr hc _ u
    · -- `R` injective on the box (pivot `∈ Ioo 0 δ` so `≠ 0`)
      rw [hcondeq]
      have hsub : condBox (pivotCoord M hrs hr hc) (condBoxWidth M hrs hr0 δ η) δ
          ⊆ Set.univ \ {x | x (pivotCoord M hrs hr hc) = 0} := by
        intro u hu
        refine ⟨Set.mem_univ u, ?_⟩
        obtain ⟨hpiv, _⟩ := hu
        simp only [Set.mem_setOf_eq]; exact ne_of_gt (Set.mem_Ioo.mp hpiv).1
      exact (Rmap_injOn M hrs hr hc Set.univ).mono hsub
    · -- `|det (D u)| = |u (hN ▸ p)|^(r·M2−1)`
      rw [hcondeq]
      intro u _
      rw [Dmap_abs_det M hrs hr hc, hp]
    · -- each non-pivot box interval measurable
      exact fun k => measurableSet_condBoxWidth M hrs hr0 δ η _
    · -- every box coordinate interval measurable
      exact fun k => measurableSet_condBoxWidth M hrs hr0 δ η _
    · -- the conditioned rest box has positive measure
      have hηpos' : 0 < η := by rw [hηdef]; positivity
      rw [volume_pi_pi]
      exact CanonicallyOrderedAdd.prod_pos.mpr
        (fun k _ => condBoxWidth_volume_pos M hrs hr0 δ η hδ hηpos' _)
    · -- `Uy` measurable (`Uunit` a polynomial in the non-pivot coords)
      have hins : Measurable (fun y : Fin n → ℝ =>
          (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) (0 : ℝ) y)
            : Fin (routeMAmbient M) → ℝ)) := by
        have key : ∀ (N : ℕ) (hh : N = n + 1),
            Measurable (fun y : Fin n → ℝ =>
              (hh ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) (0 : ℝ) y) : Fin N → ℝ)) := by
          intro N hh; subst hh
          exact measurable_pi_iff.2 (fun i => by
            rcases Fin.eq_self_or_eq_succAbove (hN ▸ pivotCoord M hrs hr hc) i with rfl | ⟨k, rfl⟩
            · simp only [Fin.insertNth_apply_same]; exact measurable_const
            · simp only [Fin.insertNth_apply_succAbove]; exact measurable_pi_apply k)
        exact key _ hN
      exact (measurable_Uunit M hrs hr hc).comp hins
    · -- the PEELED RATE `routeMCore (ψ (R (hN ▸ insertNth p z y))) = z²·Uy y`
      intro z hz y hy
      have hmem : (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) z y)
          : Fin (routeMAmbient M) → ℝ)
            ∈ condBox (pivotCoord M hrs hr hc) (condBoxWidth M hrs hr0 δ η) δ := by
        refine insertNth_mem_condBox M hrs hr0 hr hc δ η hN
          (hN ▸ pivotCoord M hrs hr hc) hp hz (fun k => ?_)
        have := hy k
        simpa only [Set.mem_pi, Set.mem_univ, true_implies] using this
      have hcancel : P1u M hrs (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) z y))
            * Lam0u M hrs (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) z y))
          = P2u M hrs (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) z y)) :=
        Lam0u_cancel_of_box M hrs hr0 hr hc δ η γ hδ hγpos hmargin
          (rest_of_condBox M hrs hr0 hr hc δ η hmem)
      rw [routeMCore_psiMap_Rmap M hrs hr hc _ hcancel,
        zu_hN_insertNth M hrs hr hc hN (hN ▸ pivotCoord M hrs hr hc) hp z y,
        Uunit_hN_insertNth M hrs hr hc hN (hN ▸ pivotCoord M hrs hr hc) hp z y]
    · -- `U`-positivity on the box (the `z = δ/2` rest membership, `z`-free transport)
      intro y hy
      have hδ2 : (δ / 2) ∈ Set.Ioo (0 : ℝ) δ := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have hmem : (hN ▸ (Fin.insertNth (hN ▸ pivotCoord M hrs hr hc) (δ / 2) y)
          : Fin (routeMAmbient M) → ℝ)
            ∈ condBox (pivotCoord M hrs hr hc) (condBoxWidth M hrs hr0 δ η) δ := by
        refine insertNth_mem_condBox M hrs hr0 hr hc δ η hN
          (hN ▸ pivotCoord M hrs hr hc) hp hδ2 (fun k => ?_)
        have := hy k
        simpa only [Set.mem_pi, Set.mem_univ, true_implies] using this
      have hrest2 := rest_of_condBox M hrs hr0 hr hc δ η hmem
      have hagree := hN_insertNth_agree_off_pivot M hrs hr hc hN
        (hN ▸ pivotCoord M hrs hr hc) hp (δ / 2) y
      refine Uunit_pos_of_box M hrs hr0 hr hc δ η γ hδ hγpos hmargin (fun k hk => ?_)
      rw [← hagree k hk]
      exact hrest2 k hk

/-! ## The spine-feeding closer (`hSmeared` ∀M at L=2, OUTRIGHT) -/

/-- **`hSmeared` ∀M at L=2 — CLOSED.** For any `M : Fin 3 → ℕ` with `1 ≤ minAdm M`, and any `c'` at
or above the achiever threshold `½·minAdm M`, the BOUNDARY-SMEARED branch's achiever box-divergence
holds: `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`, every `ε > 0`. The square reduction
(`smeared_deepRank_eq_M0`: `deepRank M = M 0`) routes the smeared branch entirely through the
fully-built square chart `smearedChart_of_square`, fed to the M-agnostic
`routeMCore_box_diverges_of_smearedChart`. This is exactly the shape the dispatch spine's `hSmeared`
slot consumes (`RouteMAchieverDispatch.routeMCore_box_diverges_achiever_spine`); composing it with
the `2 ≤ L` gate closes the SMEARED branch ∀M at L=2 outright. -/
theorem hSmeared_squareSmeared_L2 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε)
    (hsm : BoundarySmeared M) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_smearedChart M (smearedChart_of_square M hpos hsm) c' hc' ε hε

end DLNFibre.DLN.RLCT
