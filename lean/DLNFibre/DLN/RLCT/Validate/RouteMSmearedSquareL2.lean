import DLNFibre.DLN.RLCT.Validate.RouteMSmearedDecodeL2
import DLNFibre.Core.Matrix.DiagDominance

/-!
# `RouteMSmearedSquareL2` — discharging the two analytic hypotheses on the smeared L=2 stratum

The smeared L=2 stratum (`certificate-smeared-l2-two-facts.md`, decorrelated p&p + Codex) is exactly
`M0 < M1` with the front-bottleneck split `r = min(M0,M1) = M0`, so the rank-block front matrix `P₁` is
**square** (`M0 × M0`). This file discharges, on the square slice `r = M0`, the two genuinely-analytic
hypotheses the chart assembly `routeMCore_smearedL2` left open:

* **`hcancel` (Fact 1, off-pole cancellation)** — `P₁·Λ₀ = P₂`. For a square invertible `P₁`,
  `K := P₁⁻¹·P₂` factors `P₂ = P₁·K`, and `det(P₁ᵀP₁) = (det P₁)² ≠ 0`; the banked
  `Lam0u_cancel_of_factoring` then fires. The single input is `det P₁ ≠ 0`.

The invertibility input `det P₁ ≠ 0` is supplied UNCONDITIONALLY on a conditioned box via strict row
diagonal dominance (`Core.Matrix.StrictRowDominant.det_ne_zero`, Levy–Desplanques) — not merely a.e.
The per-`r` off-diagonal box width `η = δ/(4(r−1))` (Codex scope catch: a fixed `δ/8` is singular for
`r ≥ 5`) gives the margin `γ = δ/4 > 0`.

SCOPE (load-bearing, honored): Fact 1 is FALSE for the free front `A0u` at `r < M0` (the cancellation
needs `col(P₂) ⊆ col(P₁)`, which a free tall `P₁` does not give). So the cancellation here is proved on
the SQUARE slice `r = M0` only, which is the ENTIRE genuine smeared L=2 stratum — there is no smeared
L=2 configuration with `s > 0` and a tall `P₁`.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin 3 → ℕ} {r s : ℕ}

/-! ## Fact 1: the off-pole cancellation from a square invertible `P₁` (stratum `r = M 0`)

`det P1u` is well-typed only when `P1u` is square (`r = M 0`). Since the statement is elaborated before
any `subst`, the input is supplied as `hr0 : r = M 0` plus the Gram det `det(P1uᵀP1u) ≠ 0` (the Gram is
square `Fin r` for any `r`) — the unconditional-on-the-box dominance lemma will produce both. -/

/-- **The square-slice column factoring `∃ K, P₂ = P₁·K`.** On `r = M 0` the front rank block `P1u` is
square; given the Gram `det(P1uᵀP1u) ≠ 0`, `P1u` is invertible (`det(P1uᵀP1u) = (det P1u)²`), so
`K := P1u⁻¹·P2u` factors `P₂ = P₁·K` (the column space of `P₁` is everything). -/
theorem P2u_factorsThrough_P1u_of_gram (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (u : Fin (routeMAmbient M) → ℝ)
    (hgram : ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0) :
    ∃ K : Matrix (Fin r) (Fin s) ℝ, P2u M hrs u = P1u M hrs u * K := by
  -- `r = M 0` makes `P1u` genuinely square; `subst` so `det`/`⁻¹` apply directly
  subst hr0
  -- `det P1u ≠ 0` from `det(P1uᵀP1u) = (det P1u)² ≠ 0`
  have hdet : (P1u M hrs u).det ≠ 0 := by
    intro h0
    apply hgram
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
  have hunit : IsUnit (P1u M hrs u).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨(P1u M hrs u)⁻¹ * P2u M hrs u, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]

/-- **The square-slice off-pole cancellation `P₁·Λ₀ = P₂`.** Combines the column factoring
(`P2u_factorsThrough_P1u_of_gram`, needs `r = M 0` + Gram invertible) with the banked
`Lam0u_cancel_of_factoring`. The genuinely-analytic Fact 1 of `routeMCore_smearedL2`, on the stratum. -/
theorem Lam0u_cancel_of_gram_square (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (u : Fin (routeMAmbient M) → ℝ)
    (hgram : ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0) :
    P1u M hrs u * Lam0u M hrs u = P2u M hrs u := by
  obtain ⟨K, hK⟩ := P2u_factorsThrough_P1u_of_gram M hrs hr0 u hgram
  exact Lam0u_cancel_of_factoring M hrs u K hK hgram

/-! ## The Gram det from strict row diagonal dominance of `P₁` (the box-unconditional off-pole input)

`det(P1uᵀP1u) = (det P1u)²`, and on the square slice a strictly-row-diagonally-dominant `P1u` has
`det P1u ≠ 0` (Levy–Desplanques, `Core.Matrix.StrictRowDominant.det_ne_zero`). The dominance hypothesis
is the box-membership readoff (the conditioning `|P1u_ii| ≥ δ/2`, off-diagonals `≤ η = δ/(4(r−1))`,
margin `γ = δ/4`). The dominance condition is phrased entrywise, well-typed for any `r`, and `subst hr0`
makes `P1u` genuinely square so `StrictRowDominant` applies. -/

open DLNFibre.Core.Matrix in
/-- **Square `P₁` diagonal dominance ⟹ Gram det `≠ 0`.** Given `r = M 0` (square `P1u`) and the strict
row-diagonal-dominance margin (`∑_{a≠i}|P1u i a| + γ ≤ |P1u i i|`, `γ > 0`), the Gram `det(P1uᵀP1u) ≠ 0`.
`det(P1uᵀP1u) = (det P1u)²`, `det P1u ≠ 0` by Levy–Desplanques. -/
theorem gram_det_ne_of_diagDominant (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (u : Fin (routeMAmbient M) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hdom : ∀ i : Fin (M 0),
      (∑ a ∈ Finset.univ.erase (Fin.cast hr0.symm i), |P1u M hrs u i a|) + γ
        ≤ |P1u M hrs u i (Fin.cast hr0.symm i)|) :
    ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0 := by
  -- eliminate `r` in favour of `M 0` (`subst` the variable `r`); `Fin.cast rfl` collapses to `id`
  subst hr0
  simp only [Fin.cast_eq_self] at hdom
  -- assemble `StrictRowDominant (P1u) γ`, get `det P1u ≠ 0`, then the Gram
  have hdd : StrictRowDominant (P1u M hrs u) γ := ⟨hγ, hdom⟩
  have hdet : (P1u M hrs u).det ≠ 0 := hdd.det_ne_zero
  rw [Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero hdet hdet

/-! ## The conditioned box (slot-classified) and the `P₁` diagonal-dominance readoff

Per the `(2,3,1)` shape generalized to opaque widths: the rank-block diagonal front coords pinned in
`[δ/2, δ]`, every other (non-pivot) coord in `[−η, η]`. Following the cleanest design (decorrelated
Codex), the classification is on `FlatIdx M` (the slot), precomposed with `slotEquiv` — so the readoff
is slot-level (`coordOf q ↦ slotBox q`), avoiding repeated `coordOf`-injectivity work. The box is
parameterized by an arbitrary width `η > 0` and the dominance is gated by a margin hypothesis
`(↑(r−1))·η + γ ≤ δ/2`, robust for all `r ≥ 1` (no `δ/(4(r−1))` divide-by-zero). -/

/-- The diagonal front slots `frontSlot i (deepWidthEquiv (inl i))` (`r = M 0`, so `i : Fin (M 0)`
indexes both the row and the rank-block column via the `Fin.cast hr0.symm`). -/
noncomputable def p1DiagSlots (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) :
    Finset (FlatIdx M) :=
  Finset.image
    (fun i : Fin (M 0) => frontSlot M i (deepWidthEquiv hrs (Sum.inl (Fin.cast hr0.symm i))))
    Finset.univ

/-- The slot-level box: `[δ/2, δ]` on a rank-block diagonal front slot, `[−η, η]` elsewhere. -/
noncomputable def slotBox (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (δ η : ℝ)
    (q : FlatIdx M) : Set ℝ :=
  if q ∈ p1DiagSlots M hrs hr0 then Set.Icc (δ / 2) δ else Set.Icc (-η) η

/-- The ambient conditioned box width: `slotBox` precomposed with `slotEquiv`. -/
noncomputable def condBoxWidth (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (δ η : ℝ) :
    Fin (routeMAmbient M) → Set ℝ :=
  fun m => slotBox M hrs hr0 δ η (slotEquiv M m)

/-- The slot-level readoff: `condBoxWidth (coordOf q) = slotBox q` (the `slotEquiv (coordOf q) = q`
round-trip). -/
theorem condBoxWidth_coordOf (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (δ η : ℝ)
    (q : FlatIdx M) :
    condBoxWidth M hrs hr0 δ η (coordOf M q) = slotBox M hrs hr0 δ η q := by
  unfold condBoxWidth coordOf
  rw [Equiv.apply_symm_apply]

/-- Each box width is measurable (both branches `Icc`). -/
theorem measurableSet_condBoxWidth (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (δ η : ℝ)
    (m : Fin (routeMAmbient M)) : MeasurableSet (condBoxWidth M hrs hr0 δ η m) := by
  unfold condBoxWidth slotBox
  split <;> exact measurableSet_Icc

/-! ### Slot classification: which front slots are diagonal -/

/-- A front slot is a `p1DiagSlot` iff its column is the rank-block diagonal of its row. Concretely
`frontSlot i k ∈ p1DiagSlots ↔ k = deepWidthEquiv (inl (Fin.cast hr0.symm i))`. -/
theorem frontSlot_mem_p1DiagSlots_iff (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (i : Fin (M 0)) (k : Fin (M 1)) :
    frontSlot M i k ∈ p1DiagSlots M hrs hr0
      ↔ k = deepWidthEquiv hrs (Sum.inl (Fin.cast hr0.symm i)) := by
  unfold p1DiagSlots
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i', _, h⟩
    -- `frontSlot i' (…) = frontSlot i k` ⟹ rows equal (`i' = i`) and cols equal (`k = …`)
    have hrow : i' = i := by
      have := congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
      exact Fin.ext this
    have hcol : (deepWidthEquiv hrs (Sum.inl (Fin.cast hr0.symm i')) : Fin (M 1)) = k := by
      have := congrArg (fun q : FlatIdx M => (q.2.val : ℕ)) h
      exact (Fin.ext this)
    rw [← hcol, hrow]
  · rintro rfl
    exact ⟨i, Finset.mem_univ _, rfl⟩

/-- A front coord is never the pivot (the pivot is a deep-layer top slot). -/
theorem coordOf_frontSlot_ne_pivot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (i : Fin (M 0)) (k : Fin (M 1)) :
    coordOf M (frontSlot M i k) ≠ pivotCoord M hrs hr hc := by
  intro h
  exact frontSlot_ne_topSlot M hrs i k ⟨0, hr⟩ ⟨0, hc⟩ (coordOf_injective M h)

/-- **The diagonal front entry bound.** On the box, the rank-block diagonal entry
`P1u i (cast i) = u (coordOf (frontSlot i (deepWidthEquiv (inl (cast i)))))` is in `[δ/2, δ]`, so
`δ/2 ≤ |P1u i (cast i)|`. -/
theorem P1u_diag_ge_of_mem (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η : ℝ) (hδ : 0 < δ) {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k)
    (i : Fin (M 0)) :
    δ / 2 ≤ |P1u M hrs u i (Fin.cast hr0.symm i)| := by
  set k := deepWidthEquiv hrs (Sum.inl (Fin.cast hr0.symm i)) with hk
  have hslot : frontSlot M i k ∈ p1DiagSlots M hrs hr0 :=
    (frontSlot_mem_p1DiagSlots_iff M hrs hr0 i k).mpr rfl
  have hval : u (coordOf M (frontSlot M i k)) ∈ Set.Icc (δ / 2) δ := by
    have hne := coordOf_frontSlot_ne_pivot M hrs hr hc i k
    have := hrest _ hne
    rwa [condBoxWidth_coordOf, slotBox, if_pos hslot] at this
  have hP1eq : P1u M hrs u i (Fin.cast hr0.symm i) = u (coordOf M (frontSlot M i k)) := rfl
  rw [hP1eq]
  rw [Set.mem_Icc] at hval
  rw [abs_of_nonneg (by linarith [hval.1])]
  exact hval.1

/-- **The off-diagonal front entry bound.** For a column `a ≠ cast i`, the slot is NOT a diagonal
slot (same row, different rank-block column), so `P1u i a ∈ [−η, η]`, i.e. `|P1u i a| ≤ η`. -/
theorem P1u_offdiag_le_of_mem (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η : ℝ) {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k)
    (i : Fin (M 0)) (a : Fin r) (ha : a ≠ Fin.cast hr0.symm i) :
    |P1u M hrs u i a| ≤ η := by
  set k := deepWidthEquiv hrs (Sum.inl a) with hk
  -- `frontSlot i k` is NOT diagonal: its column `k ≠ deepWidthEquiv (inl (cast i))`
  have hnotdiag : frontSlot M i k ∉ p1DiagSlots M hrs hr0 := by
    rw [frontSlot_mem_p1DiagSlots_iff]
    intro hcoleq
    -- `deepWidthEquiv (inl a) = deepWidthEquiv (inl (cast i))` ⟹ `a = cast i` (injective)
    have : (Sum.inl a : Fin r ⊕ Fin s) = Sum.inl (Fin.cast hr0.symm i) :=
      (deepWidthEquiv hrs).injective hcoleq
    exact ha (Sum.inl_injective this)
  have hval : u (coordOf M (frontSlot M i k)) ∈ Set.Icc (-η) η := by
    have hne := coordOf_frontSlot_ne_pivot M hrs hr hc i k
    have := hrest _ hne
    rwa [condBoxWidth_coordOf, slotBox, if_neg hnotdiag] at this
  have hP1eq : P1u M hrs u i a = u (coordOf M (frontSlot M i k)) := rfl
  rw [hP1eq, abs_le]
  rw [Set.mem_Icc] at hval
  exact hval

/-- **The box ⟹ Gram det `≠ 0`.** On the conditioned box (diagonal front coords in `[δ/2,δ]`, the rest
in `[−η,η]`), with the margin condition `(↑(r−1))·η + γ ≤ δ/2` and `γ > 0`, `P₁` is strictly row
diagonally dominant, so `det(P₁ᵀP₁) ≠ 0`. The off-diagonal sum has `r−1` terms each `≤ η`. -/
theorem gram_det_ne_of_box (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hmargin : ((r - 1 : ℕ) : ℝ) * η + γ ≤ δ / 2)
    {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k) :
    ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0 := by
  refine gram_det_ne_of_diagDominant M hrs hr0 u γ hγ (fun i => ?_)
  -- the off-diagonal sum: `r−1` terms each `≤ η`
  have hsum : (∑ a ∈ Finset.univ.erase (Fin.cast hr0.symm i), |P1u M hrs u i a|)
      ≤ ((r - 1 : ℕ) : ℝ) * η := by
    calc (∑ a ∈ Finset.univ.erase (Fin.cast hr0.symm i), |P1u M hrs u i a|)
        ≤ ∑ _a ∈ Finset.univ.erase (Fin.cast hr0.symm i), η :=
          Finset.sum_le_sum (fun a ha => P1u_offdiag_le_of_mem M hrs hr0 hr hc δ η hrest i a
            (Finset.ne_of_mem_erase ha))
      _ = ((Finset.univ.erase (Fin.cast hr0.symm i)).card : ℝ) * η := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((r - 1 : ℕ) : ℝ) * η := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- the diagonal: `≥ δ/2`
  have hdiag := P1u_diag_ge_of_mem M hrs hr0 hr hc δ η hδ hrest i
  -- combine: `∑ + γ ≤ (r−1)η + γ ≤ δ/2 ≤ |diag|`
  linarith [hsum, hdiag, hmargin]

/-! ## `hUpos`: the `z`-free unit `U = ‖P₁·H̄_unit‖²` is positive (stratum `r = M 0`)

`Uunit = ∑ᵢⱼ ((P₁·H̄_unit) i j)²` is `> 0` iff the matrix `P₁·H̄_unit ≠ 0`. The angular unit `H̄_unit`
has its pivot entry `(⟨0⟩,⟨0⟩) = 1`, so `H̄_unit ≠ 0`; and on the square stratum a `det P₁ ≠ 0` `P₁`
gives `P₁·H̄_unit ≠ 0` (left-mult by an invertible matrix is injective, `P₁·0 = 0`). -/

/-- A finite double sum of squares is positive once one entry is nonzero. -/
theorem frobeniusSq_pos_of_entry_ne {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) {i₀ : ι} {j₀ : κ} (h : X i₀ j₀ ≠ 0) :
    (0 : ℝ) < ∑ i, ∑ j, (X i j) ^ 2 := by
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) ?_
  exact ⟨i₀, Finset.mem_univ _, Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨j₀, Finset.mem_univ _, by positivity⟩⟩

/-- **`Uunit > 0` on the square stratum from `det P₁ ≠ 0`.** `H̄_unit` has pivot entry `1`, so it is a
nonzero matrix; left-multiplication by the invertible `P₁` keeps it nonzero, so some entry of
`P₁·H̄_unit` is nonzero and the sum of squares is positive. -/
theorem Uunit_pos_of_det_ne (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (hr0 : r = M 0) (u : Fin (routeMAmbient M) → ℝ)
    (hdet : ((P1u M hrs u).transpose * P1u M hrs u).det ≠ 0) :
    0 < Uunit M hrs hr hc u := by
  subst hr0
  -- `det P₁ ≠ 0` from the Gram
  have hdetP1 : (P1u M hrs u).det ≠ 0 := by
    intro h0; apply hdet; rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
  have hunit : IsUnit (P1u M hrs u).det := isUnit_iff_ne_zero.mpr hdetP1
  -- `H̄_unit ≠ 0`: its pivot entry is `1`
  have hHne : HbarUnit M hrs hr hc u ≠ 0 := by
    intro h0
    have hpiv : HbarUnit M hrs hr hc u ⟨0, hr⟩ ⟨0, hc⟩ = 1 := by
      simp only [HbarUnit]
      rw [if_pos]
      rfl
    rw [h0] at hpiv
    exact one_ne_zero hpiv.symm
  -- `P₁·H̄_unit ≠ 0` (left-mult by invertible is injective)
  have hprodne : P1u M hrs u * HbarUnit M hrs hr hc u ≠ 0 := by
    intro h0
    letI := Matrix.invertibleOfIsUnitDet (P1u M hrs u) hunit
    apply hHne
    have hz : P1u M hrs u * HbarUnit M hrs hr hc u
        = P1u M hrs u * (0 : Matrix (Fin (M 0)) (Fin (M 2)) ℝ) := by
      rw [Matrix.mul_zero]; exact h0
    exact (Matrix.mul_right_injective_of_invertible (P1u M hrs u)) hz
  -- some entry is nonzero
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hprodne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  rw [Uunit]
  exact frobeniusSq_pos_of_entry_ne _ (by simpa using hj)

/-! ## The two named hypotheses, discharged from box membership (the directly-pluggable forms)

`gram_det_ne_of_box` makes `det(P1uᵀP1u) ≠ 0` unconditional on the box; the two named analytic
hypotheses of `routeMCore_smearedL2` then close. These are the forms a headline plugs in. -/

/-- The rest-box membership extracted from full `condBox` membership (drop the pivot constraint). -/
theorem rest_of_condBox (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η : ℝ) {u : Fin (routeMAmbient M) → ℝ}
    (hu : u ∈ condBox (pivotCoord M hrs hr hc) (condBoxWidth M hrs hr0 δ η) δ) :
    ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k := hu.2

/-- **`hcancel` from box membership** (the off-pole cancellation `P₁·Λ₀ = P₂`). -/
theorem Lam0u_cancel_of_box (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hmargin : ((r - 1 : ℕ) : ℝ) * η + γ ≤ δ / 2) {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k) :
    P1u M hrs u * Lam0u M hrs u = P2u M hrs u :=
  Lam0u_cancel_of_gram_square M hrs hr0 u
    (gram_det_ne_of_box M hrs hr0 hr hc δ η γ hδ hγ hmargin hrest)

/-- **`hUpos` from box membership** (the `z`-free unit `U > 0`). -/
theorem Uunit_pos_of_box (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hmargin : ((r - 1 : ℕ) : ℝ) * η + γ ≤ δ / 2) {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k) :
    0 < Uunit M hrs hr hc u :=
  Uunit_pos_of_det_ne M hrs hr hc hr0 u
    (gram_det_ne_of_box M hrs hr0 hr hc δ η γ hδ hγ hmargin hrest)

/-! ## Field A (brick b): the Varah `Λ₀`-entry bound

`Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` collapses to `P₁⁻¹P₂` on the square slice (`(P₁ᵀP₁)⁻¹P₁ᵀ = P₁⁻¹` since
`P₁ᵀ⁻¹P₁ᵀ = 1`). The Core Varah bound `inv_mul_entry_bound` then bounds each entry of `Λ₀` by
`(1/γ)·η` (δ-free with `γ = δ/4`, `η = δ/(4(r−1))`). -/

/-- **The Varah `Λ₀`-entry bound on the box.** On the square slice `Λ₀ = P₁⁻¹P₂`, and the residual
front cols satisfy `|P₂ i b| ≤ η` (non-diagonal); the Core Varah inverse-entry bound gives
`|Λ₀ a b| ≤ (1/γ)·η`. -/
theorem Lam0u_entry_bound_of_box (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0) (hr : 0 < r)
    (hc : 0 < M 2) (δ η γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hmargin : ((r - 1 : ℕ) : ℝ) * η + γ ≤ δ / 2)
    {u : Fin (routeMAmbient M) → ℝ}
    (hrest : ∀ k, k ≠ pivotCoord M hrs hr hc → u k ∈ condBoxWidth M hrs hr0 δ η k)
    (a : Fin r) (b : Fin s) :
    |Lam0u M hrs u a b| ≤ (1 / γ) * η := by
  have hgram := gram_det_ne_of_box M hrs hr0 hr hc δ η γ hδ hγ hmargin hrest
  -- the column bound on `P₂`: each residual front entry `≤ η`
  have hP2col : ∀ i : Fin (M 0), |P2u M hrs u i b| ≤ η := by
    intro i
    -- `P2u i b = u (coordOf (frontSlot i (deepWidthEquiv (inr b))))`, a non-diagonal front slot
    set k := deepWidthEquiv hrs (Sum.inr b) with hk
    have hnotdiag : frontSlot M i k ∉ p1DiagSlots M hrs hr0 := by
      rw [frontSlot_mem_p1DiagSlots_iff]
      intro hcoleq
      exact Sum.inr_ne_inl ((deepWidthEquiv hrs).injective hcoleq)
    have hval : u (coordOf M (frontSlot M i k)) ∈ Set.Icc (-η) η := by
      have hne := coordOf_frontSlot_ne_pivot M hrs hr hc i k
      have := hrest _ hne
      rwa [condBoxWidth_coordOf, slotBox, if_neg hnotdiag] at this
    have hP2eq : P2u M hrs u i b = u (coordOf M (frontSlot M i k)) := rfl
    rw [hP2eq, abs_le]; rwa [Set.mem_Icc] at hval
  -- subst to the square slice, where `Λ₀ = P₁⁻¹P₂` and the Core Varah bound applies
  subst hr0
  haveI : Nonempty (Fin (M 0)) := ⟨⟨0, hr⟩⟩
  have hdetP1 : (P1u M hrs u).det ≠ 0 := by
    intro h0; apply hgram; rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
  have hunit : IsUnit (P1u M hrs u).det := isUnit_iff_ne_zero.mpr hdetP1
  have hunitT : IsUnit ((P1u M hrs u).transpose).det := Matrix.isUnit_det_transpose _ hunit
  -- `Λ₀ = P₁⁻¹ P₂`
  have hLamEq : Lam0u M hrs u = (P1u M hrs u)⁻¹ * P2u M hrs u := by
    rw [Lam0u, Matrix.mul_inv_rev,
      Matrix.mul_assoc ((P1u M hrs u)⁻¹) ((P1u M hrs u).transpose)⁻¹ ((P1u M hrs u).transpose),
      Matrix.nonsing_inv_mul _ hunitT, Matrix.mul_one]
  -- the diagonal dominance of the (now square) `P₁`
  have hdd : DLNFibre.Core.Matrix.StrictRowDominant (P1u M hrs u) γ := by
    refine ⟨hγ, fun i => ?_⟩
    have hsum : (∑ a ∈ Finset.univ.erase i, |P1u M hrs u i a|) ≤ ((M 0 - 1 : ℕ) : ℝ) * η := by
      calc (∑ a ∈ Finset.univ.erase i, |P1u M hrs u i a|)
          ≤ ∑ _a ∈ Finset.univ.erase i, η :=
            Finset.sum_le_sum (fun a ha => P1u_offdiag_le_of_mem M hrs rfl hr hc δ η hrest i a
              (by simpa using Finset.ne_of_mem_erase ha))
        _ = ((Finset.univ.erase i).card : ℝ) * η := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((M 0 - 1 : ℕ) : ℝ) * η := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have hdiag := P1u_diag_ge_of_mem M hrs rfl hr hc δ η hδ hrest i
    simp only [Fin.cast_eq_self] at hdiag
    linarith [hsum, hdiag, hmargin]
  rw [hLamEq]
  exact hdd.inv_mul_entry_bound (P2u M hrs u) b (Mj := η) hP2col a

/-! ## The wired headline (the two named hypotheses discharged from box membership)

`routeMCore_smearedL2` takes three per-family inputs over peeled points: the off-pole cancellation
`hcancel`, `U`-positivity `hUpos`, and the field-A containment `hSpre`. The first two are the
genuinely-analytic NAMED facts the certificate adjudicated; this headline discharges BOTH from box
membership (`gram_det_ne_of_box` ⟹ both, on the conditioned box), leaving the field-A containment
`hSpre` and the per-point box membership `hmem` of the peeled points as the residual per-family inputs
(both readoff-level: `hmem` is the membership bridge, proved cheaply at a concrete `M`).

The honest scope (decorrelated Codex Q3): this is the smeared L=2 box-divergence on the square stratum
`r = M 0` GIVEN field-A containment — the two analytic hypotheses `hcancel`/`hUpos` are no longer
assumed. A fully unconditional headline additionally discharges `hSpre`. -/

/-- **The smeared L=2 box-divergence on the square stratum, with `hcancel`/`hUpos` discharged.** For
`r = M 0` (the entire genuine smeared L=2 stratum), the conditioned box `condBoxWidth` makes the off-pole
cancellation and `U`-positivity UNCONDITIONAL (via the diagonal-dominance Gram det); the box-divergence
then follows from the chart facts + field-A containment `hSpre` + the peeled-point membership `hmem`. -/
theorem routeMCore_smearedL2_square {n : ℕ} (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr0 : r = M 0)
    (hr : 0 < r) (hc : 0 < M 2) (hN : routeMAmbient M = n + 1)
    (p : Fin (n + 1)) (box : Fin (n + 1) → Set ℝ) (c' ε δ η γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hmargin : ((r - 1 : ℕ) : ℝ) * η + γ ≤ δ / 2)
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoord M hrs hr hc)
    (hSpre : condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ
      ⊆ (fun u => psiMap M hrs (Rmap M hrs hr hc u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hboxmeas : ∀ k, MeasurableSet (box (p.succAbove k)))
    (hboxmeasAll : ∀ k : Fin (routeMAmbient M), MeasurableSet ((fun k => box (hN ▸ k)) k))
    (hboxpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box (p.succAbove k))))
    (hexp : ((r * M 2 - 1 : ℕ) : ℝ) - 2 * c' ≤ -1)
    (hmem : ∀ z ∈ Set.Ioo (0:ℝ) δ,
      ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
        (hN ▸ (Fin.insertNth p z y) : Fin (routeMAmbient M) → ℝ)
          ∈ condBox (pivotCoord M hrs hr hc) (condBoxWidth M hrs hr0 δ η) δ) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ := by
  refine routeMCore_smearedL2 (M := M) (n := n) hrs hr hc hN p
    box c' ε δ hδ hp hSpre hboxmeas hboxmeasAll hboxpos hexp ?_ ?_
  · -- `hcancel` on each peeled point (off the pole, unconditional on the box)
    intro z hz y hy
    exact Lam0u_cancel_of_box M hrs hr0 hr hc δ η γ hδ hγ hmargin
      (rest_of_condBox M hrs hr0 hr hc δ η (hmem z hz y hy))
  · -- `hUpos` at the `z = 0` point. The rest coords are `z`-free, so reuse the rest membership of the
    -- `z = δ/2` peeled point (`hN_insertNth_agree_off_pivot`).
    intro y hy
    have hδ2 : (δ / 2) ∈ Set.Ioo (0:ℝ) δ := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hrest2 := rest_of_condBox M hrs hr0 hr hc δ η (hmem (δ / 2) hδ2 y hy)
    -- transfer the rest membership from `insertNth p (δ/2) y` to `insertNth p 0 y` (z-free off pivot)
    have hagree := hN_insertNth_agree_off_pivot M hrs hr hc hN p hp (δ / 2) y
    refine Uunit_pos_of_box M hrs hr0 hr hc δ η γ hδ hγ hmargin (fun k hk => ?_)
    rw [← hagree k hk]
    exact hrest2 k hk

end DLNFibre.DLN.RLCT
