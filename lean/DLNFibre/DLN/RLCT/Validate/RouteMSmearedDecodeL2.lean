import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartOpaque
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP

/-!
# `RouteMSmearedDecodeL2` — the opaque-width L=2 chart maps `ψ`/`R` + the DECODE

The opaque-width generalization of the `(2,3,1)` chart (`RouteM231Smeared`). Builds, for any L=2 widths
`M : Fin 3 → ℕ` with the front-bottleneck split `r + s = M 1`:

* the slot bijection `slotEquiv M : Fin (routeMAmbient M) ≃ FlatIdx M` (the noncomputable `equivFin.symm`);
* the deepest-top flat coords `topSlot a j` / bottom coords `botSlot b j` (via `deepWidthEquiv hrs`);
* the radial pivot `pivotSlot`, the radial blow-up `R := pivotBlowupOn (topCoords) pivotSlot`;
* the chart components read off `u` at these slots (`A0u`, `zu`, `HbarUnit u`, `Sbotu`, `Λ₀u`);
* the shear `shiftCore` (the `−Λ₀·Sbot` shift into the Core slots) + `ψ := paramsEquivFlat ∘ packM ∘ shearMBody`;
* the DECODE `packM (shearMBody (R u)) = chartL2Params M hrs (A0u u) (zu u) (HbarUnit u) (Sbotu u) (Λ₀u u)`.

Then the banked `routeMCore_phiL2` gives the rate `routeMCore M (ψ (R u)) = (zu u)²·‖P₁·H̄_unit‖²` off the
shear pole, the input to `routeMCore_box_diverges_smearedL2`'s peeled-rate hypothesis.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin 3 → ℕ} {r s : ℕ}

/-! ## The slot bijection and the deepest-row flat coords -/

/-- The (noncomputable) slot bijection `Fin (routeMAmbient M) ≃ FlatIdx M` (the `equivFin.symm`;
`routeMAmbient M = flatDim M = card (FlatIdx M)`). -/
noncomputable def slotEquiv (M : Fin 3 → ℕ) : Fin (routeMAmbient M) ≃ FlatIdx M :=
  (Fintype.equivFin (FlatIdx M)).symm

/-- A layer-0 (front) flat slot `⟨⟨0, i⟩, j⟩`. -/
def frontSlot (M : Fin 3 → ℕ) (i : Fin (M 0)) (j : Fin (M 1)) : FlatIdx M :=
  ⟨⟨(0 : Fin 2), i⟩, j⟩

/-- A deepest-top flat slot `⟨⟨1, deepWidthEquiv (inl a)⟩, j⟩` (top `r`-row block of `A¹`). -/
noncomputable def topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (j : Fin (M 2)) :
    FlatIdx M :=
  ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inl a)⟩, j⟩

/-- A deepest-bottom flat slot `⟨⟨1, deepWidthEquiv (inr b)⟩, j⟩` (bottom `s`-row block of `A¹`). -/
noncomputable def botSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (b : Fin s) (j : Fin (M 2)) :
    FlatIdx M :=
  ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inr b)⟩, j⟩

/-- The deepest row of `topSlot a j`, as a `Fin (M 1)` (the `M (1:Fin 2).castSucc = M 1` row). -/
theorem topSlot_row (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (j : Fin (M 2)) :
    (topSlot M hrs a j).1.2 = deepWidthEquiv hrs (Sum.inl a) := rfl

/-- The deepest row of `botSlot b j`. -/
theorem botSlot_row (M : Fin 3 → ℕ) (hrs : r + s = M 1) (b : Fin s) (j : Fin (M 2)) :
    (botSlot M hrs b j).1.2 = deepWidthEquiv hrs (Sum.inr b) := rfl

/-- The `Fin (routeMAmbient M)` coordinate of a flat slot `q` (the `slotEquiv.symm`). -/
noncomputable def coordOf (M : Fin 3 → ℕ) (q : FlatIdx M) : Fin (routeMAmbient M) :=
  (slotEquiv M).symm q

/-- The deepest-top radial coords (R's active set / the shear's Core slots): the `r·c` coords
`coordOf (topSlot a j)`. -/
noncomputable def topCoords (M : Fin 3 → ℕ) (hrs : r + s = M 1) : Finset (Fin (routeMAmbient M)) :=
  Finset.image (fun p : Fin r × Fin (M 2) => coordOf M (topSlot M hrs p.1 p.2)) Finset.univ

/-- The radial pivot coord (the `(0,0)` entry of the top block) — needs `0 < r`, `0 < M 2`. -/
noncomputable def pivotCoord (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2) :
    Fin (routeMAmbient M) :=
  coordOf M (topSlot M hrs ⟨0, hr⟩ ⟨0, hc⟩)

/-! ## `coordOf` injectivity + the deepest-row slots are distinct -/

/-- `coordOf` is injective (`slotEquiv.symm` is a bijection). -/
theorem coordOf_injective (M : Fin 3 → ℕ) {q q' : FlatIdx M} (h : coordOf M q = coordOf M q') :
    q = q' := (slotEquiv M).symm.injective h

/-- `coordOf q = coordOf q' ↔ q = q'`. -/
theorem coordOf_inj_iff (M : Fin 3 → ℕ) (q q' : FlatIdx M) :
    coordOf M q = coordOf M q' ↔ q = q' :=
  ⟨coordOf_injective M, fun h => by rw [h]⟩

/-- `deepWidthEquiv` separates the `inl`/`inr` blocks: `topSlot a j ≠ botSlot b j'` (same layer `1`, so
the row equality is homogeneous; `deepWidthEquiv` injective + `Sum.inl_ne_inr`). -/
theorem topSlot_ne_botSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (a : Fin r) (j : Fin (M 2)) (b : Fin s) (j' : Fin (M 2)) :
    topSlot M hrs a j ≠ botSlot M hrs b j' := by
  intro h
  -- both slots have layer `1`; compare row `.val`s (non-dependent ℕ codomain ⟹ `congrArg` is cast-free)
  have hval : (deepWidthEquiv hrs (Sum.inl a) : Fin (M 1)).val
      = (deepWidthEquiv hrs (Sum.inr b) : Fin (M 1)).val :=
    congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
  have hrow : deepWidthEquiv hrs (Sum.inl a) = deepWidthEquiv hrs (Sum.inr b) := Fin.ext hval
  exact Sum.inl_ne_inr ((deepWidthEquiv hrs).injective hrow)

/-- A front slot is never a deepest-top slot (different layer: `0 ≠ 1`). -/
theorem frontSlot_ne_topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (i : Fin (M 0)) (jf : Fin (M 1)) (a : Fin r) (j : Fin (M 2)) :
    frontSlot M i jf ≠ topSlot M hrs a j := by
  intro h
  have hlayer : (0 : Fin 2) = (1 : Fin 2) := congrArg (·.1.1) h
  exact absurd hlayer (by decide)

/-! ## The chart components, read off `u` at the flat slots -/

/-- The front factor `A⁰ i j = u (coordOf (frontSlot i j))` (the identity front block). -/
noncomputable def A0u (M : Fin 3 → ℕ) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin (M 1)) ℝ :=
  fun i j => u (coordOf M (frontSlot M i j))

/-- The radial pivot value `z = u (pivotCoord)`. -/
noncomputable def zu (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  u (pivotCoord M hrs hr hc)

/-- The residual `S_bot b j = u (coordOf (botSlot b j))` (the free bottom block). -/
noncomputable def Sbotu (M : Fin 3 → ℕ) (hrs : r + s = M 1) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin s) (Fin (M 2)) ℝ :=
  fun b j => u (coordOf M (botSlot M hrs b j))

/-- The angular UNIT block `H̄_unit a j`: the pivot entry `(⟨0⟩,⟨0⟩)` is fixed `= 1`, every other top-row
entry is the free coord `u (coordOf (topSlot a j))`. (The `(0,0)` entry IS the radial pivot, so its
angular value is `1`; the others are the `h`-coords.) -/
noncomputable def HbarUnit (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) : Matrix (Fin r) (Fin (M 2)) ℝ :=
  fun a j => if coordOf M (topSlot M hrs a j) = pivotCoord M hrs hr hc then 1
    else u (coordOf M (topSlot M hrs a j))

/-- The rank-block front columns `P₁ i a = A⁰ i (deepWidthEquiv (inl a))`. -/
noncomputable def P1u (M : Fin 3 → ℕ) (hrs : r + s = M 1) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin r) ℝ :=
  fun i a => A0u M u i (deepWidthEquiv hrs (Sum.inl a))

/-- The residual front columns `P₂ i b = A⁰ i (deepWidthEquiv (inr b))`. -/
noncomputable def P2u (M : Fin 3 → ℕ) (hrs : r + s = M 1) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin s) ℝ :=
  fun i b => A0u M u i (deepWidthEquiv hrs (Sum.inr b))

/-- The rational routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` (the smeared shear coefficient; pole at `det P₁ᵀP₁ = 0`). -/
noncomputable def Lam0u (M : Fin 3 → ℕ) (hrs : r + s = M 1) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin r) (Fin s) ℝ :=
  ((P1u M hrs u).transpose * P1u M hrs u)⁻¹ * (P1u M hrs u).transpose * P2u M hrs u

/-- The `z`-free unit `U = ‖P₁·H̄_unit‖²_F` (the polynomial factor of the rate `F = z²·U`). -/
noncomputable def Uunit (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  ∑ i, ∑ j, ((P1u M hrs u * HbarUnit M hrs hr hc u) i j) ^ 2

/-- `Uunit ≥ 0` (a sum of squares). -/
theorem Uunit_nonneg (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) : (0 : ℝ) ≤ Uunit M hrs hr hc u :=
  frobeniusSq_nonneg _

/-! ## The rate wrapper: `routeMCore M (ψ (R u)) = (zu u)²·Uunit` from the DECODE + cancellation

The reusable bridge from the opaque-width DECODE `ψ(R u) = phiL2 M hrs (A0u u) …` (with `Hbar := HbarUnit`)
to the headline's peeled-rate, via the banked rate core `routeMCore_phiL2`. The decode + the off-pole
cancellation `P₁·Λ₀ = P₂` are the per-`u` inputs (the cancellation holds on the conditioned box where
`det P₁ ≠ 0`). -/

/-- **The rate from the decode.** Given the decode `ψ(R u) = phiL2 M hrs (A0u u)(zu u)(HbarUnit u)(Sbotu u)
(Lam0u u)` and the shear cancellation `P₁·Λ₀ = P₂` (off the pole), the loss factorizes:
`routeMCore M (ψ(R u)) = (zu u)²·Uunit u`. The banked `routeMCore_phiL2` with `Hbar := HbarUnit`. -/
theorem routeMCore_rate_of_decode (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)) (u : Fin (routeMAmbient M) → ℝ)
    (hDecode : ψ (R u) = phiL2 M hrs (A0u M u) (zu M hrs hr hc u) (HbarUnit M hrs hr hc u)
      (Sbotu M hrs u) (Lam0u M hrs u))
    (hcancel : P1u M hrs u * Lam0u M hrs u = P2u M hrs u) :
    routeMCore M (ψ (R u)) = (zu M hrs hr hc u) ^ 2 * Uunit M hrs hr hc u := by
  rw [hDecode, Uunit]
  exact routeMCore_phiL2 M hrs (A0u M u) (zu M hrs hr hc u) (HbarUnit M hrs hr hc u)
    (Sbotu M hrs u) (Lam0u M hrs u) (P1u M hrs u) (P2u M hrs u)
    (fun i a => rfl) (fun i b => rfl) hcancel

/-! ## `topCoords` membership + the radial blow-up `R` -/

/-- `coordOf (topSlot a j) ∈ topCoords` (the deepest-top coords are exactly these images). -/
theorem coordOf_topSlot_mem (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (j : Fin (M 2)) :
    coordOf M (topSlot M hrs a j) ∈ topCoords M hrs := by
  rw [topCoords, Finset.mem_image]
  exact ⟨(a, j), Finset.mem_univ _, rfl⟩

/-- Membership in `topCoords` is exactly "is the `coordOf` of some top slot". -/
theorem mem_topCoords_iff (M : Fin 3 → ℕ) (hrs : r + s = M 1) (m : Fin (routeMAmbient M)) :
    m ∈ topCoords M hrs ↔ ∃ a : Fin r, ∃ j : Fin (M 2), coordOf M (topSlot M hrs a j) = m := by
  rw [topCoords, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, j⟩, _, h⟩; exact ⟨a, j, h⟩
  · rintro ⟨a, j, h⟩; exact ⟨(a, j), Finset.mem_univ _, h⟩

/-- `coordOf (frontSlot i jf) ∉ topCoords` (a front slot is not a top slot). -/
theorem coordOf_frontSlot_not_mem (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (i : Fin (M 0)) (jf : Fin (M 1)) : coordOf M (frontSlot M i jf) ∉ topCoords M hrs := by
  rw [mem_topCoords_iff]
  rintro ⟨a, j, h⟩
  exact frontSlot_ne_topSlot M hrs i jf a j (coordOf_injective M h.symm)

/-- `coordOf (botSlot b j) ∉ topCoords` (a bottom slot is not a top slot). -/
theorem coordOf_botSlot_not_mem (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (b : Fin s) (j : Fin (M 2)) : coordOf M (botSlot M hrs b j) ∉ topCoords M hrs := by
  rw [mem_topCoords_iff]
  rintro ⟨a, j', h⟩
  exact topSlot_ne_botSlot M hrs a j' b j (coordOf_injective M h)

/-- The radial blow-up `R := pivotBlowupOn (topCoords) pivotCoord`: fixes the pivot, scales the other
top coords by the pivot, fixes the spectators (front + bottom). The sole Jacobian carrier. -/
noncomputable def Rmap (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  pivotBlowupOn (topCoords M hrs) (pivotCoord M hrs hr hc)

/-! ## The smeared shear `shiftFull` (the `−Λ₀·S_bot` correction, by an injective single-term sum)

The correction at a deepest-top coord `m = coordOf (topSlot a j)` is `−(Λ₀·S_bot) a j`. To define it
TOTALLY over all `m` WITHOUT a dependent slot-extraction, sum over all `(a,j)` with an `if` selecting the
unique matching slot (`coordOf (topSlot ·) ` is injective). The single nonzero term gives the value. -/

/-- The full-vector correction `−∑_{a,j} [coordOf(topSlot a j) = m]·(Λ₀ v'·S_bot v') a j`. At a top coord
`m = coordOf(topSlot a₀ j₀)` it collapses to `−(Λ₀·S_bot) a₀ j₀`; off `topCoords` it is `0`. -/
noncomputable def shiftFull (M : Fin 3 → ℕ) (hrs : r + s = M 1) (v' : Fin (routeMAmbient M) → ℝ)
    (m : Fin (routeMAmbient M)) : ℝ :=
  -∑ a : Fin r, ∑ j : Fin (M 2),
    (if coordOf M (topSlot M hrs a j) = m then (Lam0u M hrs v' * Sbotu M hrs v') a j else 0)

/-- **The single-term collapse.** At a deepest-top coord, `shiftFull` reads off the `(a,j)` correction
(the `coordOf (topSlot ·)` injectivity kills every off-diagonal term). -/
theorem shiftFull_topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (v' : Fin (routeMAmbient M) → ℝ)
    (a₀ : Fin r) (j₀ : Fin (M 2)) :
    shiftFull M hrs v' (coordOf M (topSlot M hrs a₀ j₀))
      = -(Lam0u M hrs v' * Sbotu M hrs v') a₀ j₀ := by
  -- the column of equal top slots: `topSlot a j = topSlot a₀ j₀ ⟹ j = j₀` (non-dependent `.2.val`)
  have hcol : ∀ (a : Fin r) (j : Fin (M 2)),
      topSlot M hrs a j = topSlot M hrs a₀ j₀ → j = j₀ := fun a j h =>
    Fin.ext (congrArg (fun q : FlatIdx M => (q.2.val : ℕ)) h)
  -- the row: `topSlot a j = topSlot a₀ j₀ ⟹ a = a₀` (via `deepWidthEquiv` injectivity on the row `.1.2`)
  have hrow : ∀ (a : Fin r) (j : Fin (M 2)),
      topSlot M hrs a j = topSlot M hrs a₀ j₀ → a = a₀ := by
    intro a j h
    have hv : (deepWidthEquiv hrs (Sum.inl a) : Fin (M 1)).val
        = (deepWidthEquiv hrs (Sum.inl a₀) : Fin (M 1)).val :=
      congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
    have he : deepWidthEquiv hrs (Sum.inl a) = deepWidthEquiv hrs (Sum.inl a₀) := Fin.ext hv
    exact Sum.inl_injective ((deepWidthEquiv hrs).injective he)
  rw [shiftFull, neg_inj, Finset.sum_eq_single a₀]
  · rw [Finset.sum_eq_single j₀]
    · rw [if_pos rfl]
    · intro j _ hj
      refine if_neg (fun hcoord => hj ?_)
      exact hcol a₀ j (coordOf_injective M hcoord)
    · intro hj0; exact absurd (Finset.mem_univ j₀) hj0
  · intro a _ ha
    refine Finset.sum_eq_zero (fun j _ => if_neg (fun hcoord => ha ?_))
    exact hrow a j (coordOf_injective M hcoord)
  · intro ha0; exact absurd (Finset.mem_univ a₀) ha0

/-! ## `Rmap` apply forms (the radial blow-up at the three slot types) -/

/-- The pivot coord is in `topCoords` (it is `coordOf (topSlot ⟨0⟩ ⟨0⟩)`). -/
theorem pivotCoord_mem (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2) :
    pivotCoord M hrs hr hc ∈ topCoords M hrs := coordOf_topSlot_mem M hrs ⟨0, hr⟩ ⟨0, hc⟩

/-- `Rmap u m = u m` off `topCoords` (spectators: front + bottom; `pivot ∈ topCoords` so `m ≠ pivot`). -/
theorem Rmap_spectator (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) {m : Fin (routeMAmbient M)} (hm : m ∉ topCoords M hrs) :
    Rmap M hrs hr hc u m = u m := by
  have hmp : m ≠ pivotCoord M hrs hr hc := fun h => hm (h ▸ pivotCoord_mem M hrs hr hc)
  simp only [Rmap, pivotBlowupOn, if_neg hmp, if_neg hm]

/-- `Rmap u (coordOf (topSlot a j)) = zu · HbarUnit a j` (pivot ↦ `z`=`z·1`; else `z·u m`=`z·HbarUnit`). -/
theorem Rmap_topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M 2)) :
    Rmap M hrs hr hc u (coordOf M (topSlot M hrs a j))
      = zu M hrs hr hc u * HbarUnit M hrs hr hc u a j := by
  rw [Rmap, HbarUnit, zu, pivotBlowupOn]
  by_cases hpiv : coordOf M (topSlot M hrs a j) = pivotCoord M hrs hr hc
  · -- the pivot entry: `R u (pivot) = u pivot = z`, and `HbarUnit = 1`, so RHS `= u pivot · 1`
    rw [if_pos hpiv, if_pos hpiv, mul_one]
  · -- a non-pivot top coord: `R u m = u pivot · u m = z · HbarUnit`
    have hmem := coordOf_topSlot_mem M hrs a j
    rw [if_neg hpiv, if_pos hmem, if_neg hpiv]

/-! ## `A0u`/`Sbotu`/`Lam0u` read only the complement `topCoordsᶜ` (the shear's spectator coords)

`A0u` reads front slots, `Sbotu` reads bottom slots — both `∉ topCoords`. So they (and `Λ₀` built from
them) are invariant under any change confined to `topCoords`. Lets the shear-shift reconstruct `u` off
`topCoords` (where it agrees) and recover the same `Λ₀`/`S_bot`. -/

/-- `A0u v = A0u w` if `v`, `w` agree off `topCoords` (A⁰ reads front slots, all `∉ topCoords`). -/
theorem A0u_congr (M : Fin 3 → ℕ) (hrs : r + s = M 1) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoords M hrs → v m = w m) : A0u M v = A0u M w := by
  funext i jf
  exact h _ (coordOf_frontSlot_not_mem M hrs i jf)

/-- `Sbotu v = Sbotu w` if `v`, `w` agree off `topCoords` (S_bot reads bottom slots, all `∉ topCoords`). -/
theorem Sbotu_congr (M : Fin 3 → ℕ) (hrs : r + s = M 1) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoords M hrs → v m = w m) : Sbotu M hrs v = Sbotu M hrs w := by
  funext b j
  exact h _ (coordOf_botSlot_not_mem M hrs b j)

/-- `Lam0u v = Lam0u w` if `v`, `w` agree off `topCoords` (`Λ₀` is built from `A0u` via `P₁`/`P₂`). -/
theorem Lam0u_congr (M : Fin 3 → ℕ) (hrs : r + s = M 1) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoords M hrs → v m = w m) : Lam0u M hrs v = Lam0u M hrs w := by
  have hA : A0u M v = A0u M w := A0u_congr M hrs h
  have hP1 : P1u M hrs v = P1u M hrs w := by funext i a; simp only [P1u, hA]
  have hP2 : P2u M hrs v = P2u M hrs w := by funext i b; simp only [P2u, hA]
  rw [Lam0u, Lam0u, hP1, hP2]

/-! ## The smeared shear `shiftCore` + the flat map `ψ`, and the DECODE -/

/-- The shear shift (the `(reg, spec) → core` form `shearMBody` consumes): reconstruct the full vector
from the spec block (zero core), then read `shiftFull` at the `coreSet.equivFin.symm`-indexed coord. The
`equivFin.symm`/`equivFin` round-trip (in `shearMBody_apply_of_mem`) then collapses to `shiftFull` at the
coord directly. -/
noncomputable def shiftCore (M : Fin 3 → ℕ) (hrs : r + s = M 1)
    (q : (Fin 0 → ℝ) × (Fin (topCoords M hrs)ᶜ.card → ℝ)) : Fin (topCoords M hrs).card → ℝ :=
  fun jc => shiftFull M hrs
    ((splitOfCoreSet (topCoords M hrs)).symm (q.1, ((0 : Fin (topCoords M hrs).card → ℝ), q.2)))
    ((topCoords M hrs).equivFin.symm jc)

/-- The flat smeared map `ψ = paramsEquivFlat ∘ packM ∘ shearMBody`, `packM := (flatEquivOf (slotEquiv)).symm`. -/
noncomputable def psiMap (M : Fin 3 → ℕ) (hrs : r + s = M 1) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun w => paramsEquivFlat M
    ((flatEquivOf M (slotEquiv M)).symm (shearMBody (topCoords M hrs) (shiftCore M hrs) w))

/-- **The shear-shift value at a deepest-top coord** (the `shiftCore` collapse): `shiftCore` evaluated at
the `equivFin` index of `coordOf (topSlot a j)` is `−(Λ₀·S_bot) a j`. The `equivFin.symm/equivFin`
round-trip + `shiftFull_topSlot` + the reconstruction's `topCoordsᶜ`-agreement with `Rmap u` (= `u`). -/
theorem shiftCore_at_topSlot (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M 2))
    (hmem : coordOf M (topSlot M hrs a j) ∈ topCoords M hrs) :
    shiftCore M hrs ((splitOfCoreSet (topCoords M hrs) (Rmap M hrs hr hc u)).1,
        (splitOfCoreSet (topCoords M hrs) (Rmap M hrs hr hc u)).2.2)
        ((topCoords M hrs).equivFin ⟨coordOf M (topSlot M hrs a j), hmem⟩)
      = -(Lam0u M hrs u * Sbotu M hrs u) a j := by
  rw [shiftCore, Equiv.symm_apply_apply]
  -- the reconstruction agrees with `Rmap u` (hence `u`) off `topCoords`, so `Λ₀`/`S_bot` are unchanged
  set v := (splitOfCoreSet (topCoords M hrs)).symm
    ((splitOfCoreSet (topCoords M hrs) (Rmap M hrs hr hc u)).1,
      ((0 : Fin (topCoords M hrs).card → ℝ),
        (splitOfCoreSet (topCoords M hrs) (Rmap M hrs hr hc u)).2.2)) with hv
  have hagree : ∀ m, m ∉ topCoords M hrs → v m = u m := by
    intro m hm
    rw [hv, splitOfCoreSet_symm_specBlock_eq _ _ _ _ hm, Rmap_spectator M hrs hr hc u hm]
  rw [shiftFull_topSlot, Lam0u_congr M hrs hagree, Sbotu_congr M hrs hagree]

/-! ## The DECODE `packM (shearMBody (R u)) = chartL2Params …`

The Params-level decode (the headline's peeled-rate input, modulo `paramsEquivFlat`). Proved layerwise
(`fin_cases` over the `Fin 2` layers — never the opaque `i`/`j`), each layer through the readback bricks. -/

/-- **The packM readback.** `packM (shearMBody … w) layer i j = shearMBody … w (coordOf ⟨⟨layer,i⟩,j⟩)`
(the `flatEquivOf_symm_coord` extraction at `e := slotEquiv M`). -/
theorem packM_shear_entry (M : Fin 3 → ℕ) (hrs : r + s = M 1) (w : Fin (routeMAmbient M) → ℝ)
    (q : FlatIdx M) :
    ((flatEquivOf M (slotEquiv M)).symm (shearMBody (topCoords M hrs) (shiftCore M hrs) w))
        q.1.1 q.1.2 q.2
      = shearMBody (topCoords M hrs) (shiftCore M hrs) w (coordOf M q) := by
  rw [flatEquivOf_symm_coord]; rfl

/-- **The Params-level DECODE.** `packM (shearMBody (R u)) = chartL2Params M hrs (A0u u)(zu u)(HbarUnit u)
(Sbotu u)(Lam0u u)`. The front layer is the identity readoff; the deep top layer is the radial `z·H̄_unit`
minus the shear `Λ₀·S_bot`; the deep bottom layer is the free residual `S_bot`. -/
theorem decode_params (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    (flatEquivOf M (slotEquiv M)).symm
        (shearMBody (topCoords M hrs) (shiftCore M hrs) (Rmap M hrs hr hc u))
      = chartL2Params M hrs (A0u M u) (zu M hrs hr hc u) (HbarUnit M hrs hr hc u)
          (Sbotu M hrs u) (Lam0u M hrs u) := by
  funext layer i j
  -- read the LHS entry off the slot `q := ⟨⟨layer, i⟩, j⟩`
  rw [packM_shear_entry M hrs (Rmap M hrs hr hc u) ⟨⟨layer, i⟩, j⟩]
  -- dispatch on the layer (`Fin 2`); never `fin_cases` the opaque `i`/`j`
  fin_cases layer
  · -- LAYER 0 (front): the identity readoff `A0u`
    show shearMBody (topCoords M hrs) (shiftCore M hrs) (Rmap M hrs hr hc u)
        (coordOf M (frontSlot M i j)) = A0u M u i j
    rw [shearMBody_apply_of_not_mem _ _ _ (coordOf_frontSlot_not_mem M hrs i j),
      Rmap_spectator M hrs hr hc u (coordOf_frontSlot_not_mem M hrs i j)]
    rfl
  · -- LAYER 1 (deep): split the row into the top `r` block (radial − shear) and bottom `s` block (S_bot)
    show shearMBody (topCoords M hrs) (shiftCore M hrs) (Rmap M hrs hr hc u)
        (coordOf M ⟨⟨(1 : Fin 2), i⟩, j⟩)
      = chartL2Deep hrs (zu M hrs hr hc u) (HbarUnit M hrs hr hc u) (Sbotu M hrs u)
          (Lam0u M hrs u) i j
    rw [chartL2Deep]
    rcases hsplit : (deepWidthEquiv hrs).symm i with a | b
    · -- TOP row `i = deepWidthEquiv (inl a)`: the slot is `topSlot a j`
      have hi : i = deepWidthEquiv hrs (Sum.inl a) := by
        rw [← hsplit, Equiv.apply_symm_apply]
      have hslot : (⟨⟨(1 : Fin 2), i⟩, j⟩ : FlatIdx M) = topSlot M hrs a j := by
        rw [topSlot, hi]
      rw [hslot, deepBlock, Sum.elim_inl]
      have hmem := coordOf_topSlot_mem M hrs a j
      rw [shearMBody_apply_of_mem _ _ _ hmem]
      rw [show (topCoords M hrs).equivFin
          ⟨coordOf M (topSlot M hrs a j), hmem⟩
          = (topCoords M hrs).equivFin ⟨coordOf M (topSlot M hrs a j), hmem⟩ from rfl]
      rw [shiftCore_at_topSlot M hrs hr hc u a j hmem, Rmap_topSlot M hrs hr hc u a j]
      -- `z·H̄ + (−(Λ₀·S_bot)) = (z•H̄ − Λ₀·S_bot) a j`
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    · -- BOTTOM row `i = deepWidthEquiv (inr b)`: the slot is `botSlot b j`, the free residual `S_bot`
      have hi : i = deepWidthEquiv hrs (Sum.inr b) := by
        rw [← hsplit, Equiv.apply_symm_apply]
      have hslot : (⟨⟨(1 : Fin 2), i⟩, j⟩ : FlatIdx M) = botSlot M hrs b j := by
        rw [botSlot, hi]
      rw [hslot, deepBlock, Sum.elim_inr]
      rw [shearMBody_apply_of_not_mem _ _ _ (coordOf_botSlot_not_mem M hrs b j),
        Rmap_spectator M hrs hr hc u (coordOf_botSlot_not_mem M hrs b j)]
      rfl

/-- **The flat DECODE** `psiMap (Rmap u) = phiL2 …` (apply `paramsEquivFlat` to `decode_params`). The
headline's peeled-rate input, exactly. -/
theorem psiMap_Rmap_eq_phiL2 (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    psiMap M hrs (Rmap M hrs hr hc u)
      = phiL2 M hrs (A0u M u) (zu M hrs hr hc u) (HbarUnit M hrs hr hc u)
          (Sbotu M hrs u) (Lam0u M hrs u) := by
  rw [psiMap, phiL2, decode_params M hrs hr hc u]

/-- **The opaque-width L=2 smeared rate** `routeMCore M (psiMap (Rmap u)) = (zu u)²·Uunit u`, off the
shear pole (`P₁·Λ₀ = P₂`). The decode `psiMap (Rmap u) = phiL2 …` fed through `routeMCore_rate_of_decode`. -/
theorem routeMCore_psiMap_Rmap (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ)
    (hcancel : P1u M hrs u * Lam0u M hrs u = P2u M hrs u) :
    routeMCore M (psiMap M hrs (Rmap M hrs hr hc u)) = (zu M hrs hr hc u) ^ 2 * Uunit M hrs hr hc u :=
  routeMCore_rate_of_decode M hrs hr hc (psiMap M hrs) (Rmap M hrs hr hc) u
    (psiMap_Rmap_eq_phiL2 M hrs hr hc u) hcancel

/-! ## `ψ` measure-preserving + a measurable embedding

`ψ = paramsEquivFlat ∘ packM ∘ shearMBody` with `packM := (flatEquivOf (slotEquiv)).symm`. The two outer
factors are banked measure-preserving `MeasurableEquiv`s; `shearMBody` is MP for any measurable shift
(`measurePreserving_shearMBody`). The shift `shiftCore` is measurable via the banked matrix-inverse /
`Λ₀`-entry toolkit. -/

/-- Each entry `A0u v i j` is measurable in `v` (a coordinate projection). -/
theorem measurable_A0u_entry (M : Fin 3 → ℕ) (i : Fin (M 0)) (j : Fin (M 1)) :
    Measurable (fun v : Fin (routeMAmbient M) → ℝ => A0u M v i j) :=
  measurable_pi_apply _

/-- Each entry `Sbotu v b j` is measurable in `v`. -/
theorem measurable_Sbotu_entry (M : Fin 3 → ℕ) (hrs : r + s = M 1) (b : Fin s) (j : Fin (M 2)) :
    Measurable (fun v : Fin (routeMAmbient M) → ℝ => Sbotu M hrs v b j) :=
  measurable_pi_apply _

/-- Each entry `Lam0u v a b` is measurable in `v` (the `(P₁ᵀP₁)⁻¹P₁ᵀP₂` chain via `measurable_lamEntry`,
with `P₁`/`P₂` entrywise the coordinate-projections `A0u`). -/
theorem measurable_Lam0u_entry (M : Fin 3 → ℕ) (hrs : r + s = M 1) (a : Fin r) (b : Fin s) :
    Measurable (fun v : Fin (routeMAmbient M) → ℝ => Lam0u M hrs v a b) :=
  measurable_lamEntry (fun v => P1u M hrs v) (fun v => P2u M hrs v)
    (fun i a => measurable_pi_apply _) (fun i b => measurable_pi_apply _) a b

/-- `v' ↦ shiftFull M hrs v' m` is measurable (a finite signed sum of products of `Λ₀`/`S_bot` entries). -/
theorem measurable_shiftFull_coord (M : Fin 3 → ℕ) (hrs : r + s = M 1) (m : Fin (routeMAmbient M)) :
    Measurable (fun v' : Fin (routeMAmbient M) → ℝ => shiftFull M hrs v' m) := by
  unfold shiftFull
  refine (Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun j _ => ?_))).neg
  by_cases h : coordOf M (topSlot M hrs a j) = m
  · simp only [if_pos h, Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun b _ =>
      (measurable_Lam0u_entry M hrs a b).mul (measurable_Sbotu_entry M hrs b j))
  · simp only [if_neg h]; exact measurable_const

/-- `shiftCore` is measurable (reconstruct via the `splitOfCoreSet.symm` ME, then `shiftFull`). -/
theorem measurable_shiftCore (M : Fin 3 → ℕ) (hrs : r + s = M 1) :
    Measurable (shiftCore M hrs) := by
  apply measurable_pi_iff.2
  intro jc
  unfold shiftCore
  -- the reconstruction `q ↦ splitOfCoreSet.symm (q.1, (0, q.2))` is measurable
  have hrecon : Measurable (fun q : (Fin 0 → ℝ) × (Fin (topCoords M hrs)ᶜ.card → ℝ) =>
      (splitOfCoreSet (topCoords M hrs)).symm
        (q.1, ((0 : Fin (topCoords M hrs).card → ℝ), q.2))) :=
    (splitOfCoreSet (topCoords M hrs)).symm.measurable.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact (measurable_shiftFull_coord M hrs _).comp hrecon

/-- `psiMap` as an explicit `Function.comp` triple (`rfl`). -/
theorem psiMap_eq_comp (M : Fin 3 → ℕ) (hrs : r + s = M 1) :
    psiMap M hrs = ⇑(paramsEquivFlat M) ∘ ⇑(flatEquivOf M (slotEquiv M)).symm
      ∘ shearMBody (topCoords M hrs) (shiftCore M hrs) := rfl

/-- **`ψ = psiMap` is measure-preserving** (the three banked MP factors composed). -/
theorem measurePreserving_psiMap (M : Fin 3 → ℕ) (hrs : r + s = M 1) :
    MeasurePreserving (psiMap M hrs) (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume := by
  rw [psiMap_eq_comp]
  have hshear : MeasurePreserving (shearMBody (topCoords M hrs) (shiftCore M hrs))
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume :=
    measurePreserving_shearMBody (topCoords M hrs) (shiftCore M hrs) (measurable_shiftCore M hrs)
  have hpack : MeasurePreserving (⇑(flatEquivOf M (slotEquiv M)).symm)
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) (volume : Measure (Params M)) :=
    (measurePreserving_flatEquivOf M (slotEquiv M)).symm _
  exact (measurePreserving_paramsEquivFlat M).comp (hpack.comp hshear)

/-- **`ψ = psiMap` is a measurable embedding** (a composition of measurable equivalences). -/
theorem measurableEmbedding_psiMap (M : Fin 3 → ℕ) (hrs : r + s = M 1) :
    MeasurableEmbedding (psiMap M hrs) := by
  have h1 : MeasurableEmbedding (shearMBody (topCoords M hrs) (shiftCore M hrs)) :=
    measurableEmbedding_shearMBody (topCoords M hrs) (shiftCore M hrs) (measurable_shiftCore M hrs)
  have h2 : MeasurableEmbedding (⇑(flatEquivOf M (slotEquiv M)).symm) :=
    (flatEquivOf M (slotEquiv M)).symm.measurableEmbedding
  have h3 : MeasurableEmbedding (⇑(paramsEquivFlat M)) := (paramsEquivFlat M).measurableEmbedding
  have hpsi : psiMap M hrs = (⇑(paramsEquivFlat M) ∘ ⇑(flatEquivOf M (slotEquiv M)).symm)
      ∘ shearMBody (topCoords M hrs) (shiftCore M hrs) := rfl
  rw [hpsi]
  exact (h3.comp h2).comp h1

/-! ## The radial blow-up `R = Rmap` certificates (fderiv / injOn / |det| = |u p|^h) -/

/-- `topCoords.card = r·(M 2)` (the injective image of `Fin r × Fin (M 2)`). -/
theorem topCoords_card (M : Fin 3 → ℕ) (hrs : r + s = M 1) :
    (topCoords M hrs).card = r * M 2 := by
  rw [topCoords, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  · -- the map `(a,j) ↦ coordOf (topSlot a j)` is injective
    rintro ⟨a, j⟩ ⟨a', j'⟩ h
    have hslot : topSlot M hrs a j = topSlot M hrs a' j' := coordOf_injective M h
    have hj : j = j' := Fin.ext (congrArg (fun q : FlatIdx M => (q.2.val : ℕ)) hslot)
    have hrow : (deepWidthEquiv hrs (Sum.inl a) : Fin (M 1)) = deepWidthEquiv hrs (Sum.inl a') :=
      Fin.ext (congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) hslot)
    have ha : a = a' := Sum.inl_injective ((deepWidthEquiv hrs).injective hrow)
    rw [ha, hj]

/-- The fderiv carrier `Dmap u := pivotBlowupOnDeriv topCoords pivotCoord u`. -/
noncomputable def Dmap (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ) :=
  pivotBlowupOnDeriv (topCoords M hrs) (pivotCoord M hrs hr hc) u

/-- `Rmap` has fderiv `Dmap` on any set (the banked `pivotBlowupOn_hasFDerivWithinAt`). -/
theorem Rmap_hasFDerivWithinAt (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (S : Set (Fin (routeMAmbient M) → ℝ)) (u : Fin (routeMAmbient M) → ℝ) :
    HasFDerivWithinAt (Rmap M hrs hr hc) (Dmap M hrs hr hc u) S u :=
  pivotBlowupOn_hasFDerivWithinAt _ _ S u

/-- `Rmap` is injective off `{u pivot = 0}` (the banked `pivotBlowupOn_injOn`). -/
theorem Rmap_injOn (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (S : Set (Fin (routeMAmbient M) → ℝ)) :
    Set.InjOn (Rmap M hrs hr hc) (S \ {x | x (pivotCoord M hrs hr hc) = 0}) :=
  pivotBlowupOn_injOn _ _ S

/-- `|det (Dmap u)| = |u pivot|^(r·(M 2) − 1)` (the banked `pivotBlowupOnDeriv_det`, `card = r·c`). -/
theorem Dmap_abs_det (M : Fin 3 → ℕ) (hrs : r + s = M 1) (hr : 0 < r) (hc : 0 < M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    |(Dmap M hrs hr hc u).det| = |u (pivotCoord M hrs hr hc)| ^ (r * M 2 - 1) := by
  rw [Dmap, pivotBlowupOnDeriv_det _ _ (pivotCoord_mem M hrs hr hc), topCoords_card, abs_pow]

end DLNFibre.DLN.RLCT
