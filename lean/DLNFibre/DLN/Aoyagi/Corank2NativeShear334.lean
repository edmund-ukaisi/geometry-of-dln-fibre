import DLNFibre.DLN.Aoyagi.Corank2FanCover334

/-!
# `DLN.Aoyagi.Corank2NativeShear334` — the 9 born-native W3-clean σ_p block shears (3,3,4)

The born-native per-pivot node-1 shears of the (3,3,4) fan (shape (b), `assembly-extraction.md` §2):
one shear `σ_p = blockShear (qdisp t1P· t2P·)` per A0-dominant, keyed by the surviving `A0[i,j]`
entry's coordinate slot `p ∈ {0,1,2,3,4,5,6,7,20}`. The `t1P·`/`t2P·` are the **DIRECT** §2 signed
term data (`φ_(i,j)[k] = shearH_disp(u∘σ)[σ(k)]`, σ = colswap(j)∘rowswap(i)); NOT the
`σ⁻¹ ∘ shearH ∘ σ` conjugate (that is the pen-and-paper DESCRIPTION only — this construction is
grep-clean of any orbit-conjugation / transport-chart machinery, in the def and in the proof).

`pivot slot 20 = dom(0,0)` is the landed canonical `shearPhiH`; the other eight are its row/column
swapped siblings. Each is a rank-≤2 quadratic block shear: every corrected coordinate is a sum of ≤ 2
signed products of KEPT coordinates, so `‖·‖ ≤ 2‖x‖²` (box inflation `C = 2`, `r ↦ r + 2r²`) and its
Jacobian is exactly `1` (unipotent shear-pin). The generic engine (`§0`, `qdisp`) proves
keep/read/norm-bound/covers/`|jacDet|=1`/injective ONCE for any rank-≤2 signed quadratic displacement
whose term sources are kept; the nine shears are its instances (`hsrc` discharged by `decide`).

## Scope
- IN: the 9 native displacements + their box-containment (`covers_P·`, `nativeSel_covers`),
  `|jacDet| = 1` (`nativeSel_jacDet`), injectivity, differentiability — the node-1 shear layer.
- OUT: the fan assembly + `hcover` (`Corank2NativeFan334`); the entry-equalities `hentry` (the (B)
  seat); the per-leaf `jac`/`divisorMin` (the (C) seat).
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.GeneralGeoAtlas
open DLNFibre.DLN.Aoyagi.Corank2FanCover334

namespace DLNFibre.DLN.Aoyagi.NativeShear334

/-! ## §0 — the generic rank-≤2 signed quadratic block-shear engine

A displacement whose coordinate `i` is a sum of ≤ 2 signed products `±xₐ·x_b`, encoded by two "term
families" `t1 t2 : Fin D → Option (Bool × Fin D × Fin D)` (`true`=+, `false`=−). When every term's
sources are KEPT (`srcKept`, disjoint from the corrected coordinates — decidable, so `by decide`), the
shear `blockShear (qdisp t1 t2)` box-contains with inflation `r ↦ r + 2r²`, has `|jacDet| = 1`, and is
injective. -/

variable {D : ℕ}

/-- A signed single quadratic term family at coordinate `i`:
`t i = some (sg, a, b) ↦ (±1)·xₐ·x_b`, `t i = none ↦ 0`. -/
def sterm (t : Fin D → Option (Bool × Fin D × Fin D)) (x : Fin D → ℝ) (i : Fin D) : ℝ :=
  (t i).elim 0 (fun q => (if q.1 then (1 : ℝ) else -1) * (x q.2.1 * x q.2.2))

theorem sterm_none (t : Fin D → Option (Bool × Fin D × Fin D)) (x : Fin D → ℝ) {i : Fin D}
    (h : t i = none) : sterm t x i = 0 := by simp [sterm, h]

theorem sterm_some (t : Fin D → Option (Bool × Fin D × Fin D)) (x : Fin D → ℝ)
    {i a b : Fin D} {sg : Bool} (h : t i = some (sg, a, b)) :
    sterm t x i = (if sg then (1 : ℝ) else -1) * (x a * x b) := by simp [sterm, h]

/-- Per-coordinate bound `|sterm t x i| ≤ r²` when `‖x‖ ≤ r` (the sign has `|±1| = 1`). -/
theorem sterm_abs_le {t : Fin D → Option (Bool × Fin D × Fin D)} {r : ℝ} (hr : 0 ≤ r)
    {x : Fin D → ℝ} (hx : ‖x‖ ≤ r) (i : Fin D) : |sterm t x i| ≤ r ^ 2 := by
  cases h : t i with
  | none => rw [sterm_none t x h, abs_zero]; positivity
  | some q =>
    obtain ⟨sg, a, b⟩ := q
    have ha : |x a| ≤ r := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x a).trans hx
    have hb : |x b| ≤ r := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x b).trans hx
    have hsg : |(if sg then (1 : ℝ) else -1)| = 1 := by cases sg <;> simp
    rw [sterm_some t x h, abs_mul, hsg, one_mul, abs_mul]
    calc |x a| * |x b| ≤ r * r := mul_le_mul ha hb (abs_nonneg _) hr
      _ = r ^ 2 := by ring

/-- The rank-≤2 signed quadratic displacement `x i ↦ (sterm t1 x i) + (sterm t2 x i)`. -/
def qdisp (t1 t2 : Fin D → Option (Bool × Fin D × Fin D)) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun x i => sterm t1 x i + sterm t2 x i

/-- The kept coordinates: neither term family touches `i`. Reducible so `qkeep` is decidable
(needed for the `by decide` source checks). -/
abbrev qkeep (t1 t2 : Fin D → Option (Bool × Fin D × Fin D)) : Fin D → Prop :=
  fun i => t1 i = none ∧ t2 i = none

/-- The source condition: every term of `t` reads only KEPT coordinates. Reducible so the finite
`Decidable` instance is found, hence `by decide` at each concrete shear. -/
abbrev srcKept (t1 t2 t : Fin D → Option (Bool × Fin D × Fin D)) : Prop :=
  ∀ i sg a b, t i = some (sg, a, b) → qkeep t1 t2 a ∧ qkeep t1 t2 b

theorem qdisp_keep (t1 t2 : Fin D → Option (Bool × Fin D × Fin D)) (u : Fin D → ℝ) (i : Fin D)
    (hi : qkeep t1 t2 i) : qdisp t1 t2 u i = 0 := by
  obtain ⟨h1, h2⟩ := hi
  simp only [qdisp, sterm_none t1 u h1, sterm_none t2 u h2, add_zero]

theorem qdisp_read (t1 t2 : Fin D → Option (Bool × Fin D × Fin D))
    (hsrc1 : srcKept t1 t2 t1) (hsrc2 : srcKept t1 t2 t2)
    (u v : Fin D → ℝ) (h : ∀ i, qkeep t1 t2 i → u i = v i) : qdisp t1 t2 u = qdisp t1 t2 v := by
  funext i
  simp only [qdisp]
  congr 1
  · cases hti : t1 i with
    | none => rw [sterm_none t1 u hti, sterm_none t1 v hti]
    | some q =>
      obtain ⟨sg, a, b⟩ := q
      obtain ⟨hka, hkb⟩ := hsrc1 i sg a b hti
      rw [sterm_some t1 u hti, sterm_some t1 v hti, h a hka, h b hkb]
  · cases hti : t2 i with
    | none => rw [sterm_none t2 u hti, sterm_none t2 v hti]
    | some q =>
      obtain ⟨sg, a, b⟩ := q
      obtain ⟨hka, hkb⟩ := hsrc2 i sg a b hti
      rw [sterm_some t2 u hti, sterm_some t2 v hti, h a hka, h b hkb]

theorem qdisp_norm_bound (t1 t2 : Fin D → Option (Bool × Fin D × Fin D)) {r : ℝ}
    {x : Fin D → ℝ} (hx : ‖x‖ ≤ r) : ‖qdisp t1 t2 x‖ ≤ 2 * r ^ 2 := by
  have hr : 0 ≤ r := le_trans (norm_nonneg x) hx
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  calc |qdisp t1 t2 x i| ≤ |sterm t1 x i| + |sterm t2 x i| := abs_add_le _ _
    _ ≤ r ^ 2 + r ^ 2 := add_le_add (sterm_abs_le hr hx i) (sterm_abs_le hr hx i)
    _ = 2 * r ^ 2 := by ring

theorem differentiable_sterm (t : Fin D → Option (Bool × Fin D × Fin D)) (i : Fin D) :
    Differentiable ℝ (fun x => sterm t x i) := by
  cases h : t i with
  | none =>
    have he : (fun x : Fin D → ℝ => sterm t x i) = fun _ => (0 : ℝ) :=
      funext (fun x => sterm_none t x h)
    rw [he]; exact differentiable_const 0
  | some q =>
    obtain ⟨sg, a, b⟩ := q
    have he : (fun x : Fin D → ℝ => sterm t x i) = fun x => (if sg then (1 : ℝ) else -1) * (x a * x b) :=
      funext (fun x => sterm_some t x h)
    rw [he]; fun_prop

theorem differentiable_qdisp (t1 t2 : Fin D → Option (Bool × Fin D × Fin D)) :
    Differentiable ℝ (qdisp t1 t2) :=
  differentiable_pi.2 (fun i => (differentiable_sterm t1 i).add (differentiable_sterm t2 i))

/-- **The generic box-containment** for a rank-≤2 signed quadratic shear (inflation `r ↦ r + 2r²`). -/
theorem qShear_covers (t1 t2 : Fin D → Option (Bool × Fin D × Fin D))
    (hsrc1 : srcKept t1 t2 t1) (hsrc2 : srcKept t1 t2 t2) {r : ℝ} :
    closedBall (0 : Fin D → ℝ) r ⊆ blockShear (qdisp t1 t2) '' closedBall 0 (r + 2 * r ^ 2) :=
  blockShear_covers_scaled (qkeep t1 t2) (qdisp_keep t1 t2) (qdisp_read t1 t2 hsrc1 hsrc2)
    (fun x hx => qdisp_norm_bound t1 t2 hx)

theorem jacDet_qShear (t1 t2 : Fin D → Option (Bool × Fin D × Fin D))
    (hsrc1 : srcKept t1 t2 t1) (hsrc2 : srcKept t1 t2 t2) (u : Fin D → ℝ) :
    jacDet (blockShear (qdisp t1 t2)) u = 1 :=
  jacDet_blockShear (qdisp t1 t2) (qkeep t1 t2) (differentiable_qdisp t1 t2)
    (qdisp_keep t1 t2) (qdisp_read t1 t2 hsrc1 hsrc2) u

theorem injective_qShear (t1 t2 : Fin D → Option (Bool × Fin D × Fin D))
    (hsrc1 : srcKept t1 t2 t1) (hsrc2 : srcKept t1 t2 t2) :
    Function.Injective (blockShear (qdisp t1 t2)) :=
  injective_blockShear (qdisp t1 t2) (qkeep t1 t2) (qdisp_keep t1 t2)
    (qdisp_read t1 t2 hsrc1 hsrc2)

/-! ## §1 — the 9 native shears (pivot slot `p`), one per A0-dominant. Data (`t1P·`/`t2P·`) is the
DIRECT §2 signed-term encoding, machine-generated from `extract_native_shears.py` (cross-checked
exact). `pivot slot 20 = dom(0,0) = shearPhiH`; `srcKept` discharged by `decide`. -/

-- BEGIN generated (extract_native_shears.py; assembly-extraction.md §2)
/-! ### pivot slot 0  (dom(1, 0)) -/
/-- Native shear term data 1, pivot slot 0 (dom(1, 0)); `true`=+, `false`=−. -/
def t1P0 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 2 then some (true, 20, 4)
  else   if i = 3 then some (true, 20, 6)
  else   if i = 5 then some (true, 1, 4)
  else   if i = 7 then some (true, 1, 6)
  else   if i = 12 then some (false, 1, 16)
  else   if i = 13 then some (false, 1, 17)
  else   if i = 14 then some (false, 1, 18)
  else   if i = 15 then some (false, 1, 19)
  else none

/-- Native shear term data 2, pivot slot 0 (dom(1, 0)). -/
def t2P0 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 12 then some (false, 20, 8)
  else   if i = 13 then some (false, 20, 9)
  else   if i = 14 then some (false, 10, 20)
  else   if i = 15 then some (false, 11, 20)
  else none

theorem hsrc1_P0 : srcKept t1P0 t2P0 t1P0 := by decide
theorem hsrc2_P0 : srcKept t1P0 t2P0 t2P0 := by decide
/-- Native shear at pivot slot 0 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P0 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P0 t2P0) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P0 t2P0 hsrc1_P0 hsrc2_P0
theorem jacDet_P0 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P0 t2P0)) u = 1 :=
  jacDet_qShear t1P0 t2P0 hsrc1_P0 hsrc2_P0 u
theorem injective_P0 : Function.Injective (blockShear (qdisp t1P0 t2P0)) :=
  injective_qShear t1P0 t2P0 hsrc1_P0 hsrc2_P0

/-! ### pivot slot 1  (dom(2, 0)) -/
/-- Native shear term data 1, pivot slot 1 (dom(2, 0)); `true`=+, `false`=−. -/
def t1P1 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 2 then some (true, 20, 5)
  else   if i = 3 then some (true, 20, 7)
  else   if i = 4 then some (true, 0, 5)
  else   if i = 6 then some (true, 0, 7)
  else   if i = 16 then some (false, 0, 12)
  else   if i = 17 then some (false, 0, 13)
  else   if i = 18 then some (false, 0, 14)
  else   if i = 19 then some (false, 0, 15)
  else none

/-- Native shear term data 2, pivot slot 1 (dom(2, 0)). -/
def t2P1 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 16 then some (false, 20, 8)
  else   if i = 17 then some (false, 20, 9)
  else   if i = 18 then some (false, 10, 20)
  else   if i = 19 then some (false, 11, 20)
  else none

theorem hsrc1_P1 : srcKept t1P1 t2P1 t1P1 := by decide
theorem hsrc2_P1 : srcKept t1P1 t2P1 t2P1 := by decide
/-- Native shear at pivot slot 1 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P1 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P1 t2P1) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P1 t2P1 hsrc1_P1 hsrc2_P1
theorem jacDet_P1 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P1 t2P1)) u = 1 :=
  jacDet_qShear t1P1 t2P1 hsrc1_P1 hsrc2_P1 u
theorem injective_P1 : Function.Injective (blockShear (qdisp t1P1 t2P1)) :=
  injective_qShear t1P1 t2P1 hsrc1_P1 hsrc2_P1

/-! ### pivot slot 2  (dom(0, 1)) -/
/-- Native shear term data 1, pivot slot 2 (dom(0, 1)); `true`=+, `false`=−. -/
def t1P2 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 0 then some (true, 20, 4)
  else   if i = 1 then some (true, 20, 5)
  else   if i = 6 then some (true, 3, 4)
  else   if i = 7 then some (true, 3, 5)
  else   if i = 8 then some (false, 12, 4)
  else   if i = 9 then some (false, 13, 4)
  else   if i = 10 then some (false, 14, 4)
  else   if i = 11 then some (false, 15, 4)
  else none

/-- Native shear term data 2, pivot slot 2 (dom(0, 1)). -/
def t2P2 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 8 then some (false, 16, 5)
  else   if i = 9 then some (false, 17, 5)
  else   if i = 10 then some (false, 18, 5)
  else   if i = 11 then some (false, 19, 5)
  else none

theorem hsrc1_P2 : srcKept t1P2 t2P2 t1P2 := by decide
theorem hsrc2_P2 : srcKept t1P2 t2P2 t2P2 := by decide
/-- Native shear at pivot slot 2 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P2 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P2 t2P2) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P2 t2P2 hsrc1_P2 hsrc2_P2
theorem jacDet_P2 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P2 t2P2)) u = 1 :=
  jacDet_qShear t1P2 t2P2 hsrc1_P2 hsrc2_P2 u
theorem injective_P2 : Function.Injective (blockShear (qdisp t1P2 t2P2)) :=
  injective_qShear t1P2 t2P2 hsrc1_P2 hsrc2_P2

/-! ### pivot slot 3  (dom(0, 2)) -/
/-- Native shear term data 1, pivot slot 3 (dom(0, 2)); `true`=+, `false`=−. -/
def t1P3 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 0 then some (true, 20, 6)
  else   if i = 1 then some (true, 20, 7)
  else   if i = 4 then some (true, 2, 6)
  else   if i = 5 then some (true, 2, 7)
  else   if i = 8 then some (false, 12, 6)
  else   if i = 9 then some (false, 13, 6)
  else   if i = 10 then some (false, 14, 6)
  else   if i = 11 then some (false, 15, 6)
  else none

/-- Native shear term data 2, pivot slot 3 (dom(0, 2)). -/
def t2P3 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 8 then some (false, 16, 7)
  else   if i = 9 then some (false, 17, 7)
  else   if i = 10 then some (false, 18, 7)
  else   if i = 11 then some (false, 19, 7)
  else none

theorem hsrc1_P3 : srcKept t1P3 t2P3 t1P3 := by decide
theorem hsrc2_P3 : srcKept t1P3 t2P3 t2P3 := by decide
/-- Native shear at pivot slot 3 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P3 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P3 t2P3) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P3 t2P3 hsrc1_P3 hsrc2_P3
theorem jacDet_P3 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P3 t2P3)) u = 1 :=
  jacDet_qShear t1P3 t2P3 hsrc1_P3 hsrc2_P3 u
theorem injective_P3 : Function.Injective (blockShear (qdisp t1P3 t2P3)) :=
  injective_qShear t1P3 t2P3 hsrc1_P3 hsrc2_P3

/-! ### pivot slot 4  (dom(1, 1)) -/
/-- Native shear term data 1, pivot slot 4 (dom(1, 1)); `true`=+, `false`=−. -/
def t1P4 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 1 then some (true, 0, 5)
  else   if i = 3 then some (true, 2, 6)
  else   if i = 7 then some (true, 5, 6)
  else   if i = 12 then some (false, 16, 5)
  else   if i = 13 then some (false, 17, 5)
  else   if i = 14 then some (false, 10, 2)
  else   if i = 15 then some (false, 11, 2)
  else   if i = 20 then some (true, 0, 2)
  else none

/-- Native shear term data 2, pivot slot 4 (dom(1, 1)). -/
def t2P4 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 12 then some (false, 2, 8)
  else   if i = 13 then some (false, 2, 9)
  else   if i = 14 then some (false, 18, 5)
  else   if i = 15 then some (false, 19, 5)
  else none

theorem hsrc1_P4 : srcKept t1P4 t2P4 t1P4 := by decide
theorem hsrc2_P4 : srcKept t1P4 t2P4 t2P4 := by decide
/-- Native shear at pivot slot 4 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P4 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P4 t2P4) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P4 t2P4 hsrc1_P4 hsrc2_P4
theorem jacDet_P4 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P4 t2P4)) u = 1 :=
  jacDet_qShear t1P4 t2P4 hsrc1_P4 hsrc2_P4 u
theorem injective_P4 : Function.Injective (blockShear (qdisp t1P4 t2P4)) :=
  injective_qShear t1P4 t2P4 hsrc1_P4 hsrc2_P4

/-! ### pivot slot 5  (dom(2, 1)) -/
/-- Native shear term data 1, pivot slot 5 (dom(2, 1)); `true`=+, `false`=−. -/
def t1P5 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 0 then some (true, 1, 4)
  else   if i = 3 then some (true, 2, 7)
  else   if i = 6 then some (true, 4, 7)
  else   if i = 16 then some (false, 12, 4)
  else   if i = 17 then some (false, 13, 4)
  else   if i = 18 then some (false, 10, 2)
  else   if i = 19 then some (false, 11, 2)
  else   if i = 20 then some (true, 1, 2)
  else none

/-- Native shear term data 2, pivot slot 5 (dom(2, 1)). -/
def t2P5 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 16 then some (false, 2, 8)
  else   if i = 17 then some (false, 2, 9)
  else   if i = 18 then some (false, 14, 4)
  else   if i = 19 then some (false, 15, 4)
  else none

theorem hsrc1_P5 : srcKept t1P5 t2P5 t1P5 := by decide
theorem hsrc2_P5 : srcKept t1P5 t2P5 t2P5 := by decide
/-- Native shear at pivot slot 5 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P5 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P5 t2P5) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P5 t2P5 hsrc1_P5 hsrc2_P5
theorem jacDet_P5 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P5 t2P5)) u = 1 :=
  jacDet_qShear t1P5 t2P5 hsrc1_P5 hsrc2_P5 u
theorem injective_P5 : Function.Injective (blockShear (qdisp t1P5 t2P5)) :=
  injective_qShear t1P5 t2P5 hsrc1_P5 hsrc2_P5

/-! ### pivot slot 6  (dom(1, 2)) -/
/-- Native shear term data 1, pivot slot 6 (dom(1, 2)); `true`=+, `false`=−. -/
def t1P6 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 1 then some (true, 0, 7)
  else   if i = 2 then some (true, 3, 4)
  else   if i = 5 then some (true, 4, 7)
  else   if i = 12 then some (false, 16, 7)
  else   if i = 13 then some (false, 17, 7)
  else   if i = 14 then some (false, 10, 3)
  else   if i = 15 then some (false, 11, 3)
  else   if i = 20 then some (true, 0, 3)
  else none

/-- Native shear term data 2, pivot slot 6 (dom(1, 2)). -/
def t2P6 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 12 then some (false, 3, 8)
  else   if i = 13 then some (false, 3, 9)
  else   if i = 14 then some (false, 18, 7)
  else   if i = 15 then some (false, 19, 7)
  else none

theorem hsrc1_P6 : srcKept t1P6 t2P6 t1P6 := by decide
theorem hsrc2_P6 : srcKept t1P6 t2P6 t2P6 := by decide
/-- Native shear at pivot slot 6 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P6 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P6 t2P6) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P6 t2P6 hsrc1_P6 hsrc2_P6
theorem jacDet_P6 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P6 t2P6)) u = 1 :=
  jacDet_qShear t1P6 t2P6 hsrc1_P6 hsrc2_P6 u
theorem injective_P6 : Function.Injective (blockShear (qdisp t1P6 t2P6)) :=
  injective_qShear t1P6 t2P6 hsrc1_P6 hsrc2_P6

/-! ### pivot slot 7  (dom(2, 2)) -/
/-- Native shear term data 1, pivot slot 7 (dom(2, 2)); `true`=+, `false`=−. -/
def t1P7 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 0 then some (true, 1, 6)
  else   if i = 2 then some (true, 3, 5)
  else   if i = 4 then some (true, 5, 6)
  else   if i = 16 then some (false, 12, 6)
  else   if i = 17 then some (false, 13, 6)
  else   if i = 18 then some (false, 10, 3)
  else   if i = 19 then some (false, 11, 3)
  else   if i = 20 then some (true, 1, 3)
  else none

/-- Native shear term data 2, pivot slot 7 (dom(2, 2)). -/
def t2P7 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 16 then some (false, 3, 8)
  else   if i = 17 then some (false, 3, 9)
  else   if i = 18 then some (false, 14, 6)
  else   if i = 19 then some (false, 15, 6)
  else none

theorem hsrc1_P7 : srcKept t1P7 t2P7 t1P7 := by decide
theorem hsrc2_P7 : srcKept t1P7 t2P7 t2P7 := by decide
/-- Native shear at pivot slot 7 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P7 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P7 t2P7) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P7 t2P7 hsrc1_P7 hsrc2_P7
theorem jacDet_P7 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P7 t2P7)) u = 1 :=
  jacDet_qShear t1P7 t2P7 hsrc1_P7 hsrc2_P7 u
theorem injective_P7 : Function.Injective (blockShear (qdisp t1P7 t2P7)) :=
  injective_qShear t1P7 t2P7 hsrc1_P7 hsrc2_P7

/-! ### pivot slot 20  (dom(0, 0)) -/
/-- Native shear term data 1, pivot slot 20 (dom(0, 0)); `true`=+, `false`=−. -/
def t1P20 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 4 then some (true, 0, 2)
  else   if i = 5 then some (true, 1, 2)
  else   if i = 6 then some (true, 0, 3)
  else   if i = 7 then some (true, 1, 3)
  else   if i = 8 then some (false, 0, 12)
  else   if i = 9 then some (false, 0, 13)
  else   if i = 10 then some (false, 0, 14)
  else   if i = 11 then some (false, 0, 15)
  else none

/-- Native shear term data 2, pivot slot 20 (dom(0, 0)). -/
def t2P20 : Fin 21 → Option (Bool × Fin 21 × Fin 21) := fun i =>
  if i = 8 then some (false, 1, 16)
  else   if i = 9 then some (false, 1, 17)
  else   if i = 10 then some (false, 1, 18)
  else   if i = 11 then some (false, 1, 19)
  else none

theorem hsrc1_P20 : srcKept t1P20 t2P20 t1P20 := by decide
theorem hsrc2_P20 : srcKept t1P20 t2P20 t2P20 := by decide
/-- Native shear at pivot slot 20 box-contains (inflation `r ↦ r + 2r²`). -/
theorem covers_P20 {r : ℝ} :
    closedBall (0 : Fin 21 → ℝ) r ⊆ blockShear (qdisp t1P20 t2P20) '' closedBall 0 (r + 2 * r ^ 2) :=
  qShear_covers t1P20 t2P20 hsrc1_P20 hsrc2_P20
theorem jacDet_P20 (u : Fin 21 → ℝ) : jacDet (blockShear (qdisp t1P20 t2P20)) u = 1 :=
  jacDet_qShear t1P20 t2P20 hsrc1_P20 hsrc2_P20 u
theorem injective_P20 : Function.Injective (blockShear (qdisp t1P20 t2P20)) :=
  injective_qShear t1P20 t2P20 hsrc1_P20 hsrc2_P20

-- END generated

/-! ## §2 — the per-pivot node-1 selector `nativeSel` (id off the 9 A0-dominant pivots) -/

/-- **The per-pivot node-1 native shear** `nativeSel p = σ_p` — `blockShear (qdisp t1P· t2P·)` for
each A0-dominant pivot slot `p ∈ {0,1,2,3,4,5,6,7,20}`, `id` elsewhere. The node-1 shear family of the
born-native fan (shape (b)). W3-clean: each branch is the DIRECT §2 native displacement. -/
def nativeSel : Fin 21 → (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun p =>
  if p = 0 then blockShear (qdisp t1P0 t2P0)
  else if p = 1 then blockShear (qdisp t1P1 t2P1)
  else if p = 2 then blockShear (qdisp t1P2 t2P2)
  else if p = 3 then blockShear (qdisp t1P3 t2P3)
  else if p = 4 then blockShear (qdisp t1P4 t2P4)
  else if p = 5 then blockShear (qdisp t1P5 t2P5)
  else if p = 6 then blockShear (qdisp t1P6 t2P6)
  else if p = 7 then blockShear (qdisp t1P7 t2P7)
  else if p = 20 then blockShear (qdisp t1P20 t2P20)
  else id

/-- **Each node-1 native shear box-contains** with the `C = 2` inflation `r ↦ r + 2r²`, at every pivot
of the outer center `{0,1,2,3,4,5,6,7,20}`. Dispatch to the nine `covers_P·`. -/
theorem nativeSel_covers (p : Fin 21)
    (hp : p ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))) {t : ℝ} :
    closedBall (0 : Fin 21 → ℝ) t ⊆ nativeSel p '' closedBall 0 (t + 2 * t ^ 2) := by
  fin_cases hp <;> simp only [nativeSel, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact covers_P0 | exact covers_P1 | exact covers_P2 | exact covers_P3 | exact covers_P4
      | exact covers_P5 | exact covers_P6 | exact covers_P7 | exact covers_P20

/-- **Each node-1 native shear is differentiable.** -/
theorem nativeSel_differentiable (p : Fin 21) : Differentiable ℝ (nativeSel p) := by
  simp only [nativeSel]
  split_ifs <;>
    first
      | exact differentiable_id
      | exact (differentiable_id.add (differentiable_qdisp _ _))

/-- **Each node-1 native shear has `|jacDet| = 1`** (unipotent), at every dominant pivot. -/
theorem nativeSel_jacDet (p : Fin 21)
    (hp : p ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))) (u : Fin 21 → ℝ) :
    jacDet (nativeSel p) u = 1 := by
  fin_cases hp <;> simp only [nativeSel, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact jacDet_P0 u | exact jacDet_P1 u | exact jacDet_P2 u | exact jacDet_P3 u
      | exact jacDet_P4 u | exact jacDet_P5 u | exact jacDet_P6 u | exact jacDet_P7 u
      | exact jacDet_P20 u

end DLNFibre.DLN.Aoyagi.NativeShear334
