import Mathlib.Order.Height
import Mathlib.Order.Hom.Basic

open Set

example {α β : Type*} [PartialOrder α] [PartialOrder β]
    (S : Set α) (T : Set β) (e : ↥S ≃o ↥T) :
    S.chainHeight (· < ·) = T.chainHeight (· < ·) := by
  rw [← Set.chainHeight_coe_univ S (· < ·), ← Set.chainHeight_coe_univ T (· < ·)]
  have himg : e.toRelIsoLT '' (Set.univ : Set ↥S) = Set.univ := by
    rw [Set.image_univ]; exact e.toEquiv.surjective.range_eq
  have h := Set.chainHeight_eq_of_relIso (Set.univ : Set ↥S) e.toRelIsoLT
  rw [himg] at h
  exact h.symm
