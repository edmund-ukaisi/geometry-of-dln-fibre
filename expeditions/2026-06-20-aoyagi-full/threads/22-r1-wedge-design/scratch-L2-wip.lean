import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGE
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.Case222Resolution

open MeasureTheory
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## L=2 (3,3,4) achiever wedge — Route 2 scaffolding -/

/-- The concrete (3,3,4) network. -/
abbrev M334 : Fin 3 → ℕ := ![3, 3, 4]

/-- `minAdm M334 = 8`. -/
theorem minAdm_M334 : minAdm M334 = 8 := by
  rw [← minAdmRec_eq_minAdm]; decide

/-- `flatDim M334 = 21` (= 3·3 + 3·4). -/
theorem flatDim_M334 : flatDim M334 = 21 := by decide

/-! ### Entry indices in `FlatIdx M334` -/

/-- A layer-0 entry `(0, i, j)` of `A1 : Fin 3 × Fin 3`. -/
def fidx0 (i j : Fin 3) : FlatIdx M334 := ⟨⟨0, i⟩, j⟩

/-- A layer-1 entry `(1, i, j)` of `A2 : Fin 3 × Fin 4`. -/
def fidx1 (i : Fin 3) (j : Fin 4) : FlatIdx M334 := ⟨⟨1, i⟩, j⟩

/-- The pivot entry: `A2` top-left, `(s,i,j) = (1,0,0)`. -/
def pivotEntry : FlatIdx M334 := fidx1 0 0

/-- The 8 active entries: `A1`'s bottom-right `2×2` and `A2`'s top row. -/
def activeEntries : Finset (FlatIdx M334) :=
  { fidx0 1 1, fidx0 1 2, fidx0 2 1, fidx0 2 2,
    fidx1 0 0, fidx1 0 1, fidx1 0 2, fidx1 0 3 }

/-- The flat active set: the `equivFin`-images of the active entries. -/
noncomputable def activeFlat : Finset (Fin (flatDim M334)) :=
  activeEntries.image (Fintype.equivFin (FlatIdx M334))

/-- The flat pivot coordinate. -/
noncomputable def pivotFlat : Fin (flatDim M334) := (Fintype.equivFin (FlatIdx M334)) pivotEntry

/-- The 8 active entries are distinct (kernel-decidable on the concrete `FlatIdx M334`). -/
theorem activeEntries_card : activeEntries.card = 8 := by decide

/-- The pivot entry is among the active entries. -/
theorem pivotEntry_mem_active : pivotEntry ∈ activeEntries := by decide

/-- `activeFlat.card = 8` (image under the injective `equivFin`). -/
theorem activeFlat_card : activeFlat.card = 8 := by
  have h : (Finset.image (⇑(Fintype.equivFin (FlatIdx M334))) activeEntries).card
      = activeEntries.card :=
    Finset.card_image_of_injOn (fun a _ b _ hab => (Fintype.equivFin (FlatIdx M334)).injective hab)
  show (Finset.image (⇑(Fintype.equivFin (FlatIdx M334))) activeEntries).card = 8
  rw [h, activeEntries_card]

/-- `pivotFlat ∈ activeFlat`. -/
theorem pivotFlat_mem_activeFlat : pivotFlat ∈ activeFlat := by
  rw [activeFlat, pivotFlat, Finset.mem_image]
  exact ⟨pivotEntry, pivotEntry_mem_active, rfl⟩

/-- **Inverse-coordinate lemma (`rfl`).** Each matrix entry of `(paramsEquivFlat M).symm x` is the
flat coordinate at the `equivFin`-image of that entry's index. The linchpin of Route 2. -/
theorem paramsEquivFlat_symm_coord (M : Fin 3 → ℕ) (x : Fin (flatDim M) → ℝ)
    (s : Fin 2) (i : Fin (M s.castSucc)) (j : Fin (M s.succ)) :
    ((paramsEquivFlat M).symm x) s i j
      = x ((Fintype.equivFin (FlatIdx M)) (⟨⟨s, i⟩, j⟩ : FlatIdx M)) := rfl

/-- **Membership reflection.** `equivFin e ∈ activeFlat ↔ e ∈ activeEntries`. -/
theorem equivFin_mem_activeFlat (e : FlatIdx M334) :
    (Fintype.equivFin (FlatIdx M334)) e ∈ activeFlat ↔ e ∈ activeEntries := by
  show (Fintype.equivFin (FlatIdx M334)) e
      ∈ activeEntries.image (Fintype.equivFin (FlatIdx M334)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hae⟩
    rwa [(Fintype.equivFin (FlatIdx M334)).injective hae] at ha
  · intro he; exact ⟨e, he, rfl⟩

/-- **Pivot reflection.** `equivFin e = pivotFlat ↔ e = pivotEntry`. -/
theorem equivFin_eq_pivotFlat (e : FlatIdx M334) :
    (Fintype.equivFin (FlatIdx M334)) e = pivotFlat ↔ e = pivotEntry := by
  rw [pivotFlat]
  exact ⟨fun h => (Fintype.equivFin (FlatIdx M334)).injective h, fun h => by rw [h]⟩

/-! ### The wedged parameter and its per-entry values -/

/-- The wedged parameter `A(x) = (paramsEquivFlat).symm (pivotBlowupOn activeFlat pivotFlat x)` —
the single weighted radial blow-up pulled back into `Params M334`. The pivot coord is the radial
variable `u = x pivotFlat`; the 8 active entries are scaled by `u`. -/
noncomputable def wedgeParam (x : Fin (flatDim M334) → ℝ) : Params M334 :=
  (paramsEquivFlat M334).symm (pivotBlowupOn activeFlat pivotFlat x)

/-- **Per-entry value of the wedged parameter** (cascade form). The pivot entry is `x pivotFlat`;
an active entry is `x pivotFlat * x (equivFin e)`; an inactive entry is `x (equivFin e)`. -/
theorem wedgeParam_entry (x : Fin (flatDim M334) → ℝ)
    (s : Fin 2) (i : Fin (M334 s.castSucc)) (j : Fin (M334 s.succ)) :
    wedgeParam x s i j
      = (if (⟨⟨s, i⟩, j⟩ : FlatIdx M334) = pivotEntry then x pivotFlat
         else if (⟨⟨s, i⟩, j⟩ : FlatIdx M334) ∈ activeEntries
           then x pivotFlat * x ((Fintype.equivFin (FlatIdx M334)) ⟨⟨s, i⟩, j⟩)
           else x ((Fintype.equivFin (FlatIdx M334)) ⟨⟨s, i⟩, j⟩)) := by
  rw [wedgeParam, paramsEquivFlat_symm_coord]
  show pivotBlowupOn activeFlat pivotFlat x ((Fintype.equivFin (FlatIdx M334)) ⟨⟨s, i⟩, j⟩) = _
  simp only [pivotBlowupOn]
  have hp := equivFin_eq_pivotFlat ⟨⟨s, i⟩, j⟩
  have ha := equivFin_mem_activeFlat ⟨⟨s, i⟩, j⟩
  split_ifs with c1 c2 c3 c4 c5 c6 <;>
    first
      | rfl
      | (exact absurd (hp.mpr ‹_›) ‹_›)
      | (exact absurd (hp.mp ‹_›) ‹_›)
      | (exact absurd (ha.mpr ‹_›) ‹_›)
      | (exact absurd (ha.mp ‹_›) ‹_›)

end DLNFibre.DLN.RLCT
