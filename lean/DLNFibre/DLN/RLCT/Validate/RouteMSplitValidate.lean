import DLNFibre.DLN.RLCT.Foundations.CoreSplitMP

/-!
# `RouteMSplitValidate` — the general `splitOfPartition` reproduces the worked `(2,3,1)` block split

Structural sanity check (spec-first discipline, #159 sub-tide 2): the convention-agnostic
`splitOfPartition` (in `Foundations.CoreSplitMP`) subsumes the hand-built `split231` —
`(Fin 9 → ℝ) ≃ᵐ (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ))` with the SAME block assignment

    Reg = {coord 0},  Core = {coords 6, 7},  Spec = {coords 1, 2, 3, 4, 5, 8}

(`RouteM231Smeared`'s `split231` peels coord `0`, then coords `6, 7`; everything else is `Spec`).
We build the concrete index equiv `e231 : Fin 1 ⊕ (Fin 2 ⊕ Fin 6) ≃ Fin 9` carrying that
assignment and confirm `splitOfPartition e231` reads each block off the right original coordinates
(`splitOfPartition_reg`/`_core`/`_spec`). This validates the cardinality `9 = 1 + 2 + 6` and the
FlatIdx alignment on the worked instance, WITHOUT re-importing the `RouteM231Smeared` chart (the
`Foundations` primitive stays network-free; this Validate file is the cross-check).
-/

open MeasureTheory

namespace DLNFibre.DLN.RLCT

/-- The `(2,3,1)` block-assignment map `Fin 1 ⊕ (Fin 2 ⊕ Fin 6) → Fin 9`:
`Reg 0 ↦ 0`; `Core {0,1} ↦ {6,7}`; `Spec {0,1,2,3,4,5} ↦ {1,2,3,4,5,8}`. -/
def e231Fun : (Fin 1 ⊕ (Fin 2 ⊕ Fin 6)) → Fin 9
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl j) => ![6, 7] j
  | Sum.inr (Sum.inr k) => ![1, 2, 3, 4, 5, 8] k

/-- `e231Fun` is a bijection (the `9 = 1 + 2 + 6` block partition is a genuine permutation of
`Fin 9`); decided by kernel reduction. -/
theorem e231Fun_bijective : Function.Bijective e231Fun := by
  constructor
  · intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [e231Fun]
  · decide +kernel

/-- The concrete index equiv `Fin 1 ⊕ (Fin 2 ⊕ Fin 6) ≃ Fin 9` for the `(2,3,1)` block split. -/
noncomputable def e231 : (Fin 1 ⊕ (Fin 2 ⊕ Fin 6)) ≃ Fin 9 :=
  Equiv.ofBijective e231Fun e231Fun_bijective

/-- **The `(2,3,1)` split is measure-preserving** — the general primitive, applied to `e231`. -/
theorem measurePreserving_splitOfPartition_e231 :
    MeasurePreserving (splitOfPartition e231) (volume : Measure (Fin 9 → ℝ)) volume :=
  measurePreserving_splitOfPartition e231

/-- **Reg reads coord 0** — `(split u).1 0 = u 0`. -/
theorem split_e231_reg (u : Fin 9 → ℝ) : (splitOfPartition e231 u).1 0 = u 0 := by
  rw [splitOfPartition_reg]; rfl

/-- **Core reads coords 6, 7** — `(split u).2.1 = ![u 6, u 7]`. -/
theorem split_e231_core (u : Fin 9 → ℝ) :
    (splitOfPartition e231 u).2.1 0 = u 6 ∧ (splitOfPartition e231 u).2.1 1 = u 7 := by
  refine ⟨?_, ?_⟩ <;> rw [splitOfPartition_core] <;> rfl

/-- **Spec reads coords 1,2,3,4,5,8** — `(split u).2.2 = ![u 1, u 2, u 3, u 4, u 5, u 8]`. -/
theorem split_e231_spec (u : Fin 9 → ℝ) :
    (splitOfPartition e231 u).2.2 0 = u 1 ∧ (splitOfPartition e231 u).2.2 1 = u 2 ∧
    (splitOfPartition e231 u).2.2 2 = u 3 ∧ (splitOfPartition e231 u).2.2 3 = u 4 ∧
    (splitOfPartition e231 u).2.2 4 = u 5 ∧ (splitOfPartition e231 u).2.2 5 = u 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [splitOfPartition_spec] <;> rfl

end DLNFibre.DLN.RLCT
