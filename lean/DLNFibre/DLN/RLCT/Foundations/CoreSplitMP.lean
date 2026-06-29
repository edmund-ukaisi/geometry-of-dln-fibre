import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.EquivFin

/-!
# `DLNFibre.DLN.RLCT.Foundations.CoreSplitMP` — the general `Reg × Core × Spec` block split

`splitOfPartition` is the GENERAL primitive behind the per-family smeared chart's `shearM`
(#159, sub-tide 2): a measure-preserving block-equivalence
`(Fin N → ℝ) ≃ᵐ (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))`
aligned to an arbitrary index decomposition `e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin N`. It subsumes the
concrete `piFinSuccAbove`-surgery splits `split121`/`split231` (which hand-pick the Reg/Core/Spec
coords for one shape) by reading the block assignment OFF the index-equiv `e`.

It is exactly the input shape `measurePreserving_coreShear_measurable a b c shift` consumes (the
skew-product on `(reg, core, spec)`), so
`shearM = splitOfPartition.symm ∘ coreShear ∘ splitOfPartition`
is measure-preserving for ANY widths.

## The cast-free construction (the spec-first win — NO opaque-width `Fin`-cast thrash)

Reindex the function space along `e` (`piCongrLeft`, a coordinate re-label — never a `Nat`-cast on a
dependent `Fin` type), then split the sum index twice (`sumPiEquivProdPi`):

    (Fin N → ℝ)
      ≃ᵐ[piCongrLeft (·=ℝ) e]              (Fin a ⊕ (Fin b ⊕ Fin c) → ℝ)            -- `.symm`
      ≃ᵐ[sumPiEquivProdPi]                 (Fin a → ℝ) × (Fin b ⊕ Fin c → ℝ)
      ≃ᵐ[prodCongr id sumPiEquivProdPi]    (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))

Each step is a Mathlib `MeasurableEquiv` with a volume-preserving lemma
(`volume_measurePreserving_piCongrLeft`, `volume_measurePreserving_sumPiEquivProdPi`,
`MeasurePreserving.prod`). The whole equivalence preserves `volume` by composition.

The thin `(a, b, c) ↦ FlatIdx M` instance (which flat coords are Reg / Core / Spec) is wired
SEPARATELY by the per-family consumer (it picks `e` from the achiever rank pattern); this
primitive is convention-agnostic.
-/

open MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {N a b c : ℕ}

/-- **The general block split** `(Fin N → ℝ) ≃ᵐ (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))`,
aligned to the index decomposition `e : Fin a ⊕ (Fin b ⊕ Fin c) ≃ Fin N`. The Reg / Core / Spec
blocks are the `inl` / `inr ∘ inl` / `inr ∘ inr` preimages of `e`. -/
noncomputable def splitOfPartition (e : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin N) :
    (Fin N → ℝ) ≃ᵐ (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin a → ℝ))
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin b ⊕ Fin c => ℝ))))

/-- **`splitOfPartition` is measure-preserving.** Each factor is volume-preserving
(`piCongrLeft`, `sumPiEquivProdPi`, the `prodCongr` of `id` with `sumPiEquivProdPi`), so the
composite preserves the product Lebesgue measure. -/
theorem measurePreserving_splitOfPartition (e : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin N) :
    MeasurePreserving (splitOfPartition e)
      (volume : Measure (Fin N → ℝ)) volume := by
  unfold splitOfPartition
  -- Step 1: reindex along `e`, then take `.symm` (still MP).
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e).symm
      (volume : Measure (Fin N → ℝ)) volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) e).symm _
  -- Step 2: split the outer sum index `Fin a ⊕ (Fin b ⊕ Fin c)`.
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin a ⊕ (Fin b ⊕ Fin c) => ℝ))
      volume volume :=
    volume_measurePreserving_sumPiEquivProdPi _
  -- Step 3: split the inner sum index `Fin b ⊕ Fin c`, under `id` on the `Fin a` factor.
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin a → ℝ))
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin b ⊕ Fin c => ℝ)))
      (volume : Measure ((Fin a → ℝ) × (Fin b ⊕ Fin c → ℝ))) volume := by
    rw [show (volume : Measure ((Fin a → ℝ) × (Fin b ⊕ Fin c → ℝ)))
          = (volume : Measure (Fin a → ℝ)).prod volume from Measure.volume_eq_prod _ _,
      show (volume : Measure ((Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))))
          = (volume : Measure (Fin a → ℝ)).prod volume from Measure.volume_eq_prod _ _]
    exact (MeasurePreserving.id (volume : Measure (Fin a → ℝ))).prod
      (volume_measurePreserving_sumPiEquivProdPi _)
  exact h1.trans (h2.trans h3)

/-! ## Coordinate readback — how `splitOfPartition` reads the three blocks off `e`

The Reg / Core / Spec blocks are exactly the `inl` / `inr ∘ inl` / `inr ∘ inr` preimages of `e`:
each block coordinate equals the original coordinate at the corresponding `e`-image. These let the
per-family consumer relate its shift (a function of the original coords) to the split blocks — the
bridge the concrete `split121_shear121` / `split231_shear231` proved by hand. All three are `rfl`
(each split step is a definitional projection; the constant codomain kills the `piCongrLeft`
cast). -/

/-- The **Reg** block reads `u` at the `inl` image of `e`: `(split u).1 i = u (e (.inl i))`. -/
@[simp]
theorem splitOfPartition_reg (e : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin N) (u : Fin N → ℝ) (i : Fin a) :
    (splitOfPartition e u).1 i = u (e (Sum.inl i)) := rfl

/-- The **Core** block reads `u` at the `inr ∘ inl` image of `e`:
`(split u).2.1 j = u (e (.inr (.inl j)))`. -/
@[simp]
theorem splitOfPartition_core (e : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin N) (u : Fin N → ℝ) (j : Fin b) :
    (splitOfPartition e u).2.1 j = u (e (Sum.inr (Sum.inl j))) := rfl

/-- The **Spec** block reads `u` at the `inr ∘ inr` image of `e`:
`(split u).2.2 k = u (e (.inr (.inr k)))`. -/
@[simp]
theorem splitOfPartition_spec (e : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin N) (u : Fin N → ℝ) (k : Fin c) :
    (splitOfPartition e u).2.2 k = u (e (Sum.inr (Sum.inr k))) := rfl

/-- The **inverse** writes each block back to its `e`-image coordinate:
`(split.symm q) (e idx) = (the block entry at idx)`, packaged as a single `Sum.elim`. The original
coordinate `u m` is recovered by `m = e idx` for the unique `idx`. -/
theorem splitOfPartition_symm_apply (e : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin N)
    (q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))) (idx : Fin a ⊕ (Fin b ⊕ Fin c)) :
    (splitOfPartition e).symm q (e idx)
      = Sum.elim q.1 (Sum.elim q.2.1 q.2.2) idx := by
  -- `(split e).symm = piCongrLeft (·=ℝ) e ∘ (sumPiEquivProdPi).symm ∘ (prodCongr id sum).symm`;
  -- the `piCongrLeft` then reads coord `e idx` back to the `idx` block entry.
  -- Read the block entry off the forward readback at `u := (split e).symm q`
  -- (`split` roundtrips `q`).
  have hround : splitOfPartition e ((splitOfPartition e).symm q) = q :=
    (splitOfPartition e).apply_symm_apply q
  rcases idx with i | (j | k)
  · have := splitOfPartition_reg e ((splitOfPartition e).symm q) i
    rw [hround] at this; exact this.symm
  · have := splitOfPartition_core e ((splitOfPartition e).symm q) j
    rw [hround] at this; exact this.symm
  · have := splitOfPartition_spec e ((splitOfPartition e).symm q) k
    rw [hround] at this; exact this.symm

/-! ## The thin `coreSet`-driven instance (parameterization iii — the consumer's wiring)

The per-family consumer (`shearM_conj`, #159) supplies only a `coreSet : Finset (Fin N)` — the flat
indices of the kept top-`r` rows of `A^{L−1}` (the slots `coreShear` adds the shift to). The
reg / spec sub-split of the complement is FREE; we take **reg = ∅** so the shift reads the FULL
complement `coreSetᶜ` (= front + S_bot), matching the worked instances (`split231` Core = {6,7},
complement = {0..5,8}; `split121` Core = {2}, complement = {0,1,3}). The index-equiv isolating the
core is `∅ ⊕ (coreSet ⊕ coreSetᶜ) ≃ Fin N` (`sumCompl`, the subtypes re-indexed to `Fin` by
card). -/

variable [DecidableEq (Fin N)]

/-- The index decomposition `Fin 0 ⊕ (Fin #coreSet ⊕ Fin #coreSetᶜ) ≃ Fin N` that isolates `coreSet`
in the Core block (`inr ∘ inl`) and puts the whole complement in the Spec block (`inr ∘ inr`),
with an empty Reg block. -/
noncomputable def coreSetEquiv (coreSet : Finset (Fin N)) :
    (Fin 0 ⊕ (Fin coreSet.card ⊕ Fin coreSetᶜ.card)) ≃ Fin N :=
  (Equiv.emptySum (Fin 0) _).trans
    ((Equiv.sumCongr coreSet.equivFin.symm
      (coreSetᶜ.equivFin.symm.trans
        (Equiv.subtypeEquivRight (fun x => by simp [Finset.mem_compl])))).trans
      (Equiv.sumCompl (· ∈ coreSet)))

/-- **The `coreSet`-driven block split** `(Fin N → ℝ) ≃ᵐ (Fin 0 → ℝ) × ((Fin #coreSet → ℝ) × (Fin
#coreSetᶜ → ℝ))` — the thin instance the per-family `shearM_conj` consumes. Core = `coreSet`,
Spec = `coreSetᶜ`, Reg = ∅. -/
noncomputable def splitOfCoreSet (coreSet : Finset (Fin N)) :
    (Fin N → ℝ) ≃ᵐ (Fin 0 → ℝ) × ((Fin coreSet.card → ℝ) × (Fin coreSetᶜ.card → ℝ)) :=
  splitOfPartition (coreSetEquiv coreSet)

/-- **`splitOfCoreSet` is measure-preserving** (the general primitive at `coreSetEquiv`). -/
theorem measurePreserving_splitOfCoreSet (coreSet : Finset (Fin N)) :
    MeasurePreserving (splitOfCoreSet coreSet) (volume : Measure (Fin N → ℝ)) volume :=
  measurePreserving_splitOfPartition (coreSetEquiv coreSet)

/-- **Core isolation.** The Core block of `splitOfCoreSet` reads `u` at the `coreSet` coordinate
`coreSet.equivFin.symm j` — i.e. exactly the kept-row flat indices, in `Finset` order. This is the
property `coreShear` needs: the shift is added to exactly the `coreSet` slots. -/
theorem splitOfCoreSet_core (coreSet : Finset (Fin N)) (u : Fin N → ℝ) (j : Fin coreSet.card) :
    (splitOfCoreSet coreSet u).2.1 j = u (coreSet.equivFin.symm j) := by
  rw [splitOfCoreSet, splitOfPartition_core]; rfl

/-- **Spec = complement.** The Spec block reads `u` at the `coreSetᶜ` coordinate. -/
theorem splitOfCoreSet_spec (coreSet : Finset (Fin N)) (u : Fin N → ℝ) (k : Fin coreSetᶜ.card) :
    (splitOfCoreSet coreSet u).2.2 k = u (coreSetᶜ.equivFin.symm k) := by
  rw [splitOfCoreSet, splitOfPartition_spec]; rfl

end DLNFibre.DLN.RLCT
