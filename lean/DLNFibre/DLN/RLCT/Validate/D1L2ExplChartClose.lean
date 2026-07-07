import DLNFibre.DLN.RLCT.Validate.D1L2PhiExpl
import DLNFibre.DLN.RLCT.Validate.D1L2PhiExplClose
import DLNFibre.DLN.RLCT.Validate.D1L2SchurAssembly
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing
import DLNFibre.DLN.RLCT.Foundations.CoreSplitMP

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2ExplChartClose` — the L = 2 crux close (Option A)

The coordinate/measure PLUMBING sub-tide that closes the sole L = 2 headline crux
`d1ge_L2_hAtV_explicit` (`D1L2ExplicitCoreProducer`) by feeding the banked consumer
`d1ge_L2_hAtV_of_explicit_chart` (`D1L2SchurAssembly`) with the banked germ `schur_loss_germ_L2_rlct`
(`D1L2PhiExpl`). All analytic content is banked; this module is the reindex + `qₑ` construction.

## The flat-coordinate partition (Codex-validated)

The germ readout `F = schurReadoutF_L2 … x = ∑_{a,bb} ((recoverProduct (b x + C₀) - Br₀) a bb)²`
(`b := blockFlatEquiv_L2`) depends on the block coordinates of `Q := b x + C₀` via `recoverProduct`,
which reads only `Q.2.toBlocks₁₁ (M11)`, `Q.2.toBlocks₁₂ (M12)`, `Q.1.toBlocks₂₁ (M21)`,
`Q.1.toBlocks₂₂ (A0red)`, `Q.2.toBlocks₂₂ (A1red)`. So the `flatDim H` coordinates split into:

* **REGULAR** (`nRegL2 H r` coords): `L0.₂₁ (M21)`, `L1.₁₁ (M11)`, `L1.₁₂ (M12)` — the `∑ p²` block.
* **CORE** (`flatDim (H − r)` coords): `L0.₂₂ (A0red)`, `L1.₂₂ (A1red)` — exactly the two reduced
  `(H − r)` layers.
* **SPEC** (`specDim` coords): `L0.₁₁ (X)`, `L0.₁₂ (Y)`, `L1.₂₁ (Uu)` — untouched by `F`.

`e_idx` (below) realises this partition as an index-equiv aligned to `blockFlatEquiv_L2`, feeding the
banked `CoreSplitMP.splitOfPartition` (measure-preserving on flat `Pi` spaces — matrix-level MP is
unavailable). The core slot is aligned to `paramsEquivFlat (H − r)` order so the consumer's `e` is a
pure translation.

Single-writer: NOT yet in the aggregator. Controller wires `D1L2ExplChartClose` (its closure pulls
`D1L2PhiExpl`, `CommonPivotL2`, `S1InverseDerivEquiv`, `CoreSplitMP`), then `D1L2ExplicitCoreProducer`
imports it to fill the crux.
-/

open Matrix MeasureTheory
open scoped ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable (H : Fin (2 + 1) → ℕ) (r : ℕ)

/-! ## The role-index types (Codex-validated semantic partition) -/

/-- The **regular** index type (the `∑ p²` block): `L0.₂₁` (M21, row nonpivot × col pivot) plus
`L1.₁₁,₁₂` (M11, M12: row pivot × col arbitrary). Its cardinality is `nRegL2 H r`. -/
abbrev RegIdx : Type :=
  (Fin (H 0 - r) × Fin r) ⊕ (Fin r × (Fin r ⊕ Fin (H (Fin.last 2) - r)))

/-- The **core** index type: exactly `FlatIdx (H − r)` (the two reduced layers `A0red, A1red`),
so it is `paramsEquivFlat (H − r)`-ordered. -/
abbrev CoreIdx : Type := FlatIdx (fun s => H s - r)

/-- The **spectator** index type (untouched by `F`): `L0.₁₁,₁₂` (X, Y) plus `L1.₂₁` (Uu). -/
abbrev SpecIdx : Type :=
  (Fin r × (Fin r ⊕ Fin (H 1 - r))) ⊕ (Fin (H 1 - r) × Fin r)

/-- `Fintype.card (RegIdx H r) = nRegL2 H r` (needs `r ≤ H 0`, `r ≤ H (last 2)`). -/
theorem card_RegIdx (hr0 : r ≤ H 0) (hr2 : r ≤ H (Fin.last 2)) :
    Fintype.card (RegIdx H r) = nRegL2 H r := by
  simp only [RegIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  -- (H0-r)*r + r*(r + (Hlast-r)) = r*(H0 + Hlast - r)
  rw [nRegL2]
  have h1 : r + (H (Fin.last 2) - r) = H (Fin.last 2) := Nat.add_sub_cancel' hr2
  have h2 : H 0 + H (Fin.last 2) - r = (H 0 - r) + H (Fin.last 2) := by omega
  rw [h1, h2]
  ring

/-! ## The role-partition index-equiv `roleEquiv : RegIdx ⊕ (CoreIdx ⊕ SpecIdx) ≃ FlatIdx H`

The pivots `I, K, J` (from the germ's `exists_common_pivot_L2_at`) place the `r` pivot rows/cols in
the `Sum.inl` block of each `sumSplit`. Layer dispatch (`s : Fin 2`) is done ONCE via `Fin.cases`; the
forward map is explicit so the `splitOfPartition` readbacks are definitional. -/

variable {H r}

/-- The per-layer row split `Fin r ⊕ Fin (H s.castSucc − r) ≃ Fin (H s.castSucc)`: `sumSplit I` at
layer 0, `sumSplit K` at layer 1. -/
noncomputable def rowSplit (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1))
    (hI : Function.Injective I) (hK : Function.Injective K) :
    (s : Fin 2) → (Fin r ⊕ Fin (H s.castSucc - r) ≃ Fin (H s.castSucc)) :=
  Fin.cases (sumSplit I hI) (fun x => Fin.cases (sumSplit K hK) (fun e => e.elim0) x)

/-- The per-layer column split `Fin r ⊕ Fin (H s.succ − r) ≃ Fin (H s.succ)`: `sumSplit K` at layer 0,
`sumSplit J` at layer 1. -/
noncomputable def colSplit (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H (Fin.last 2)))
    (hK : Function.Injective K) (hJ : Function.Injective J) :
    (s : Fin 2) → (Fin r ⊕ Fin (H s.succ - r) ≃ Fin (H s.succ)) :=
  Fin.cases (sumSplit K hK) (fun x => Fin.cases (sumSplit J hJ) (fun e => e.elim0) x)

@[simp] theorem rowSplit_zero (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1))
    (hI : Function.Injective I) (hK : Function.Injective K) :
    rowSplit I K hI hK 0 = sumSplit I hI := rfl
@[simp] theorem rowSplit_one (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1))
    (hI : Function.Injective I) (hK : Function.Injective K) :
    rowSplit I K hI hK 1 = sumSplit K hK := rfl
@[simp] theorem colSplit_zero (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H (Fin.last 2)))
    (hK : Function.Injective K) (hJ : Function.Injective J) :
    colSplit K J hK hJ 0 = sumSplit K hK := rfl
@[simp] theorem colSplit_one (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H (Fin.last 2)))
    (hK : Function.Injective K) (hJ : Function.Injective J) :
    colSplit K J hK hJ 1 = sumSplit J hJ := rfl

variable (I : Fin r → Fin (H 0)) (K : Fin r → Fin (H 1)) (J : Fin r → Fin (H (Fin.last 2)))
  (hI : Function.Injective I) (hK : Function.Injective K) (hJ : Function.Injective J)

/-- **The forward role → flat-index map.** Explicit constructor per role branch; the layer is
hardcoded for `Reg`/`Spec` and preserved (via the `CoreIdx = FlatIdx (H−r)` layer) for `Core`. -/
noncomputable def roleToFlat :
    (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) → FlatIdx H := fun x =>
  match x with
  -- REGULAR
  | Sum.inl (Sum.inl (a, k)) =>                    -- M21 : L0.₂₁
      ⟨⟨(0 : Fin 2), rowSplit I K hI hK 0 (Sum.inr a)⟩, colSplit K J hK hJ 0 (Sum.inl k)⟩
  | Sum.inl (Sum.inr (k, cc)) =>                   -- M11/M12 : L1.₁₁,₁₂
      ⟨⟨(1 : Fin 2), rowSplit I K hI hK 1 (Sum.inl k)⟩, colSplit K J hK hJ 1 cc⟩
  -- CORE (layer preserved from the reduced flat index)
  | Sum.inr (Sum.inl c) =>
      ⟨⟨c.1.1, rowSplit I K hI hK c.1.1 (Sum.inr c.1.2)⟩, colSplit K J hK hJ c.1.1 (Sum.inr c.2)⟩
  -- SPECTATOR
  | Sum.inr (Sum.inr (Sum.inl (k, cc))) =>         -- X/Y : L0.₁₁,₁₂
      ⟨⟨(0 : Fin 2), rowSplit I K hI hK 0 (Sum.inl k)⟩, colSplit K J hK hJ 0 cc⟩
  | Sum.inr (Sum.inr (Sum.inr (a, k))) =>          -- Uu : L1.₂₁
      ⟨⟨(1 : Fin 2), rowSplit I K hI hK 1 (Sum.inr a)⟩, colSplit K J hK hJ 1 (Sum.inl k)⟩

/-- Layer-0 classifier: read the row/col class off `sumSplit I / K`. -/
noncomputable def flatToRole0 (i : Fin (H 0)) (j : Fin (H 1)) :
    (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) :=
  match (sumSplit I hI).symm i, (sumSplit K hK).symm j with
  | Sum.inl k, Sum.inl k' => Sum.inr (Sum.inr (Sum.inl (k, Sum.inl k')))   -- X
  | Sum.inl k, Sum.inr b  => Sum.inr (Sum.inr (Sum.inl (k, Sum.inr b)))    -- Y
  | Sum.inr a, Sum.inl k  => Sum.inl (Sum.inl (a, k))                      -- M21
  | Sum.inr a, Sum.inr b  => Sum.inr (Sum.inl ⟨⟨(0 : Fin 2), a⟩, b⟩)       -- W (core L0)

/-- Layer-1 classifier: read the row/col class off `sumSplit K / J`. -/
noncomputable def flatToRole1 (i : Fin (H 1)) (j : Fin (H (Fin.last 2))) :
    (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) :=
  match (sumSplit K hK).symm i, (sumSplit J hJ).symm j with
  | Sum.inl k, Sum.inl k' => Sum.inl (Sum.inr (k, Sum.inl k'))             -- M11
  | Sum.inl k, Sum.inr b  => Sum.inl (Sum.inr (k, Sum.inr b))              -- M12
  | Sum.inr a, Sum.inl k  => Sum.inr (Sum.inr (Sum.inr (a, k)))            -- Uu
  | Sum.inr a, Sum.inr b  => Sum.inr (Sum.inl ⟨⟨(1 : Fin 2), a⟩, b⟩)       -- V (core L1)

/-- **The classifier flat-index → role** (the inverse). Layer dispatch via nested `Fin.cases`
(fully eliminating `s : Fin 2` to concrete `0`/`1`), then row/col class via `flatToRole0/1`. -/
noncomputable def flatToRole :
    FlatIdx H → (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) := fun f =>
  Fin.cases
    (motive := fun s => Fin (H s.castSucc) → Fin (H s.succ) →
        (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)))
    (flatToRole0 I K hI hK)
    (fun x => Fin.cases
      (motive := fun x : Fin 1 => Fin (H x.succ.castSucc) → Fin (H x.succ.succ) →
        (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)))
      (flatToRole1 K J hK hJ) (fun e => e.elim0) x)
    f.1.1 f.1.2 f.2

/-- Layer-0 reduction of `flatToRole` (the outer `Fin.cases` at `0`). -/
theorem flatToRole_zero (i : Fin (H 0)) (j : Fin (H 1)) :
    flatToRole I K J hI hK hJ ⟨⟨(0 : Fin 2), i⟩, j⟩ = flatToRole0 I K hI hK i j := rfl

/-- Layer-1 reduction of `flatToRole` (the outer `Fin.cases` at `1`). -/
theorem flatToRole_one (i : Fin (H 1)) (j : Fin (H (Fin.last 2))) :
    flatToRole I K J hI hK hJ ⟨⟨(1 : Fin 2), i⟩, j⟩ = flatToRole1 K J hK hJ i j := rfl

/-- **`flatToRole` is a left inverse of `roleToFlat`** — hence `roleToFlat` is injective. -/
theorem roleToFlat_leftInv :
    Function.LeftInverse (flatToRole I K J hI hK hJ) (roleToFlat I K J hI hK hJ) := by
    have h0 : ∀ (i : Fin (H 0)) (j : Fin (H 1)),
        flatToRole I K J hI hK hJ ⟨⟨(0 : Fin 2), i⟩, j⟩ = flatToRole0 I K hI hK i j := fun _ _ => rfl
    have h1 : ∀ (i : Fin (H 1)) (j : Fin (H (Fin.last 2))),
        flatToRole I K J hI hK hJ ⟨⟨(1 : Fin 2), i⟩, j⟩ = flatToRole1 K J hK hJ i j := fun _ _ => rfl
    rintro ((⟨a, k⟩ | ⟨k, (k' | b)⟩) | (c | (⟨k, (k' | b)⟩ | ⟨a, k⟩)))
    · -- M21 (L0.₂₁)
      change flatToRole I K J hI hK hJ ⟨⟨(0 : Fin 2), sumSplit I hI (Sum.inr a)⟩,
        sumSplit K hK (Sum.inl k)⟩ = _
      rw [h0]; simp only [flatToRole0, Equiv.symm_apply_apply]
    · -- M11 (L1.₁₁)
      change flatToRole I K J hI hK hJ ⟨⟨(1 : Fin 2), sumSplit K hK (Sum.inl k)⟩,
        sumSplit J hJ (Sum.inl k')⟩ = _
      rw [h1]; simp only [flatToRole1, Equiv.symm_apply_apply]
    · -- M12 (L1.₁₂)
      change flatToRole I K J hI hK hJ ⟨⟨(1 : Fin 2), sumSplit K hK (Sum.inl k)⟩,
        sumSplit J hJ (Sum.inr b)⟩ = _
      rw [h1]; simp only [flatToRole1, Equiv.symm_apply_apply]
    · -- Core: layer s is a variable; case on it.
      obtain ⟨⟨s, i'⟩, j'⟩ := c
      refine Fin.cases (motive := fun s => ∀ (i' : Fin (H s.castSucc - r)) (j' : Fin (H s.succ - r)),
          flatToRole I K J hI hK hJ (roleToFlat I K J hI hK hJ (Sum.inr (Sum.inl ⟨⟨s, i'⟩, j'⟩)))
            = Sum.inr (Sum.inl ⟨⟨s, i'⟩, j'⟩))
          ?_ (fun x => Fin.cases ?_ (fun e => e.elim0) x) s i' j'
      · intro i' j'
        change flatToRole I K J hI hK hJ ⟨⟨(0 : Fin 2), sumSplit I hI (Sum.inr i')⟩,
          sumSplit K hK (Sum.inr j')⟩ = _
        rw [h0]; simp only [flatToRole0, Equiv.symm_apply_apply]
      · intro i' j'
        simp only [Fin.succ_zero_eq_one]
        change flatToRole I K J hI hK hJ ⟨⟨(1 : Fin 2), sumSplit K hK (Sum.inr i')⟩,
          sumSplit J hJ (Sum.inr j')⟩ = _
        rw [h1]; simp only [flatToRole1, Equiv.symm_apply_apply]
    · -- X (L0.₁₁)
      change flatToRole I K J hI hK hJ ⟨⟨(0 : Fin 2), sumSplit I hI (Sum.inl k)⟩,
        sumSplit K hK (Sum.inl k')⟩ = _
      rw [h0]; simp only [flatToRole0, Equiv.symm_apply_apply]
    · -- Y (L0.₁₂)
      change flatToRole I K J hI hK hJ ⟨⟨(0 : Fin 2), sumSplit I hI (Sum.inl k)⟩,
        sumSplit K hK (Sum.inr b)⟩ = _
      rw [h0]; simp only [flatToRole0, Equiv.symm_apply_apply]
    · -- Uu (L1.₂₁)
      change flatToRole I K J hI hK hJ ⟨⟨(1 : Fin 2), sumSplit K hK (Sum.inr a)⟩,
        sumSplit J hJ (Sum.inl k)⟩ = _
      rw [h1]; simp only [flatToRole1, Equiv.symm_apply_apply]

include hI hK hJ in
/-- The role-partition and `FlatIdx H` have the same cardinality (both `= flatDim H`). -/
theorem card_role_eq :
    Fintype.card (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) = Fintype.card (FlatIdx H) := by
  have hr0 : r ≤ H 0 := by
    have := Fintype.card_le_of_injective I hI; simpa only [Fintype.card_fin] using this
  have hr1 : r ≤ H 1 := by
    have := Fintype.card_le_of_injective K hK; simpa only [Fintype.card_fin] using this
  have hr2 : r ≤ H (Fin.last 2) := by
    have := Fintype.card_le_of_injective J hJ; simpa only [Fintype.card_fin] using this
  have hReg : Fintype.card (RegIdx H r) = nRegL2 H r := card_RegIdx H r hr0 hr2
  -- CoreIdx = FlatIdx (H − r); card FlatIdx = flatDim by def.
  have hcore : Fintype.card (CoreIdx H r) = flatDim (fun s => H s - r) := rfl
  have hflat : Fintype.card (FlatIdx H) = flatDim H := rfl
  rw [Fintype.card_sum, hReg, Fintype.card_sum, hcore, hflat, flatDim_eq (fun s => H s - r),
    flatDim_eq H]
  simp only [SpecIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fin.sum_univ_two,
    Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two, nRegL2]
  -- pin the goal (H (Fin.last 2) = H 2 by defeq), substitute the `≤`s, and `ring`.
  change r * (H 0 + H (Fin.last 2) - r)
      + ((H 0 - r) * (H 1 - r) + (H 1 - r) * (H (Fin.last 2) - r)
        + (r * (r + (H 1 - r)) + (H 1 - r) * r))
    = H 0 * H 1 + H 1 * H (Fin.last 2)
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hr0
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hr1
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hr2
  rw [ha, hb, hc, show r + a + (r + c) - r = r + a + c from by omega]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- **The role-partition index-equiv** `RegIdx ⊕ (CoreIdx ⊕ SpecIdx) ≃ FlatIdx H`. From the left
inverse (injectivity) + the cardinality equality. -/
noncomputable def roleEquiv :
    (RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) ≃ FlatIdx H :=
  Equiv.ofBijective (roleToFlat I K J hI hK hJ)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(roleToFlat_leftInv I K J hI hK hJ).injective, card_role_eq I K J hI hK hJ⟩)

@[simp] theorem roleEquiv_apply (x : RegIdx H r ⊕ (CoreIdx H r ⊕ SpecIdx H r)) :
    roleEquiv I K J hI hK hJ x = roleToFlat I K J hI hK hJ x := rfl

/-! ## `e_idx` — the flat index-equiv, aligned to `blockFlatEquiv_L2`, feeding `splitOfPartition` -/

/-- The spectator dimension (`= 2 r H1 − r²`; kept as a `Fintype.card` for the equiv). -/
def specDim (H : Fin (2 + 1) → ℕ) (r : ℕ) : ℕ := Fintype.card (SpecIdx H r)

/-- `Fin (nRegL2 H r) ≃ RegIdx H r` (from the cardinality lemma). -/
noncomputable def regEquivFin : Fin (nRegL2 H r) ≃ RegIdx H r :=
  (Fintype.equivFinOfCardEq (card_RegIdx H r
    (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective I hI)
    (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective J hJ))).symm

/-- **The flat index-equiv** `Fin nReg ⊕ (Fin (flatDim (H−r)) ⊕ Fin specDim) ≃ Fin (flatDim H)`,
aligned to `blockFlatEquiv_L2` via `roleEquiv`. Reg ↦ `RegIdx`, Core ↦ `CoreIdx = FlatIdx (H−r)`
(so `paramsEquivFlat (H−r)`-ordered), Spec ↦ `SpecIdx`; then `roleEquiv` places them at the right
flat coordinates, and `Fintype.equivFin` reindexes to `Fin (flatDim H)`. -/
noncomputable def e_idx :
    Fin (nRegL2 H r) ⊕ (Fin (flatDim (fun s => H s - r)) ⊕ Fin (specDim H r)) ≃ Fin (flatDim H) :=
  (Equiv.sumCongr (regEquivFin I J hI hJ)
      (Equiv.sumCongr (Fintype.equivFin (CoreIdx H r)).symm (Fintype.equivFin (SpecIdx H r)).symm)).trans
    ((roleEquiv I K J hI hK hJ).trans (Fintype.equivFin (FlatIdx H)))

/-- **The measure-preserving flat block split** driven by `e_idx`. -/
noncomputable def splitMP :
    (Fin (flatDim H) → ℝ) ≃ᵐ
      (Fin (nRegL2 H r) → ℝ) × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDim H r) → ℝ)) :=
  splitOfPartition (e_idx I K J hI hK hJ)

theorem measurePreserving_splitMP :
    MeasurePreserving (splitMP I K J hI hK hJ) (volume : Measure (Fin (flatDim H) → ℝ)) volume :=
  measurePreserving_splitOfPartition (e_idx I K J hI hK hJ)

/-- Raw reg-block readback: `(splitMP x).1 i = x (e_idx (inl i))`. -/
theorem splitMP_reg (x : Fin (flatDim H) → ℝ) (i : Fin (nRegL2 H r)) :
    (splitMP I K J hI hK hJ x).1 i = x (e_idx I K J hI hK hJ (Sum.inl i)) := rfl

/-- Raw core-block readback: `(splitMP x).2.1 j = x (e_idx (inr (inl j)))`. -/
theorem splitMP_core (x : Fin (flatDim H) → ℝ) (j : Fin (flatDim (fun s => H s - r))) :
    (splitMP I K J hI hK hJ x).2.1 j = x (e_idx I K J hI hK hJ (Sum.inr (Sum.inl j))) := rfl

/-- Raw spec-block readback: `(splitMP x).2.2 k = x (e_idx (inr (inr k)))`. -/
theorem splitMP_spec (x : Fin (flatDim H) → ℝ) (k : Fin (specDim H r)) :
    (splitMP I K J hI hK hJ x).2.2 k = x (e_idx I K J hI hK hJ (Sum.inr (Sum.inr k))) := rfl

/-- `e_idx` on the core slot: `= equivFin ∘ roleToFlat ∘ inr∘inl ∘ coreE.symm` (definitional). -/
theorem e_idx_core (n : Fin (flatDim (fun s => H s - r))) :
    e_idx I K J hI hK hJ (Sum.inr (Sum.inl n))
      = Fintype.equivFin (FlatIdx H)
          (roleToFlat I K J hI hK hJ (Sum.inr (Sum.inl ((Fintype.equivFin (CoreIdx H r)).symm n)))) :=
  rfl

/-! ## The core-block readback (linchpin for `hfact`)

The `splitMP` core block, decoded by `paramsEquivFlat (H − r)`, is exactly the two `blockFlatEquiv_L2`
`₂₂` corners `(A0red, A1red)` of the flat point `x` — the reduced `(H − r)` layers. -/

/-- The reduced-core parameter read off the two `₂₂` corners of `blockFlatEquiv_L2 x`. -/
noncomputable def coreParams (x : Fin (flatDim H) → ℝ) : Params (fun s => H s - r) :=
  Fin.cases (blockFlatEquiv_L2 H r I K J hI hK hJ x).1.toBlocks₂₂
    (fun y => Fin.cases (blockFlatEquiv_L2 H r I K J hI hK hJ x).2.toBlocks₂₂ (fun e => e.elim0) y)

@[simp] theorem coreParams_zero (x : Fin (flatDim H) → ℝ) :
    coreParams I K J hI hK hJ x 0 = (blockFlatEquiv_L2 H r I K J hI hK hJ x).1.toBlocks₂₂ := rfl

@[simp] theorem coreParams_one (x : Fin (flatDim H) → ℝ) :
    coreParams I K J hI hK hJ x 1 = (blockFlatEquiv_L2 H r I K J hI hK hJ x).2.toBlocks₂₂ := rfl

/-- **Core-block readback.** `(paramsEquivFlat (H − r)).symm ((splitMP x).2.1) = coreParams x`. -/
theorem paramsEquivFlat_symm_splitMP_core (x : Fin (flatDim H) → ℝ) :
    (paramsEquivFlat (fun s => H s - r)).symm ((splitMP I K J hI hK hJ x).2.1)
      = coreParams I K J hI hK hJ x := by
  funext s
  refine Fin.cases (motive := fun s =>
      (paramsEquivFlat (fun s => H s - r)).symm ((splitMP I K J hI hK hJ x).2.1) s
        = coreParams I K J hI hK hJ x s)
      ?_ (fun y => Fin.cases ?_ (fun e => e.elim0) y) s
  · -- layer 0
    funext i j
    rw [coreParams_zero, paramsEquivFlat_symm_entry, splitMP_core, e_idx_core,
      Equiv.symm_apply_apply]
    simp only [roleToFlat, rowSplit_zero, colSplit_zero]
    rw [blockFlatEquiv_L2_fst]
    simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.symm_symm, paramsEquivFlatLinear_symm_coe]
    exact (paramsEquivFlat_symm_entry H x 0 (sumSplit I hI (Sum.inr i))
      (sumSplit K hK (Sum.inr j))).symm
  · -- layer 1
    simp only [Fin.succ_zero_eq_one]
    funext i j
    rw [coreParams_one, paramsEquivFlat_symm_entry, splitMP_core, e_idx_core,
      Equiv.symm_apply_apply]
    simp only [roleToFlat, rowSplit_one, colSplit_one]
    rw [blockFlatEquiv_L2_snd]
    simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Equiv.symm_symm, paramsEquivFlatLinear_symm_coe]
    exact (paramsEquivFlat_symm_entry H x 1 (sumSplit K hK (Sum.inr i))
      (sumSplit J hJ (Sum.inr j))).symm

end DLNFibre.DLN.RLCT
