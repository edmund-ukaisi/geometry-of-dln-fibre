import DLNFibre.DLN.RLCT.Validate.D1GeChart
import DLNFibre.DLN.RLCT.Validate.D1GeBlockModel
import DLNFibre.DLN.RLCT.Validate.D1GeGlobalize
import DLNFibre.DLN.RLCT.Validate.D1GeLegGenL
import DLNFibre.DLN.RLCT.Foundations.CoreSplitMP

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeSchurResidual` — the D1 ≥-leg residual strand (piece iv), gen `L`

The general-`L` port of the L = 2 residual strand (`D1L2ExplChartClose`/`Close2`), feeding the
banked consumer `d1ge_hAtV_of_explicit_chart_genL`. Structured around the banked general-`L` chart
+ telescope (`schurChartRawGen`, `blockSchur_partProd_asym_fold`, `recoverProductGen`,
`blockFlatEquivGen`).

**The reg/core/spec role partition** (Codex-settled, `threads/genm-geleg-iv/codex/rolepart-*.md`),
per layer `s ∈ {0,…,L−1}`, of the block coordinates:

| layer `s`        | `₁₁`  | `₁₂`  | `₂₁`  | `₂₂`  |
|------------------|-------|-------|-------|-------|
| `s = 0`          | SPEC  | SPEC  | REG   | CORE  |
| `0 < s < L−1`    | SPEC  | SPEC  | SPEC  | CORE  |
| `s = L−1`        | REG   | REG   | SPEC  | CORE  |

- **REG** (`∑ p²` regular block, `card = r(H₀+Hᴸ−r) = nRegGen`): first layer's `₂₁` + last layer's
  `₁₁,₁₂` — mapped by the chart to the full-product corners `(P_L)₂₁, (P_L)₁₁, (P_L)₁₂`.
- **CORE** (`= FlatIdx (H−r)`, the reduced Params): every layer's `₂₂`.
- **SPEC** (untouched by `F`): everything else (first `₁₁,₁₂`; last `₂₁`; all interior `₁₁,₁₂,₂₁`).

The slice value (`p = 0`) is the reduced-core product `∏_s R_s = blockSchur (partProd C L)` (via
`blockSchur_partProd_asym_fold`), i.e. `dlnLoss (H−r)` on the core. **Excluded** (geleg8's germ):
the seam `schurReadout_germ_eq_gen` / the readout `schurReadoutF_gen`.

This file (foundation): the role-index types + the regular cardinality. Downstream (build order):
`roleEquivGen` (the first/interior/last classifier), `splitMPGen`/`splitHomeoGen`, `qResidGen`, the
slice value, and `e`/`hfact`/`hRne`.
-/

open Matrix MeasureTheory
open scoped Classical ENNReal Topology BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The role-index types (general-`L`) -/

/-- **The regular index type** (`∑ p²` block): first layer's `₂₁` (row nonpivot × col pivot) plus
last layer's `₁₁,₁₂` (row pivot × col arbitrary). Cardinality `r(H₀+Hᴸ−r)`. Shape-identical to L = 2
`RegIdx` (general last vertex). -/
abbrev RegIdxGen (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin (H 0 - r) × Fin r) ⊕ (Fin r × (Fin r ⊕ Fin (H (Fin.last L) - r)))

/-- **The core index type**: exactly `FlatIdx (H − r)` (every layer's `₂₂` — the reduced Params),
so it is `paramsEquivFlat (H − r)`-ordered. -/
abbrev CoreIdxGen (H : Fin (L + 1) → ℕ) (r : ℕ) : Type := FlatIdx (fun s => H s - r)

/-- The regular direction count `r(H₀+Hᴸ−r)` (the general-`L` `nRegL2`). -/
abbrev nRegGen (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ := r * (H 0 + H (Fin.last L) - r)

/-- `Fintype.card (RegIdxGen H r) = nRegGen H r` (needs `r ≤ H 0`, `r ≤ H (last L)`). Mirrors the
L = 2 `card_RegIdx`. -/
theorem card_RegIdxGen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr0 : r ≤ H 0)
    (hrL : r ≤ H (Fin.last L)) : Fintype.card (RegIdxGen H r) = nRegGen H r := by
  simp only [RegIdxGen, nRegGen, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h1 : r + (H (Fin.last L) - r) = H (Fin.last L) := Nat.add_sub_cancel' hrL
  have h2 : H 0 + H (Fin.last L) - r = (H 0 - r) + H (Fin.last L) := by omega
  rw [h1, h2]; ring

/-! ## Rung A — the role-partition index equiv `roleEquivGen` (complement-subtype construction)

The forward map `regCoreEmbGen : RegIdxGen ⊕ CoreIdxGen ↪ FlatIdx H` places REG at the boundary
layers (`firstLayer`/`lastLayer`) and CORE layer-preserved at every layer's `₂₂`; `SpecIdxGen` is
then `(range regCoreEmbGen)ᶜ` (no interior enumeration). `roleEquivGen` glues these via
`Equiv.ofInjective` + `Equiv.Set.sumCompl` + `Equiv.sumAssoc`. Injectivity is by a partial `Option`
classifier (dodging `HEq`). -/

variable {H : Fin (L + 1) → ℕ} {r : ℕ}
  (ι : (v : Fin (L + 1)) → Fin r → Fin (H v)) (hι : ∀ v, Function.Injective (ι v)) (hL : 1 ≤ L)

/-- **The reg/core forward map** `RegIdxGen ⊕ CoreIdxGen → FlatIdx H` at the pivot family `ι`. CORE
is layer-preserved onto the `₂₂` (nonpivot, nonpivot) cell; REG-first is layer `firstLayer`'s `₂₁`
(nonpivot row, pivot col); REG-last is layer `lastLayer`'s `₁₁,₁₂` (pivot row, any col, the last
column cast by `H_lastLayer_succ`). Its `sumSplit`-images make the classifier a left inverse. -/
noncomputable def regCoreEmbGen :
    (RegIdxGen H r ⊕ CoreIdxGen H r) → FlatIdx H
  | Sum.inl (Sum.inl (a, k)) =>
      ⟨⟨firstLayer hL, sumSplit (ι (firstLayer hL).castSucc) (hι _) (Sum.inr a)⟩,
        sumSplit (ι (firstLayer hL).succ) (hι _) (Sum.inl k)⟩
  | Sum.inl (Sum.inr (k, cc)) =>
      ⟨⟨lastLayer hL, sumSplit (ι (lastLayer hL).castSucc) (hι _) (Sum.inl k)⟩,
        sumSplit (ι (lastLayer hL).succ) (hι _)
          (Sum.map id (finCongr (by rw [H_lastLayer_succ H hL])) cc)⟩
  | Sum.inr ⟨⟨s, i⟩, j⟩ =>
      ⟨⟨s, sumSplit (ι s.castSucc) (hι _) (Sum.inr i)⟩,
        sumSplit (ι s.succ) (hι _) (Sum.inr j)⟩

/-- **The partial classifier** `FlatIdx H → Option (RegIdxGen ⊕ CoreIdxGen)`: reads the row/column
pivot class off `(sumSplit (ι ·)).symm`; `(nonpiv,nonpiv)` is CORE (any layer), `(nonpiv,piv)` is
REG-first (width-gated to `H 0`), `(piv,·)` is REG-last (width-gated to `H (last L)`), else `none`.
A left inverse of `regCoreEmbGen`. -/
noncomputable def flatToRegCoreGen? :
    FlatIdx H → Option (RegIdxGen H r ⊕ CoreIdxGen H r) := fun f =>
  match (sumSplit (ι f.1.1.castSucc) (hι _)).symm f.1.2,
        (sumSplit (ι f.1.1.succ) (hι _)).symm f.2 with
  | Sum.inr a, Sum.inr b => some (Sum.inr ⟨⟨f.1.1, a⟩, b⟩)
  | Sum.inr a, Sum.inl k =>
      if h : H f.1.1.castSucc - r = H 0 - r then
        some (Sum.inl (Sum.inl (finCongr h a, k)))
      else none
  | Sum.inl k, cc =>
      if h : H f.1.1.succ - r = H (Fin.last L) - r then
        some (Sum.inl (Sum.inr (k, Sum.map id (finCongr h) cc)))
      else none

/-- `flatToRegCoreGen?` is a left inverse of `regCoreEmbGen`, so `regCoreEmbGen` is injective. -/
theorem flatToRegCoreGen?_regCoreEmbGen (x : RegIdxGen H r ⊕ CoreIdxGen H r) :
    flatToRegCoreGen? ι hι (regCoreEmbGen ι hι hL x) = some x := by
  rcases x with (⟨a, k⟩ | ⟨k, cc⟩) | ⟨⟨s, i⟩, j⟩
  · -- REG-first
    have hz : H (firstLayer hL).castSucc - r = H 0 - r := by
      have hc : (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
        apply Fin.ext; simp [firstLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]
      rw [hc]
    unfold regCoreEmbGen flatToRegCoreGen?
    simp only [Equiv.symm_apply_apply, dif_pos hz]
    refine congrArg (fun z => some (Sum.inl (Sum.inl (z, k)))) ?_
    exact Fin.ext (by simp [finCongr_apply])
  · -- REG-last
    have hy : H (lastLayer hL).succ - r = H (Fin.last L) - r := by rw [H_lastLayer_succ H hL]
    unfold regCoreEmbGen flatToRegCoreGen?
    simp only [Equiv.symm_apply_apply, dif_pos hy]
    refine congrArg (fun z => some (Sum.inl (Sum.inr (k, z)))) ?_
    cases cc with
    | inl k' => rfl
    | inr b => exact congrArg Sum.inr (Fin.ext (by simp [finCongr_apply]))
  · -- CORE
    unfold regCoreEmbGen flatToRegCoreGen?
    simp only [Equiv.symm_apply_apply]

theorem regCoreEmbGen_injective : Function.Injective (regCoreEmbGen ι hι hL) := by
  intro x y h
  have hx := flatToRegCoreGen?_regCoreEmbGen ι hι hL x
  have hy := flatToRegCoreGen?_regCoreEmbGen ι hι hL y
  rw [h, hy] at hx
  exact (Option.some.injEq _ _ ▸ hx).symm

/-- **The spectator index type**: the complement of the reg/core image (no interior enumeration). -/
abbrev SpecIdxGen : Type := ↥(Set.range (regCoreEmbGen ι hι hL))ᶜ

/-- **The explicit forward role → flat map.** REG/CORE via `regCoreEmbGen`, SPEC is the subtype
value (a `FlatIdx H` outside the reg/core range). Kept explicit (not a `sumCompl` composition) so
`roleEquivGen.symm` is a single `invFun` — the L = 2 `ofBijective` shape, whose whnf stays cheap
(a `sumCompl.symm` would force a non-computing `Classical` range-membership decision). -/
noncomputable def roleToFlatGen :
    (RegIdxGen H r ⊕ (CoreIdxGen H r ⊕ SpecIdxGen ι hι hL)) → FlatIdx H
  | Sum.inl ρ => regCoreEmbGen ι hι hL (Sum.inl ρ)
  | Sum.inr (Sum.inl c) => regCoreEmbGen ι hι hL (Sum.inr c)
  | Sum.inr (Sum.inr x) => x.1

/-- `roleToFlatGen` is injective: REG/CORE inject via `regCoreEmbGen`; a SPEC value lies OUTSIDE
the reg/core range (`x.2`), so it collides with neither arm nor another SPEC (subtype). -/
theorem roleToFlatGen_injective : Function.Injective (roleToFlatGen ι hι hL) := by
  have hinj := regCoreEmbGen_injective ι hι hL
  rintro (ρ₁ | (c₁ | x₁)) (ρ₂ | (c₂ | x₂)) h <;>
    simp only [roleToFlatGen] at h
  · exact congrArg Sum.inl (Sum.inl_injective (hinj h))
  · exact absurd (hinj h) (by simp)
  · exact absurd ⟨_, h⟩ x₂.2
  · exact absurd (hinj h) (by simp)
  · exact congrArg (fun c => Sum.inr (Sum.inl c)) (Sum.inr_injective (hinj h))
  · exact absurd ⟨_, h⟩ x₂.2
  · exact absurd ⟨_, h.symm⟩ x₁.2
  · exact absurd ⟨_, h.symm⟩ x₁.2
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext h)

/-- The role partition and `FlatIdx H` have equal cardinality — via `card_congr` of the reg/core
range ⊕ complement equiv (used for the `Nat` card only, so its `symm` is never whnf'd here). -/
theorem card_roleGen :
    Fintype.card (RegIdxGen H r ⊕ (CoreIdxGen H r ⊕ SpecIdxGen ι hι hL))
      = Fintype.card (FlatIdx H) :=
  Fintype.card_congr
    ((Equiv.sumAssoc (RegIdxGen H r) (CoreIdxGen H r) (SpecIdxGen ι hι hL)).symm.trans
      ((Equiv.sumCongr (Equiv.ofInjective _ (regCoreEmbGen_injective ι hι hL))
          (Equiv.refl (SpecIdxGen ι hι hL))).trans
        (Equiv.Set.sumCompl (Set.range (regCoreEmbGen ι hι hL)))))

/-- **The role-partition index equiv** `RegIdxGen ⊕ (CoreIdxGen ⊕ SpecIdxGen) ≃ FlatIdx H`, from
the explicit `roleToFlatGen` (injective + equal card) via `Equiv.ofBijective` (readbacks `rfl`). -/
noncomputable def roleEquivGen :
    (RegIdxGen H r ⊕ (CoreIdxGen H r ⊕ SpecIdxGen ι hι hL)) ≃ FlatIdx H :=
  Equiv.ofBijective (roleToFlatGen ι hι hL)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨roleToFlatGen_injective ι hι hL, card_roleGen ι hι hL⟩)

/-- Core readback: `roleEquivGen (inr (inl c)) = regCoreEmbGen (inr c)`. -/
theorem roleEquivGen_core (c : CoreIdxGen H r) :
    roleEquivGen ι hι hL (Sum.inr (Sum.inl c)) = regCoreEmbGen ι hι hL (Sum.inr c) := rfl

/-- Reg readback: `roleEquivGen (inl ρ) = regCoreEmbGen (inl ρ)`. -/
theorem roleEquivGen_reg (ρ : RegIdxGen H r) :
    roleEquivGen ι hι hL (Sum.inl ρ) = regCoreEmbGen ι hι hL (Sum.inl ρ) := rfl

/-! ## Rung B — the flat index-equiv `e_idxGen` + the measure-preserving split `splitMPGen`

Mirrors the L = 2 `e_idx`/`splitMP`. The reg slot ↦ `RegIdxGen`, core slot ↦ `CoreIdxGen`
(`= FlatIdx (H−r)`, `paramsEquivFlat (H−r)`-ordered), spec slot ↦ `SpecIdxGen`; `roleEquivGen` puts
them at the flat coordinates, then `Fintype.equivFin` reindexes to `Fin (flatDim H)`. -/

/-- `Fin (nRegGen H r) ≃ RegIdxGen H r` (`card_RegIdxGen`; `r ≤ H 0`, `r ≤ H (last L)` by `hι`). -/
noncomputable def regEquivFinGen : Fin (nRegGen H r) ≃ RegIdxGen H r :=
  (Fintype.equivFinOfCardEq (card_RegIdxGen H r
    (by simpa using Fintype.card_le_of_injective (ι 0) (hι 0))
    (by simpa using Fintype.card_le_of_injective (ι (Fin.last L)) (hι (Fin.last L))))).symm

/-- The spectator dimension (`= Fintype.card SpecIdxGen`; kept as a card for the equiv). -/
noncomputable def specDimGen : ℕ := Fintype.card (SpecIdxGen ι hι hL)

/-- **The flat index-equiv** `Fin nReg ⊕ (Fin (flatDim (H−r)) ⊕ Fin specDim) ≃ Fin (flatDim H)`,
aligned to `blockFlatEquivGen` via `roleEquivGen`. -/
noncomputable def e_idxGen :
    Fin (nRegGen H r) ⊕ (Fin (flatDim (fun s => H s - r)) ⊕ Fin (specDimGen ι hι hL))
      ≃ Fin (flatDim H) :=
  (Equiv.sumCongr (regEquivFinGen ι hι)
      (Equiv.sumCongr (Fintype.equivFin (CoreIdxGen H r)).symm
        (Fintype.equivFin (SpecIdxGen ι hι hL)).symm)).trans
    ((roleEquivGen ι hι hL).trans (Fintype.equivFin (FlatIdx H)))

/-- **The measure-preserving flat block split** driven by `e_idxGen`. -/
noncomputable def splitMPGen :
    (Fin (flatDim H) → ℝ) ≃ᵐ
      (Fin (nRegGen H r) → ℝ)
        × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) :=
  splitOfPartition (e_idxGen ι hι hL)

theorem measurePreserving_splitMPGen :
    MeasurePreserving (splitMPGen ι hι hL) (volume : Measure (Fin (flatDim H) → ℝ)) volume :=
  measurePreserving_splitOfPartition (e_idxGen ι hι hL)

/-- Raw reg-block readback: `(splitMPGen x).1 i = x (e_idxGen (inl i))`. -/
theorem splitMPGen_reg (x : Fin (flatDim H) → ℝ) (i : Fin (nRegGen H r)) :
    (splitMPGen ι hι hL x).1 i = x (e_idxGen ι hι hL (Sum.inl i)) := rfl

/-- Raw core-block readback: `(splitMPGen x).2.1 j = x (e_idxGen (inr (inl j)))`. -/
theorem splitMPGen_core (x : Fin (flatDim H) → ℝ) (j : Fin (flatDim (fun s => H s - r))) :
    (splitMPGen ι hι hL x).2.1 j = x (e_idxGen ι hι hL (Sum.inr (Sum.inl j))) := rfl

/-- Raw spec-block readback: `(splitMPGen x).2.2 k = x (e_idxGen (inr (inr k)))`. -/
theorem splitMPGen_spec (x : Fin (flatDim H) → ℝ) (k : Fin (specDimGen ι hι hL)) :
    (splitMPGen ι hι hL x).2.2 k = x (e_idxGen ι hι hL (Sum.inr (Sum.inr k))) := rfl

/-- `e_idxGen` on the core slot: `= equivFin ∘ roleEquivGen ∘ inr∘inl ∘ coreE.symm` (defeq). -/
theorem e_idxGen_core (n : Fin (flatDim (fun s => H s - r))) :
    e_idxGen ι hι hL (Sum.inr (Sum.inl n))
      = Fintype.equivFin (FlatIdx H)
          (roleEquivGen ι hι hL
            (Sum.inr (Sum.inl ((Fintype.equivFin (CoreIdxGen H r)).symm n)))) := rfl

/-- `e_idxGen` on the reg slot: `= equivFin ∘ roleEquivGen ∘ inl ∘ regEquivFinGen` (defeq). -/
theorem e_idxGen_reg (i : Fin (nRegGen H r)) :
    e_idxGen ι hι hL (Sum.inl i)
      = Fintype.equivFin (FlatIdx H)
          (roleEquivGen ι hι hL (Sum.inl (regEquivFinGen ι hι i))) := rfl

/-! ## Rung C — the core-block readback (linchpin for `hfact`)

The `splitMPGen` core block, decoded by `paramsEquivFlat (H − r)`, is exactly the per-layer `₂₂`
corners of `blockFlatEquivGen x` — the reduced `(H − r)` Params (`coreParamsGen`). Mirrors the L = 2
`paramsEquivFlat_symm_splitMP_core`, but the general-`L` layer split needs no `Fin.cases`.
(`paramsEquivFlatLinear_symm_coe_gen`, the linear↔measurable flatten-inverse coe agreement,
is banked in `D1GeGlobalize`.) -/

/-- The reduced-core parameter read off the per-layer `₂₂` corners of `blockFlatEquivGen x`. -/
noncomputable def coreParamsGen (x : Fin (flatDim H) → ℝ) : Params (fun s => H s - r) :=
  fun s => (blockFlatEquivGen H r ι hι x s).toBlocks₂₂

/-- **Core-block readback.** `(paramsEquivFlat (H−r)).symm (splitMPGen x).2.1 = coreParamsGen x`. -/
theorem paramsEquivFlat_symm_splitMPGen_core (x : Fin (flatDim H) → ℝ) :
    (paramsEquivFlat (fun s => H s - r)).symm ((splitMPGen ι hι hL x).2.1)
      = coreParamsGen ι hι x := by
  funext s i j
  rw [paramsEquivFlat_symm_entry, splitMPGen_core, e_idxGen_core, Equiv.symm_apply_apply,
    roleEquivGen_core]
  change x (Fintype.equivFin (FlatIdx H)
      ⟨⟨s, sumSplit (ι s.castSucc) (hι _) (Sum.inr i)⟩,
        sumSplit (ι s.succ) (hι _) (Sum.inr j)⟩) = _
  rw [coreParamsGen, blockFlatEquivGen_apply]
  simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe_gen]
  exact (paramsEquivFlat_symm_entry H x s (sumSplit (ι s.castSucc) (hι _) (Sum.inr i))
    (sumSplit (ι s.succ) (hι _) (Sum.inr j))).symm

/-! ## Rung D — the `Homeomorph` version of `splitMPGen` (with the `ContDiff` inverse)

Mirrors L = 2 `splitHomeoL2`; usable by `rlctAtOn_comp_homeomorph` (which wants `≃ₜ`). -/

/-- `splitMPGen.symm` reads coordinate `c` off the three blocks via `e_idxGen.symm`. -/
theorem splitMPGen_symm_apply
    (q : (Fin (nRegGen H r) → ℝ)
      × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)))
    (c : Fin (flatDim H)) :
    (splitMPGen ι hι hL).symm q c
      = Sum.elim q.1 (Sum.elim q.2.1 q.2.2) ((e_idxGen ι hι hL).symm c) := by
  have h := splitOfPartition_symm_apply (e_idxGen ι hι hL) q ((e_idxGen ι hι hL).symm c)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- `splitMPGen.symm` is `C^∞` (each output coordinate is a projection of one input block). -/
theorem contDiff_splitMPGen_symm :
    ContDiff ℝ (⊤ : ℕ∞) (⇑(splitMPGen ι hι hL).symm) := by
  rw [contDiff_pi]
  intro c
  have hfun : (fun q => (splitMPGen ι hι hL).symm q c)
      = fun q => Sum.elim q.1 (Sum.elim q.2.1 q.2.2) ((e_idxGen ι hι hL).symm c) :=
    funext fun q => splitMPGen_symm_apply ι hι hL q c
  rw [hfun]
  rcases h : (e_idxGen ι hι hL).symm c with i | (j | k)
  · simp only [Sum.elim_inl]
    exact (contDiff_apply ℝ _ i).comp contDiff_fst
  · simp only [Sum.elim_inr, Sum.elim_inl]
    exact (contDiff_apply ℝ _ j).comp (contDiff_fst.comp contDiff_snd)
  · simp only [Sum.elim_inr]
    exact (contDiff_apply ℝ _ k).comp (contDiff_snd.comp contDiff_snd)

/-- The forward `splitMPGen` is continuous (each block coordinate is a projection). -/
theorem continuous_splitMPGen : Continuous (⇑(splitMPGen ι hι hL)) := by
  have hc1 : Continuous fun w : Fin (flatDim H) → ℝ => (splitMPGen ι hι hL w).1 :=
    continuous_pi fun i => by
      have : (fun w : Fin (flatDim H) → ℝ => (splitMPGen ι hι hL w).1 i)
          = fun w => w (e_idxGen ι hι hL (Sum.inl i)) :=
        funext fun w => splitMPGen_reg ι hι hL w i
      rw [this]; exact continuous_apply _
  have hc2 : Continuous fun w : Fin (flatDim H) → ℝ => (splitMPGen ι hι hL w).2.1 :=
    continuous_pi fun j => by
      have : (fun w : Fin (flatDim H) → ℝ => (splitMPGen ι hι hL w).2.1 j)
          = fun w => w (e_idxGen ι hι hL (Sum.inr (Sum.inl j))) :=
        funext fun w => splitMPGen_core ι hι hL w j
      rw [this]; exact continuous_apply _
  have hc3 : Continuous fun w : Fin (flatDim H) → ℝ => (splitMPGen ι hι hL w).2.2 :=
    continuous_pi fun k => by
      have : (fun w : Fin (flatDim H) → ℝ => (splitMPGen ι hι hL w).2.2 k)
          = fun w => w (e_idxGen ι hι hL (Sum.inr (Sum.inr k))) :=
        funext fun w => splitMPGen_spec ι hι hL w k
      rw [this]; exact continuous_apply _
  exact hc1.prodMk (hc2.prodMk hc3)

/-- **The `Homeomorph` version of `splitMPGen`** (same underlying equiv, so the readbacks / MP /
measurable-embedding transfer definitionally), usable by `rlctAtOn_comp_homeomorph`. -/
noncomputable def splitHomeoGen :
    (Fin (flatDim H) → ℝ) ≃ₜ
      (Fin (nRegGen H r) → ℝ)
        × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) where
  toEquiv := (splitMPGen ι hι hL).toEquiv
  continuous_toFun := continuous_splitMPGen ι hι hL
  continuous_invFun := (contDiff_splitMPGen_symm ι hι hL).continuous

@[simp] theorem splitHomeoGen_apply (w : Fin (flatDim H) → ℝ) :
    splitHomeoGen ι hι hL w = splitMPGen ι hι hL w := rfl

theorem measurePreserving_splitHomeoGen :
    MeasurePreserving (splitHomeoGen ι hι hL)
      (volume : Measure (Fin (flatDim H) → ℝ)) volume :=
  measurePreserving_splitMPGen ι hι hL

theorem measurableEmbedding_splitHomeoGen :
    MeasurableEmbedding (splitHomeoGen ι hι hL) :=
  (splitMPGen ι hι hL).measurableEmbedding

/-- `splitHomeoGen` sends the flat origin to the split origin. -/
theorem splitHomeoGen_zero :
    splitHomeoGen ι hι hL (0 : Fin (flatDim H) → ℝ)
      = (0 : (Fin (nRegGen H r) → ℝ)
              × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ))) := by
  apply Prod.ext
  · funext i; exact splitMPGen_reg ι hι hL 0 i
  · apply Prod.ext
    · funext j; exact splitMPGen_core ι hι hL 0 j
    · funext k; exact splitMPGen_spec ι hι hL 0 k

/-! ## Rung E — the regular-block readbacks + the slice-zero of the regular blocks

Each regular flat coordinate decodes to the corresponding `blockFlatEquivGen` block entry (first
layer's `₂₁`, last layer's `₁₁,₁₂`). At the reg-slice (`p = 0`) those coordinates vanish, so the
three regular blocks of `blockFlatEquivGen` vanish — the input to `qResid_slice_value_gen`. -/

/-- The first-layer `₂₁` regular role decodes to `(blockFlatEquivGen x firstLayer).toBlocks₂₁`. -/
theorem reg_entry_first₂₁_gen (x : Fin (flatDim H) → ℝ) (a : Fin (H 0 - r)) (k : Fin r) :
    x (Fintype.equivFin (FlatIdx H) (roleEquivGen ι hι hL (Sum.inl (Sum.inl (a, k)))))
      = (blockFlatEquivGen H r ι hι x (firstLayer hL)).toBlocks₂₁ a k := by
  rw [roleEquivGen_reg]
  change x (Fintype.equivFin (FlatIdx H)
      ⟨⟨firstLayer hL, sumSplit (ι (firstLayer hL).castSucc) (hι _) (Sum.inr a)⟩,
        sumSplit (ι (firstLayer hL).succ) (hι _) (Sum.inl k)⟩) = _
  rw [blockFlatEquivGen_apply]
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe_gen]
  exact (paramsEquivFlat_symm_entry H x (firstLayer hL)
    (sumSplit (ι (firstLayer hL).castSucc) (hι _) (Sum.inr a))
    (sumSplit (ι (firstLayer hL).succ) (hι _) (Sum.inl k))).symm

/-- The last-layer `₁₁` regular role decodes to `(blockFlatEquivGen x lastLayer).toBlocks₁₁`. -/
theorem reg_entry_last₁₁_gen (x : Fin (flatDim H) → ℝ) (k k' : Fin r) :
    x (Fintype.equivFin (FlatIdx H) (roleEquivGen ι hι hL (Sum.inl (Sum.inr (k, Sum.inl k')))))
      = (blockFlatEquivGen H r ι hι x (lastLayer hL)).toBlocks₁₁ k k' := by
  rw [roleEquivGen_reg]
  change x (Fintype.equivFin (FlatIdx H)
      ⟨⟨lastLayer hL, sumSplit (ι (lastLayer hL).castSucc) (hι _) (Sum.inl k)⟩,
        sumSplit (ι (lastLayer hL).succ) (hι _) (Sum.inl k')⟩) = _
  rw [blockFlatEquivGen_apply]
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe_gen]
  exact (paramsEquivFlat_symm_entry H x (lastLayer hL)
    (sumSplit (ι (lastLayer hL).castSucc) (hι _) (Sum.inl k))
    (sumSplit (ι (lastLayer hL).succ) (hι _) (Sum.inl k'))).symm

/-- The last-layer `₁₂` regular role decodes to `(blockFlatEquivGen x lastLayer).toBlocks₁₂` at the
`finCongr`-cast column (the `H (Fin.last L) → H lastLayer.succ` width bridge). -/
theorem reg_entry_last₁₂_gen (x : Fin (flatDim H) → ℝ) (k : Fin r) (b : Fin (H (Fin.last L) - r)) :
    x (Fintype.equivFin (FlatIdx H) (roleEquivGen ι hι hL (Sum.inl (Sum.inr (k, Sum.inr b)))))
      = (blockFlatEquivGen H r ι hι x (lastLayer hL)).toBlocks₁₂ k
          (finCongr (by rw [H_lastLayer_succ H hL]) b) := by
  rw [roleEquivGen_reg]
  change x (Fintype.equivFin (FlatIdx H)
      ⟨⟨lastLayer hL, sumSplit (ι (lastLayer hL).castSucc) (hι _) (Sum.inl k)⟩,
        sumSplit (ι (lastLayer hL).succ) (hι _)
          (Sum.map id (finCongr (by rw [H_lastLayer_succ H hL])) (Sum.inr b))⟩) = _
  rw [blockFlatEquivGen_apply]
  simp only [Matrix.toBlocks₁₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.symm_symm, paramsEquivFlatLinear_symm_coe_gen, Sum.map_inr]
  exact (paramsEquivFlat_symm_entry H x (lastLayer hL)
    (sumSplit (ι (lastLayer hL).castSucc) (hι _) (Sum.inl k))
    (sumSplit (ι (lastLayer hL).succ) (hι _)
      (Sum.inr (finCongr (by rw [H_lastLayer_succ H hL]) b)))).symm

/-- A regular flat coordinate of `splitMPGen.symm ((0), t)` is `0` (its reg block is `0`). -/
theorem reg_zero_of_slice_gen
    (t : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ))
    (ρ : RegIdxGen H r) :
    (splitMPGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t)
        (Fintype.equivFin (FlatIdx H) (roleEquivGen ι hι hL (Sum.inl ρ))) = 0 := by
  have hround : splitMPGen ι hι hL ((splitMPGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
      = ((0 : Fin (nRegGen H r) → ℝ), t) := (splitMPGen ι hι hL).apply_symm_apply _
  have hkey := splitMPGen_reg ι hι hL ((splitMPGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
    ((regEquivFinGen ι hι).symm ρ)
  rw [e_idxGen_reg, Equiv.apply_symm_apply] at hkey
  rw [← hkey, hround]
  rfl

/-- The three regular blocks of `blockFlatEquivGen (splitMPGen.symm ((0), t))` vanish. -/
theorem bChart_slice_reg_zero_gen
    (t : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) :
    (blockFlatEquivGen H r ι hι ((splitMPGen ι hι hL).symm
        ((0 : Fin (nRegGen H r) → ℝ), t)) (firstLayer hL)).toBlocks₂₁ = 0
    ∧ (blockFlatEquivGen H r ι hι ((splitMPGen ι hι hL).symm
        ((0 : Fin (nRegGen H r) → ℝ), t)) (lastLayer hL)).toBlocks₁₁ = 0
    ∧ (blockFlatEquivGen H r ι hι ((splitMPGen ι hι hL).symm
        ((0 : Fin (nRegGen H r) → ℝ), t)) (lastLayer hL)).toBlocks₁₂ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext a k
    rw [← reg_entry_first₂₁_gen ι hι hL _ a k]
    exact reg_zero_of_slice_gen ι hι hL t (Sum.inl (a, k))
  · funext k k'
    rw [← reg_entry_last₁₁_gen ι hι hL _ k k']
    exact reg_zero_of_slice_gen ι hι hL t (Sum.inr (k, Sum.inl k'))
  · funext k b'
    rw [show b' = finCongr (by rw [H_lastLayer_succ H hL])
          ((finCongr (by rw [H_lastLayer_succ H hL]) : Fin (H (Fin.last L) - r) ≃
            Fin (H (lastLayer hL).succ - r)).symm b') from by simp,
      ← reg_entry_last₁₂_gen ι hι hL _ k _]
    exact reg_zero_of_slice_gen ι hι hL t (Sum.inr (k, Sum.inr _))

/-! ## Rung F — the explicit `₂₂` Schur residual `qResidGen` and its global `ContDiff ℝ 1`

The general-`L` port of the L = 2 `qResid` (`D1L2ExplChartClose2`). Built on geleg8's block↔chain
bridge `blockToChainGen` and the reduced-factor telescope `blockDiagProd` (so it matches the ₂₂-part
of the germ's `schurReadoutF_gen`, with the pivot inverse `⁻¹` replaced by the bump-globalised `G`).
Widths are the `deepestChainWidth` chain widths; the endpoint cast to the DLN `H`-widths is deferred
to the slice value (rung G). -/

include ι hι in
/-- The rank bound `r ≤ H v` at every vertex, from injectivity of the pivot family `ι`. -/
theorem r_le_H_gen (v : Fin (L + 1)) : r ≤ H v := by
  simpa using Fintype.card_le_of_injective (ι v) (hι v)

/-- **The reduced-core shift** read off each layer's `₂₂` corner of the base chart value `C₀` (the
general-`L` `coreShiftParam`). -/
noncomputable def coreShiftParamGen (C₀ : BlockParamsGen H r) : Params (fun s => H s - r) :=
  fun s => (C₀ s).toBlocks₂₂

/-- The split flat coordinate type `reg × (core × spec)` (the domain of `qResidGen`). -/
abbrev SplitCoordGen : Type :=
  (Fin (nRegGen H r) → ℝ)
    × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ))

/-- **The block chart value** `blockFlatEquivGen (splitHomeoGen.symm py) + C₀` (gen-`L` `qBlock`);
its `₂₂` Schur residual (with the bump-globalised inverse `G`) is `qResidGen`. -/
noncomputable def qBlockGen (C₀ : BlockParamsGen H r) (py : SplitCoordGen ι hι hL) :
    BlockParamsGen H r :=
  blockFlatEquivGen H r ι hι ((splitHomeoGen ι hι hL).symm py) + C₀

/-- **The chart value bridged to the `ℕ`-chain** via `blockToChainGen` — matches the ₂₂-form
of the germ's `schurReadoutF_gen`. -/
noncomputable def qChainGen (C₀ : BlockParamsGen H r) (py : SplitCoordGen ι hι hL) :
    (s : ℕ) → Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
  blockToChainGen H r (r_le_H_gen ι hι) ι hι (qBlockGen ι hι hL C₀ py)

/-- Each `qChainGen` entry is `C^∞` in `py` (a reindexed affine coord of the `C^∞` block chart).
Mirrors geleg8's `contDiff_b2cg_entry` precomposed with the `C^∞` split inverse. -/
theorem contDiff_qChainGen_entry (C₀ : BlockParamsGen H r) (s : ℕ)
    (i : Fin r ⊕ Fin (deepestChainWidth H s - r))
    (j : Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun py => qChainGen ι hι hL C₀ py s i j) :=
  (contDiff_b2cg_entry H r (r_le_H_gen ι hι) ι hι C₀ s i j).comp
    (contDiff_splitMPGen_symm ι hι hL)

/-- Each entry of the telescope `blockDiagProd (qChainGen …) k` is `C^∞` (induction on
`k`, `contDiff_qChainGen_entry` + entrywise matrix multiplication). -/
theorem contDiff_blockDiagProd_qChainGen_entry (C₀ : BlockParamsGen H r) :
    ∀ (k : ℕ) (i : Fin (deepestChainWidth H 0 - r)) (j : Fin (deepestChainWidth H k - r)),
      ContDiff ℝ (⊤ : ℕ∞) (fun py => blockDiagProd (qChainGen ι hι hL C₀ py) k i j)
  | 0, i, j => by simp only [blockDiagProd]; exact contDiff_const
  | k + 1, i, j => by
      change ContDiff ℝ (⊤ : ℕ∞) (fun py =>
        (blockDiagProd (qChainGen ι hι hL C₀ py) k
          * (qChainGen ι hι hL C₀ py k).toBlocks₂₂) i j)
      exact SchurChartC2.contDiff_matrix_mul_entry
        (fun a b => contDiff_blockDiagProd_qChainGen_entry C₀ k a b)
        (fun a b => contDiff_qChainGen_entry ι hι hL C₀ k (Sum.inr a) (Sum.inr b)) i j

/-- **The `₂₂` Schur residual MATRIX** (gen `L`, bump-globalised `G`): the ₂₂-part of the
germ's `recoverProductGen`-readout, with the pivot inverse `⁻¹` swapped for `G`. In the chain widths
(`deepestChainWidth`); the last slot is `L − 1`. -/
noncomputable def qResidMatGen (C₀ : BlockParamsGen H r)
    (Br022 : Matrix (Fin (deepestChainWidth H 0 - r))
      (Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
    (py : SplitCoordGen ι hι hL) :
    Matrix (Fin (deepestChainWidth H 0 - r)) (Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ :=
  (qChainGen ι hι hL C₀ py 0).toBlocks₂₁
      * G ((qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₁)
      * (qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₂
    + blockDiagProd (qChainGen ι hι hL C₀ py) (L - 1 + 1)
    - Br022

/-- **The explicit `₂₂` Schur residual `qResidGen`** (gen `L`): flattened `qResidMatGen`, as a
`EuclideanSpace` vector. -/
noncomputable def qResidGen (C₀ : BlockParamsGen H r)
    (Br022 : Matrix (Fin (deepestChainWidth H 0 - r))
      (Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) :
    SplitCoordGen ι hι hL
      → EuclideanSpace ℝ
          (Fin ((deepestChainWidth H 0 - r) * (deepestChainWidth H (L - 1 + 1) - r))) := fun py =>
  (EuclideanSpace.equiv
      (Fin ((deepestChainWidth H 0 - r) * (deepestChainWidth H (L - 1 + 1) - r))) ℝ).symm
    (fun i => qResidMatGen ι hι hL C₀ Br022 G py
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

/-- Coordinate readback: `qResidGen i = qResidMatGen` at `finProdFinEquiv.symm i`. -/
theorem qResid_apply_gen (C₀ : BlockParamsGen H r)
    (Br022 : Matrix (Fin (deepestChainWidth H 0 - r))
      (Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (py : SplitCoordGen ι hι hL) (i) :
    (qResidGen ι hι hL C₀ Br022 G py) i
      = qResidMatGen ι hι hL C₀ Br022 G py
          (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := rfl

/-- `∑ᵢ qResidGen² = ∑_{a,b} (qResidMatGen a b)²` (flatten reindex by `finProdFinEquiv`). -/
theorem qResid_sq_sum_gen (C₀ : BlockParamsGen H r)
    (Br022 : Matrix (Fin (deepestChainWidth H 0 - r))
      (Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (py : SplitCoordGen ι hι hL) :
    ∑ i, (qResidGen ι hι hL C₀ Br022 G py) i ^ 2
      = ∑ a : Fin (deepestChainWidth H 0 - r), ∑ b : Fin (deepestChainWidth H (L - 1 + 1) - r),
          (qResidMatGen ι hι hL C₀ Br022 G py a b) ^ 2 := by
  simp_rw [qResid_apply_gen]
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin (deepestChainWidth H 0 - r) × Fin (deepestChainWidth H (L - 1 + 1) - r) =>
      (qResidMatGen ι hι hL C₀ Br022 G py p.1 p.2) ^ 2), Fintype.sum_prod_type]

/-- **`qResidGen` is globally `ContDiff ℝ 1`** (given `G` is `ContDiff ℝ 1`). The chain entries are
`C^∞` in `py` (`qChainGen`); `G(pivot)` is the `C¹` `G` composed with the `C^∞` `₁₁` block; the two
matrix products, the telescope `blockDiagProd`, and the constant `Br022` assemble entrywise. -/
theorem contDiff_qResidGen (C₀ : BlockParamsGen H r)
    (Br022 : Matrix (Fin (deepestChainWidth H 0 - r))
      (Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (qResidGen ι hι hL C₀ Br022 G) := by
  have h1top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  refine contDiff_euclidean.mpr fun i => ?_
  set a := (finProdFinEquiv.symm i).1 with ha
  set b := (finProdFinEquiv.symm i).2 with hb
  -- `G(pivot)` block entries are `C¹`.
  have hGpiv : ∀ k k' : Fin r,
      ContDiff ℝ 1 (fun py => (G ((qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₁)) k k') := by
    intro k k'
    have hM11 : ContDiff ℝ 1 (fun py => (qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₁) :=
      contDiff_matrix_of_entries fun i' j' =>
        (contDiff_qChainGen_entry ι hι hL C₀ (L - 1) (Sum.inl i') (Sum.inl j')).of_le h1top
    exact contDiff_matrixEntry (hG.comp hM11) k k'
  -- the Schur product, entrywise `C¹`.
  have hSchur : ContDiff ℝ 1 (fun py =>
      ((qChainGen ι hι hL C₀ py 0).toBlocks₂₁
        * G ((qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₁)
        * (qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₂) a b) := by
    refine contDiff_matrix_mul_entry
      (fun i' k' => contDiff_matrix_mul_entry
        (fun a' k'' => (contDiff_qChainGen_entry ι hι hL C₀ 0 (Sum.inr a') (Sum.inl k'')).of_le
          h1top) (fun k'' k''' => hGpiv k'' k''') i' k') ?_ a b
    intro k' j'
    exact (contDiff_qChainGen_entry ι hι hL C₀ (L - 1) (Sum.inl k') (Sum.inr j')).of_le h1top
  -- the telescope entry, `C¹`.
  have hTele : ContDiff ℝ 1
      (fun py => blockDiagProd (qChainGen ι hι hL C₀ py) (L - 1 + 1) a b) :=
    (contDiff_blockDiagProd_qChainGen_entry ι hι hL C₀ (L - 1 + 1) a b).of_le h1top
  have hfun : (fun py => qResidGen ι hι hL C₀ Br022 G py i)
      = fun py => ((qChainGen ι hι hL C₀ py 0).toBlocks₂₁
            * G ((qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₁)
            * (qChainGen ι hι hL C₀ py (L - 1)).toBlocks₁₂) a b
          + blockDiagProd (qChainGen ι hι hL C₀ py) (L - 1 + 1) a b
          - Br022 a b := by
    funext py
    change qResidMatGen ι hι hL C₀ Br022 G py a b = _
    simp only [qResidMatGen, Matrix.sub_apply, Matrix.add_apply]
  rw [hfun]
  exact (hSchur.add hTele).sub contDiff_const

/-! ## Rung G — the reduced-core telescope and the slice value `qResid_slice_value_gen`

At the reg-slice (`p = 0`) the three regular corners of `blockFlatEquivGen x` vanish
(`bChart_slice_reg_zero_gen`), so the Schur term reduces to `Br022` (via the corner facts +
the Schur-zero `hschur`), leaving the reduced-core product `blockDiagProd`. The telescope identifies
`blockDiagProd (blockToChainGen B) L` with the reduced-`(H−r)` product `prod (H−r) (₂₂ of B)` (up to
the endpoint block reindex). Mirrors the L = 2 `qResid_slice_value`. -/

/-- **The `inr`-restriction of an equiv fixing the `inl` summand.** If `e : ρ ⊕ β ≃ ρ ⊕ γ` fixes the
left summand pointwise, its right summand maps bijectively to the right — the induced `β ≃ γ`. -/
theorem apply_inr_of_fixInl {ρ β γ : Type*} (e : ρ ⊕ β ≃ ρ ⊕ γ)
    (hfix : ∀ a, e (Sum.inl a) = Sum.inl a) (b : β) : ∃ c, e (Sum.inr b) = Sum.inr c := by
  rcases h : e (Sum.inr b) with a | c
  · exact absurd (e.injective (h.trans (hfix a).symm)) (by simp)
  · exact ⟨c, rfl⟩

/-- `e.symm` fixes `inl` whenever `e` does. -/
theorem symm_fixInl {ρ β γ : Type*} (e : ρ ⊕ β ≃ ρ ⊕ γ)
    (hfix : ∀ a, e (Sum.inl a) = Sum.inl a) (a : ρ) : e.symm (Sum.inl a) = Sum.inl a := by
  conv_lhs => rw [← hfix a]
  rw [e.symm_apply_apply]

/-- **The induced right-block equiv** `β ≃ γ` of an `inl`-fixing `e : ρ ⊕ β ≃ ρ ⊕ γ`. -/
noncomputable def rightEquivOfFixInl {ρ β γ : Type*} (e : ρ ⊕ β ≃ ρ ⊕ γ)
    (hfix : ∀ a, e (Sum.inl a) = Sum.inl a) : β ≃ γ where
  toFun b := (apply_inr_of_fixInl e hfix b).choose
  invFun c := (apply_inr_of_fixInl e.symm (symm_fixInl e hfix) c).choose
  left_inv b := by
    have hf : e (Sum.inr b) = Sum.inr ((apply_inr_of_fixInl e hfix b).choose) :=
      (apply_inr_of_fixInl e hfix b).choose_spec
    have hg := (apply_inr_of_fixInl e.symm (symm_fixInl e hfix)
      ((apply_inr_of_fixInl e hfix b).choose)).choose_spec
    have hround : e.symm (Sum.inr ((apply_inr_of_fixInl e hfix b).choose)) = Sum.inr b := by
      rw [← hf, e.symm_apply_apply]
    exact Sum.inr_injective (hg.symm.trans hround)
  right_inv c := by
    have hg : e.symm (Sum.inr c)
        = Sum.inr ((apply_inr_of_fixInl e.symm (symm_fixInl e hfix) c).choose) :=
      (apply_inr_of_fixInl e.symm (symm_fixInl e hfix) c).choose_spec
    have hf := (apply_inr_of_fixInl e hfix
      ((apply_inr_of_fixInl e.symm (symm_fixInl e hfix) c).choose)).choose_spec
    have hround : e (Sum.inr ((apply_inr_of_fixInl e.symm (symm_fixInl e hfix) c).choose))
        = Sum.inr c := by
      rw [← hg, e.apply_symm_apply]
    exact Sum.inr_injective (hf.symm.trans hround)

/-- `e (Sum.inr b) = Sum.inr (rightEquivOfFixInl e hfix b)`. -/
theorem rightEquivOfFixInl_apply {ρ β γ : Type*} (e : ρ ⊕ β ≃ ρ ⊕ γ)
    (hfix : ∀ a, e (Sum.inl a) = Sum.inl a) (b : β) :
    e (Sum.inr b) = Sum.inr (rightEquivOfFixInl e hfix b) :=
  (apply_inr_of_fixInl e hfix b).choose_spec

/-- `e.symm (Sum.inr c) = Sum.inr ((rightEquivOfFixInl e hfix).symm c)`. -/
theorem rightEquivOfFixInl_symm_apply {ρ β γ : Type*} (e : ρ ⊕ β ≃ ρ ⊕ γ)
    (hfix : ∀ a, e (Sum.inl a) = Sum.inl a) (c : γ) :
    e.symm (Sum.inr c) = Sum.inr ((rightEquivOfFixInl e hfix).symm c) :=
  (apply_inr_of_fixInl e.symm (symm_fixInl e hfix) c).choose_spec

/-- **Block-diagonal reindex preserves the `₂₂` corner.** For `eR`, `eC` fixing `inl`, the `₂₂`
of a reindexed matrix is the `₂₂` block reindexed by the induced right-block equivs. -/
theorem reindex_toBlocks₂₂_of_fixInl {ρ β γ β' γ' : Type*}
    (eR : ρ ⊕ β ≃ ρ ⊕ β') (eC : ρ ⊕ γ ≃ ρ ⊕ γ')
    (hR : ∀ a, eR (Sum.inl a) = Sum.inl a) (hC : ∀ a, eC (Sum.inl a) = Sum.inl a)
    (M : Matrix (ρ ⊕ β) (ρ ⊕ γ) ℝ) :
    (Matrix.reindex eR eC M).toBlocks₂₂
      = Matrix.reindex (rightEquivOfFixInl eR hR) (rightEquivOfFixInl eC hC) M.toBlocks₂₂ := by
  ext a b
  simp only [Matrix.toBlocks₂₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    rightEquivOfFixInl_symm_apply eR hR, rightEquivOfFixInl_symm_apply eC hC]

/-- Block-diagonal reindex: the `₁₁` (pivot × pivot) corner is unchanged. -/
theorem reindex_toBlocks₁₁_of_fixInl {ρ β γ β' γ' : Type*}
    (eR : ρ ⊕ β ≃ ρ ⊕ β') (eC : ρ ⊕ γ ≃ ρ ⊕ γ')
    (hR : ∀ a, eR (Sum.inl a) = Sum.inl a) (hC : ∀ a, eC (Sum.inl a) = Sum.inl a)
    (M : Matrix (ρ ⊕ β) (ρ ⊕ γ) ℝ) :
    (Matrix.reindex eR eC M).toBlocks₁₁ = M.toBlocks₁₁ := by
  ext a b
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    symm_fixInl eR hR, symm_fixInl eC hC]

/-- Block-diagonal reindex: the `₂₁` (nonpivot × pivot) corner reindexes on the row only. -/
theorem reindex_toBlocks₂₁_of_fixInl {ρ β γ β' γ' : Type*}
    (eR : ρ ⊕ β ≃ ρ ⊕ β') (eC : ρ ⊕ γ ≃ ρ ⊕ γ')
    (hR : ∀ a, eR (Sum.inl a) = Sum.inl a) (hC : ∀ a, eC (Sum.inl a) = Sum.inl a)
    (M : Matrix (ρ ⊕ β) (ρ ⊕ γ) ℝ) :
    (Matrix.reindex eR eC M).toBlocks₂₁
      = Matrix.reindex (rightEquivOfFixInl eR hR) (Equiv.refl ρ) M.toBlocks₂₁ := by
  ext a k
  simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    symm_fixInl eC hC, rightEquivOfFixInl_symm_apply eR hR, Equiv.refl_symm, Equiv.refl_apply]

/-- Block-diagonal reindex: the `₁₂` (pivot × nonpivot) corner reindexes on the column only. -/
theorem reindex_toBlocks₁₂_of_fixInl {ρ β γ β' γ' : Type*}
    (eR : ρ ⊕ β ≃ ρ ⊕ β') (eC : ρ ⊕ γ ≃ ρ ⊕ γ')
    (hR : ∀ a, eR (Sum.inl a) = Sum.inl a) (hC : ∀ a, eC (Sum.inl a) = Sum.inl a)
    (M : Matrix (ρ ⊕ β) (ρ ⊕ γ) ℝ) :
    (Matrix.reindex eR eC M).toBlocks₁₂
      = Matrix.reindex (Equiv.refl ρ) (rightEquivOfFixInl eC hC) M.toBlocks₁₂ := by
  ext k b
  simp only [Matrix.toBlocks₁₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    symm_fixInl eR hR, rightEquivOfFixInl_symm_apply eC hC, Equiv.refl_symm, Equiv.refl_apply]

/-- **The per-vertex block equiv** at vertex `k`,
the common composite of `blockToChainGen`'s `rowEq`/`colEq` (`rowEq s = vertexEq s.castSucc`,
`colEq s = vertexEq s.succ`). Unifies the two so the telescope's middle reindexes cancel. -/
noncomputable def vertexEq (k : ℕ) (hk : k < L + 1) :
    Fin r ⊕ Fin (H ⟨k, hk⟩ - r) ≃ Fin r ⊕ Fin (deepestChainWidth H k - r) :=
  (sumSplit (ι ⟨k, hk⟩) (hι ⟨k, hk⟩)).trans
    ((finCongr (H_eq_deepestChainWidth H k hk)).trans
      (genChainSplit H r (r_le_H_gen ι hι) ι hι k))

/-- `vertexEq` fixes the pivot (`inl`) summand: the pivot `ι ⟨k,·⟩` recasts to `genPivotN`, which
`genChainSplit` sends back to `Sum.inl`. -/
theorem vertexEq_inl (k : ℕ) (hk : k < L + 1) (a : Fin r) :
    vertexEq ι hι k hk (Sum.inl a) = Sum.inl a := by
  have hpiv : (finCongr (H_eq_deepestChainWidth H k hk)) (ι ⟨k, hk⟩ a)
      = genPivotN H r (r_le_H_gen ι hι) ι k a := by
    rw [genPivotN, dif_pos hk]; rfl
  simp only [vertexEq, Equiv.trans_apply, sumSplit_inl]
  rw [hpiv, genChainSplit, ← sumSplit_inl (genPivotN H r (r_le_H_gen ι hι) ι k)
    (genPivotN_inj H r (r_le_H_gen ι hι) ι hι k) a, Equiv.symm_apply_apply]

/-- **The induced right-block equiv at vertex `k`** `Fin (H ⟨k,·⟩ − r) ≃ Fin (dcw H k − r)`. -/
noncomputable def vertexInr (k : ℕ) (hk : k < L + 1) :
    Fin (H ⟨k, hk⟩ - r) ≃ Fin (deepestChainWidth H k - r) :=
  rightEquivOfFixInl (vertexEq ι hι k hk) (vertexEq_inl ι hι k hk)

/-- **The per-layer `₂₂` readback of `blockToChainGen`** (slot `s < L`): the `₂₂` corner is the
block param's `₂₂` reindexed by the vertex right-block equivs `vertexInr s`, `vertexInr (s+1)`. -/
theorem blockToChainGen_toBlocks₂₂ (B : BlockParamsGen H r) (s : ℕ) (hs : s < L) :
    (blockToChainGen H r (r_le_H_gen ι hι) ι hι B s).toBlocks₂₂
      = Matrix.reindex (vertexInr ι hι s (by omega)) (vertexInr ι hι (s + 1) (by omega))
          ((B ⟨s, hs⟩).toBlocks₂₂) := by
  rw [blockToChainGen, dif_pos hs]
  exact reindex_toBlocks₂₂_of_fixInl (vertexEq ι hι s (by omega)) (vertexEq ι hι (s + 1) (by omega))
    (vertexEq_inl ι hι s (by omega)) (vertexEq_inl ι hι (s + 1) (by omega)) (B ⟨s, hs⟩)

/-- `blockToChainGen`'s `₂₁` corner (slot `s < L`): reindexed on the row only. -/
theorem blockToChainGen_toBlocks₂₁ (B : BlockParamsGen H r) (s : ℕ) (hs : s < L) :
    (blockToChainGen H r (r_le_H_gen ι hι) ι hι B s).toBlocks₂₁
      = Matrix.reindex (vertexInr ι hι s (by omega)) (Equiv.refl (Fin r))
          ((B ⟨s, hs⟩).toBlocks₂₁) := by
  rw [blockToChainGen, dif_pos hs]
  exact reindex_toBlocks₂₁_of_fixInl (vertexEq ι hι s (by omega)) (vertexEq ι hι (s + 1) (by omega))
    (vertexEq_inl ι hι s (by omega)) (vertexEq_inl ι hι (s + 1) (by omega)) (B ⟨s, hs⟩)

/-- `blockToChainGen`'s `₁₁` corner (slot `s < L`): unchanged (pivot × pivot). -/
theorem blockToChainGen_toBlocks₁₁ (B : BlockParamsGen H r) (s : ℕ) (hs : s < L) :
    (blockToChainGen H r (r_le_H_gen ι hι) ι hι B s).toBlocks₁₁ = (B ⟨s, hs⟩).toBlocks₁₁ := by
  rw [blockToChainGen, dif_pos hs]
  exact reindex_toBlocks₁₁_of_fixInl (vertexEq ι hι s (by omega)) (vertexEq ι hι (s + 1) (by omega))
    (vertexEq_inl ι hι s (by omega)) (vertexEq_inl ι hι (s + 1) (by omega)) (B ⟨s, hs⟩)

/-- `blockToChainGen`'s `₁₂` corner (slot `s < L`): reindexed on the column only. -/
theorem blockToChainGen_toBlocks₁₂ (B : BlockParamsGen H r) (s : ℕ) (hs : s < L) :
    (blockToChainGen H r (r_le_H_gen ι hι) ι hι B s).toBlocks₁₂
      = Matrix.reindex (Equiv.refl (Fin r)) (vertexInr ι hι (s + 1) (by omega))
          ((B ⟨s, hs⟩).toBlocks₁₂) := by
  rw [blockToChainGen, dif_pos hs]
  exact reindex_toBlocks₁₂_of_fixInl (vertexEq ι hι s (by omega)) (vertexEq ι hι (s + 1) (by omega))
    (vertexEq_inl ι hι s (by omega)) (vertexEq_inl ι hι (s + 1) (by omega)) (B ⟨s, hs⟩)

/-- **Generic reindexed-product cancel** (matching middle equiv). -/
theorem reindex_mul_reindex {ρ σ τ ρ' μ τ' : Type*} [Fintype σ] [Fintype μ]
    (eR : ρ ≃ ρ') (eMid : σ ≃ μ) (eC : τ ≃ τ')
    (A : Matrix ρ σ ℝ) (Bm : Matrix σ τ ℝ) :
    Matrix.reindex eR eMid A * Matrix.reindex eMid eC Bm = Matrix.reindex eR eC (A * Bm) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A Bm eR.symm eMid.symm eC.symm

/-- **The reduced-core telescope** (prefix form). `blockDiagProd (blockToChainGen B) k` is the
reduced `(H−r)` product `prodAux (H−r) (₂₂ of B) k` reindexed by the endpoint vertex equivs.
Induction on `k`; peels `blockDiagProd _ (k+1) = _ * (Q k)₂₂` (`blockToChainGen_toBlocks₂₂`) against
`prodAux_succ`, the matching middle `vertexInr k` cancelling (`reindex_mul_reindex`). -/
theorem blockDiagProd_blockToChainGen_prefix (B : BlockParamsGen H r) :
    ∀ (k : ℕ) (hk : k < L + 1),
      blockDiagProd (blockToChainGen H r (r_le_H_gen ι hι) ι hι B) k
        = Matrix.reindex (vertexInr ι hι 0 (Nat.zero_lt_succ L)) (vertexInr ι hι k hk)
            (prodAux (fun s => H s - r) (fun s => (B s).toBlocks₂₂) k hk)
  | 0, hk => by
      have hpr : vertexInr ι hι 0 (Nat.zero_lt_succ L) = vertexInr ι hι 0 hk := rfl
      rw [show blockDiagProd (blockToChainGen H r (r_le_H_gen ι hι) ι hι B) 0
            = (1 : Matrix (Fin (deepestChainWidth H 0 - r)) (Fin (deepestChainWidth H 0 - r)) ℝ)
          from rfl,
        show prodAux (fun s => H s - r) (fun s => (B s).toBlocks₂₂) 0 hk
            = (1 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) 0)) ℝ) from rfl,
        hpr, Matrix.reindex_apply]
      exact (Matrix.submatrix_one_equiv (vertexInr ι hι 0 hk).symm).symm
  | k + 1, hk => by
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      rw [show blockDiagProd (blockToChainGen H r (r_le_H_gen ι hι) ι hι B) (k + 1)
            = blockDiagProd (blockToChainGen H r (r_le_H_gen ι hι) ι hι B) k
              * (blockToChainGen H r (r_le_H_gen ι hι) ι hι B k).toBlocks₂₂ from rfl,
        blockDiagProd_blockToChainGen_prefix B k hk',
        blockToChainGen_toBlocks₂₂ ι hι B k hkL, reindex_mul_reindex,
        prodAux_succ (fun s => H s - r) (fun s => (B s).toBlocks₂₂) k hk rfl rfl]
      rfl

/-- **The slice value of `qResidMatGen`** at `p = 0`: the three regular corners of the chart
vanish (`bChart_slice_reg_zero_gen`), so the chain's regular corners equal `C₀`'s (= `Br`'s, via
`h11/h12/h21`); the Schur term becomes `Br₂₁·Br₁₁⁻¹·Br₁₂ = Br₂₂` (`hGeval`, `hschur`) and cancels
`Br₂₂`, leaving the reduced-core telescope `prodAux (H−r) (coreParamsGen + coreShiftParamGen)`. The
general-`L` port of `qResid_slice_value`. -/
theorem qResid_slice_value_gen (C₀ : BlockParamsGen H r)
    (Br : Matrix (Fin r ⊕ Fin (deepestChainWidth H 0 - r))
      (Fin r ⊕ Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ)
    (hGeval : G (Br.toBlocks₁₁) = (Br.toBlocks₁₁)⁻¹)
    (h11 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ (L - 1)).toBlocks₁₁ = Br.toBlocks₁₁)
    (h12 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ (L - 1)).toBlocks₁₂ = Br.toBlocks₁₂)
    (h21 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ 0).toBlocks₂₁ = Br.toBlocks₂₁)
    (hschur : Br.toBlocks₂₂ = Br.toBlocks₂₁ * (Br.toBlocks₁₁)⁻¹ * Br.toBlocks₁₂)
    (t : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) :
    qResidMatGen ι hι hL C₀ Br.toBlocks₂₂ G ((0 : Fin (nRegGen H r) → ℝ), t)
      = Matrix.reindex (vertexInr ι hι 0 (Nat.zero_lt_succ L))
          (vertexInr ι hι (L - 1 + 1) (by omega))
          (prodAux (fun s => H s - r)
            (coreParamsGen ι hι
                ((splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
              + coreShiftParamGen C₀) (L - 1 + 1) (by omega)) := by
  classical
  set x := (splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t) with hx
  obtain ⟨hz21, hz11, hz12⟩ := bChart_slice_reg_zero_gen ι hι hL t
  have hL0 : (0 : ℕ) < L := by omega
  have hLm1 : L - 1 < L := by omega
  have hqb : qBlockGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t)
      = blockFlatEquivGen H r ι hι x + C₀ := rfl
  -- the reg corners of the chart vanish at the slice (index-recast form).
  have hbfe21 : (blockFlatEquivGen H r ι hι x ⟨0, hL0⟩).toBlocks₂₁ = 0 := hz21
  have hbfe11 : (blockFlatEquivGen H r ι hι x ⟨L - 1, hLm1⟩).toBlocks₁₁ = 0 := hz11
  have hbfe12 : (blockFlatEquivGen H r ι hι x ⟨L - 1, hLm1⟩).toBlocks₁₂ = 0 := hz12
  -- `(qBlock ⟨·⟩)` reg corners equal `C₀`'s.
  have hqb21 : (qBlockGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t) ⟨0, hL0⟩).toBlocks₂₁
      = (C₀ ⟨0, hL0⟩).toBlocks₂₁ := by
    rw [hqb, Pi.add_apply]; ext a k
    simp only [Matrix.toBlocks₂₁, Matrix.add_apply, Matrix.of_apply]
    have := congrFun (congrFun hbfe21 a) k
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
    rw [this, zero_add]
  have hqb11 : (qBlockGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t) ⟨L - 1, hLm1⟩).toBlocks₁₁
      = (C₀ ⟨L - 1, hLm1⟩).toBlocks₁₁ := by
    rw [hqb, Pi.add_apply]; ext a k
    simp only [Matrix.toBlocks₁₁, Matrix.add_apply, Matrix.of_apply]
    have := congrFun (congrFun hbfe11 a) k
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.zero_apply] at this
    rw [this, zero_add]
  have hqb12 : (qBlockGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t) ⟨L - 1, hLm1⟩).toBlocks₁₂
      = (C₀ ⟨L - 1, hLm1⟩).toBlocks₁₂ := by
    rw [hqb, Pi.add_apply]; ext a k
    simp only [Matrix.toBlocks₁₂, Matrix.add_apply, Matrix.of_apply]
    have := congrFun (congrFun hbfe12 a) k
    simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.zero_apply] at this
    rw [this, zero_add]
  -- transport to the chain's corners = `Br`'s corners.
  have hQ21 : (qChainGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t) 0).toBlocks₂₁
      = Br.toBlocks₂₁ := by
    rw [qChainGen, blockToChainGen_toBlocks₂₁ ι hι _ 0 hL0, hqb21,
      ← blockToChainGen_toBlocks₂₁ ι hι C₀ 0 hL0, h21]
  have hQ11 : (qChainGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t) (L - 1)).toBlocks₁₁
      = Br.toBlocks₁₁ := by
    rw [qChainGen, blockToChainGen_toBlocks₁₁ ι hι _ (L - 1) hLm1, hqb11,
      ← blockToChainGen_toBlocks₁₁ ι hι C₀ (L - 1) hLm1, h11]
  have hQ12 : (qChainGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t) (L - 1)).toBlocks₁₂
      = Br.toBlocks₁₂ := by
    rw [qChainGen, blockToChainGen_toBlocks₁₂ ι hι _ (L - 1) hLm1, hqb12,
      ← blockToChainGen_toBlocks₁₂ ι hι C₀ (L - 1) hLm1, h12]
  -- the telescope of the reduced core.
  have hTele : blockDiagProd (qChainGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t)) (L - 1 + 1)
      = Matrix.reindex (vertexInr ι hι 0 (Nat.zero_lt_succ L))
          (vertexInr ι hι (L - 1 + 1) (by omega))
          (prodAux (fun s => H s - r) (coreParamsGen ι hι x + coreShiftParamGen C₀)
            (L - 1 + 1) (by omega)) := by
    rw [qChainGen, blockDiagProd_blockToChainGen_prefix ι hι
      (qBlockGen ι hι hL C₀ ((0 : Fin (nRegGen H r) → ℝ), t)) (L - 1 + 1) (by omega)]
    rfl
  -- assemble: the Schur term cancels `Br₂₂`, leaving the telescope.
  rw [qResidMatGen, hQ21, hQ11, hQ12, hGeval, ← hschur, hTele, add_sub_cancel_left]

/-! ## Rung H — the conditional `≥`-leg producer from the explicit `qResidGen` chart

Given the explicit-chart data (`C₀`, `Br`, the bump-globalised inverse `G`, the corner facts,
and the chart-transfer `hchart` in `qResidGen` terms), the general-`L` D1 `≥`-leg producer
conclusion holds. The germ `hchart` is a HYPOTHESIS (the controller discharges it via geleg8's
`schurReadoutF_gen` seam). Everything else — the slice value (G), the core-translation reindex `e`,
the Gram unit `u ≡ 1`, and the a.e.-nonvanishing `hRne` — is reconstructed and fed to the banked
consumer `d1ge_hAtV_of_explicit_chart_genL`. General-`L` port of `d1ge_L2_hAtV_explicit_close`. -/
theorem d1ge_hAtV_of_qResid_chart_genL
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (C₀ : BlockParamsGen H r)
    (Br : Matrix (Fin r ⊕ Fin (deepestChainWidth H 0 - r))
      (Fin r ⊕ Fin (deepestChainWidth H (L - 1 + 1) - r)) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ) (hGcd : ContDiff ℝ 1 G)
    (hGeval : G (Br.toBlocks₁₁) = (Br.toBlocks₁₁)⁻¹)
    (h11 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ (L - 1)).toBlocks₁₁ = Br.toBlocks₁₁)
    (h12 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ (L - 1)).toBlocks₁₂ = Br.toBlocks₁₂)
    (h21 : (blockToChainGen H r (r_le_H_gen ι hι) ι hι C₀ 0).toBlocks₂₁ = Br.toBlocks₂₁)
    (hschur : Br.toBlocks₂₂ = Br.toBlocks₂₁ * (Br.toBlocks₁₁)⁻¹ * Br.toBlocks₁₂)
    (hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin (nRegGen H r) → ℝ)
            × ((Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)) =>
              (∑ i, p.1 i ^ 2) + (∑ i, qResidGen ι hι hL C₀ Br.toBlocks₂₂ G p i ^ 2))
          ((0 : Fin (nRegGen H r) → ℝ),
            (0 : (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ)))) :
    ∃ P : Params (fun s => H s - r),
      (nRegGen H r : ℝ≥0∞) / 2
          + rlctAtOn (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0))
                  (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
              P
        ≤ rlctAt H (dlnLoss H B) v := by
  classical
  set Y := (Fin (flatDim (fun s => H s - r)) → ℝ) × (Fin (specDimGen ι hι hL) → ℝ) with hY
  have hMpos : ∀ s, 1 ≤ H s - r := fun s => Nat.sub_pos_of_lt (hpos s)
  set qₑ := qResidGen ι hι hL C₀ Br.toBlocks₂₂ G with hqe
  have hq : ContDiff ℝ 1 qₑ := contDiff_qResidGen ι hι hL C₀ Br.toBlocks₂₂ G hGcd
  set eshift := paramsEquivFlat (fun s => H s - r) (coreShiftParamGen C₀) with heshift
  set e : Y ≃ₜ Y :=
    (Homeomorph.addRight eshift).prodCongr (Homeomorph.refl (Fin (specDimGen ι hι hL) → ℝ))
      with he_def
  have he_mp : MeasurePreserving e (volume : Measure Y) volume := by
    rw [he_def]
    exact (measurePreserving_add_right volume eshift).prod (MeasurePreserving.id volume)
  have he_emb : MeasurableEmbedding e := e.measurableEmbedding
  -- the `e`-connection: `psymm (e t).1 = coreParamsGen (split.symm) + coreShiftParamGen C₀`.
  have hEconn : ∀ t : Y, (paramsEquivFlat (fun s => H s - r)).symm (e t).1
      = coreParamsGen ι hι ((splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
          + coreShiftParamGen C₀ := by
    intro t
    have hround : splitMPGen ι hι hL
        ((splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
        = ((0 : Fin (nRegGen H r) → ℝ), t) := by
      have := (splitHomeoGen ι hι hL).apply_symm_apply ((0 : Fin (nRegGen H r) → ℝ), t)
      rw [splitHomeoGen_apply] at this; exact this
    have hcp : coreParamsGen ι hι
        ((splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
        = (paramsEquivFlat (fun s => H s - r)).symm t.1 := by
      rw [← paramsEquivFlat_symm_splitMPGen_core, hround]
    rw [hcp]
    have hlin : ∀ y : Fin (flatDim (fun s => H s - r)) → ℝ,
        (paramsEquivFlat (fun s => H s - r)).symm y
          = (paramsEquivFlatLinear (fun s => H s - r)).symm y :=
      fun y => by rw [paramsEquivFlatLinear_symm_coe_gen]
    change (paramsEquivFlat (fun s => H s - r)).symm (t.1 + eshift)
        = (paramsEquivFlat (fun s => H s - r)).symm t.1 + coreShiftParamGen C₀
    rw [hlin (t.1 + eshift), hlin t.1, map_add, heshift, ← paramsEquivFlatLinear_coe,
      (paramsEquivFlatLinear (fun s => H s - r)).symm_apply_apply]
  -- the slice value in `dlnLoss` form (feeds `hfact` and `hRne`).
  have hslicez : ∀ t : Y, (∑ i, qₑ ((0 : Fin (nRegGen H r) → ℝ), t) i ^ 2)
      = dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm (e t).1) := by
    intro t
    obtain ⟨last, rfl⟩ : ∃ last, L = last + 1 := ⟨L - 1, by omega⟩
    rw [hqe, qResid_sq_sum_gen,
      qResid_slice_value_gen ι hι hL C₀ Br G hGeval h11 h12 h21 hschur t, hEconn t, dlnLoss,
      sum_sq_reindex_gen (prod (fun s => H s - r)
          (coreParamsGen ι hι ((splitHomeoGen ι hι hL).symm ((0 : Fin (nRegGen H r) → ℝ), t))
            + coreShiftParamGen C₀))
        (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last (last + 1)))) ℝ)
        (vertexInr ι hι 0 (Nat.zero_lt_succ (last + 1)))
        (vertexInr ι hι (last + 1) (by omega))]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.zero_apply,
      sub_zero]
    rfl
  -- assemble the consumer inputs.
  refine d1ge_hAtV_of_explicit_chart_genL H r B v qₑ hq (0 : Y) ?_ ?_ e he_mp he_emb
    (fun _ => 1) measurable_const 1 1 (by norm_num)
    ⟨Set.univ, Filter.univ_mem, fun _ _ => by norm_num⟩ (fun t => by rw [hslicez t, one_mul])
  · -- hchart (the interface hypothesis, in `qₑ` terms)
    exact hchart
  · -- hRne (the slice is a.e. nonvanishing)
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    rw [Measure.restrict_univ]
    have hcore : ∀ᵐ w ∂(volume : Measure (Fin (flatDim (fun s => H s - r)) → ℝ)),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm w) ≠ 0 := by
      obtain ⟨A, hA⟩ := dlnLoss_deepest_core_ne_zero_witness (fun s => H s - r) hMpos
      have hP_ne : corePoly (fun s => H s - r) ≠ 0 := by
        intro hP0'; apply hA
        have := eval_corePoly (fun s => H s - r) ((paramsEquivFlat (fun s => H s - r)) A)
        rw [hP0'] at this; simpa using this.symm
      have hae := MvPolynomial.ae_eval_ne_zero (corePoly (fun s => H s - r)) hP_ne
      exact hae.mono fun z hz => by rw [← eval_corePoly (fun s => H s - r) z]; exact hz
    have hprodY : ∀ᵐ w ∂(volume : Measure Y),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm w.1) ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae hcore
    have hae_z := he_mp.quasiMeasurePreserving.ae hprodY
    exact hae_z.mono fun z hz => by rw [hslicez z]; exact hz

end DLNFibre.DLN.RLCT
