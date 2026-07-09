import DLNFibre.DLN.RLCT.Validate.D1GeChart
import DLNFibre.DLN.RLCT.Validate.D1GeBlockModel
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
`paramsEquivFlat_symm_splitMP_core`, but the general-`L` layer split needs no `Fin.cases`. -/

/-- General-`L` `paramsEquivFlatLinear.symm` agrees with `paramsEquivFlat.symm` as a function
(the L = 2 `paramsEquivFlatLinear_symm_coe`, lifted to `Fin (L+1)`). -/
theorem paramsEquivFlatLinear_symm_coe_gen (H : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatLinear H).symm = ⇑(paramsEquivFlat H).symm := by
  funext x; apply (paramsEquivFlat H).injective
  rw [(paramsEquivFlat H).apply_symm_apply]
  have hcoe : (paramsEquivFlat H) ((paramsEquivFlatLinear H).symm x)
      = (paramsEquivFlatLinear H) ((paramsEquivFlatLinear H).symm x) := by
    rw [paramsEquivFlatLinear_coe]
  rw [hcoe, (paramsEquivFlatLinear H).apply_symm_apply]

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

end DLNFibre.DLN.RLCT
