import DLNFibre.DLN.RLCT.Validate.D1GeChart

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

open Matrix
open scoped Classical
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

/-- **The role-partition index equiv** `RegIdxGen ⊕ (CoreIdxGen ⊕ SpecIdxGen) ≃ FlatIdx H`. The
reg/core half is `regCoreEmbGen`'s range (via `Equiv.ofInjective`), the spec half its complement
(`Equiv.Set.sumCompl`); reassociated by `Equiv.sumAssoc`. -/
noncomputable def roleEquivGen :
    (RegIdxGen H r ⊕ (CoreIdxGen H r ⊕ SpecIdxGen ι hι hL)) ≃ FlatIdx H :=
  (Equiv.sumAssoc (RegIdxGen H r) (CoreIdxGen H r) (SpecIdxGen ι hι hL)).symm.trans
    ((Equiv.sumCongr (Equiv.ofInjective _ (regCoreEmbGen_injective ι hι hL))
        (Equiv.refl (SpecIdxGen ι hι hL))).trans
      (Equiv.Set.sumCompl (Set.range (regCoreEmbGen ι hι hL))))

/-- Core readback: `roleEquivGen (inr (inl c)) = regCoreEmbGen (inr c)`. -/
theorem roleEquivGen_core (c : CoreIdxGen H r) :
    roleEquivGen ι hι hL (Sum.inr (Sum.inl c)) = regCoreEmbGen ι hι hL (Sum.inr c) := by
  simp only [roleEquivGen, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inr_inl,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.ofInjective_apply, Equiv.Set.sumCompl_apply_inl]

/-- Reg readback: `roleEquivGen (inl ρ) = regCoreEmbGen (inl ρ)`. -/
theorem roleEquivGen_reg (ρ : RegIdxGen H r) :
    roleEquivGen ι hι hL (Sum.inl ρ) = regCoreEmbGen ι hι hL (Sum.inl ρ) := by
  simp only [roleEquivGen, Equiv.trans_apply, Equiv.sumAssoc_symm_apply_inl,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.ofInjective_apply, Equiv.Set.sumCompl_apply_inl]

end DLNFibre.DLN.RLCT
