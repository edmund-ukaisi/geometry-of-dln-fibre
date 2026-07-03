# Statement card — general-`L` smeared box supplier: R2 (Field-A `hSpre`) LANDED

**Status:** R2 (the general-`L` Field-A entry bound `hSpre` — the LAST-LOWER-leg blocker flagged by the
`genm-smearbox` card) is discharged **sorry-free**, on `origin/genm-smearR2` (based on
`origin/genm-smearbox @62d046b3`). One new module, axiom footprint `[propext, Classical.choice,
Quot.sound]` (forced `#print axioms`, NO `sorryAx`/`native_decide`/`monomial_rlct`). Module green
(8342 jobs, its full import closure). Aggregator wiring left for the controller.

This CLOSES **Residual 2** of the `genm-smeardata`/`genm-smearbox` cards (the general-`L` Field-A
containment — flagged there as "the blocker for the assembly, ~200 lines").

## `DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareGen.lean` (DLN connector, sorry-free)

The general-`L` analog of the L=2 `RouteMSmearedSquareL2.condBox_subset_preimage`.

### The two hard pieces (both sorry-free)
- **`wideCarrierBound_suffix`** — the shifted `wideCarrierBound_prodAux`: the SEGMENT product
  `Y = A^p·…·A^{k−1}` (from `prodAux_split_exists`'s right-fold) carries a `WideCarrierBound Y r dlb
  nb pub` with the fused invariant (`nb ≤ η·Acc`, `(δ/2)^{k−p} − η·Acc ≤ dlb`). `Nat.le_induction`
  from the identity base (`wideCarrierBound_one`), one `wideCarrier_mul` step per folded `CarrierLayer`.
- **`Lam0uG_entry_bound`** (THE CRUX) — `|Lam0uG u a b| ≤ (1/γ)·nb` on the front-carrier box, off the
  tall-Gram obstruction (decorrelated-Codex route 4). The tall Gram `P₁ᵀP₁` sums over the `M0−r`
  UNCONTROLLED front-product rows, so a direct Varah bound fails; instead route through the width-`r`
  waist: `frontProd = U·V` (`V : r × M⟨L−1⟩`, exactly `r` rows), `Λ₀ = Vρ⁻¹·Vσ` (banked
  `gram_routing_eq_factor` + inline `P₂ = U·Vσ` via `P1uG_eq_mul_Vrho`), `Vρ` `γ`-dominant
  (`waist_carrier_data`), so the Varah `StrictRowDominant.inv_mul_entry_bound` bites with the residual
  column bound `nb`. `|Λ₀ a b| ≤ (1/γ)·nb = O(η)` as `η → 0`.

### The supporting decode + bounds (all sorry-free)
- `paramsEquivFlat_apply_equivFin'` (local copy of the flat decode, avoiding the heavy `DeepestFrameRaw`
  import); `psiMapG_RmapG_flat` — `psiMapG (RmapG u) i = shearMBody … i` (`packM`/`paramsEquivFlat`
  cancel to the shear value at the coord); `coordOfG_slotEquivG` round trip.
- `waist_carrier_data` — extracts `U·V` + `CarrierBound Vρ dlb nb` + `Vσ` uniform bound + the invariant
  from `wideCarrierBound_suffix` at the waist `q` (with the `Fin.cast M⟨q⟩=r` recast, `.val`-preserving).
- `boxGen_abs_le`/`_eta`, `zuG_abs_le_of_box`, `HbarUnitG_abs_le_of_box`, `SbotuG_abs_le_of_box`,
  `topSlotG_not_carrierDiag`/`botSlotG_not_carrierDiag` — the deepest-slot box readoffs (top/bottom
  slots are layer `L−1`, never a `slotBoxGen` carrier-diagonal, so `∈ [−η,η]`).
- `psiMapG_RmapG_topSlotG` (top-slot decode value `= (z•H̄ − Λ₀·S_bot) a j`), `deepTopG_entry_le_of_box`
  (`≤ δ + s·((1/γ)nb)·η`), `psiMapG_RmapG_flat_le` (each flat coord `≤ 2δ`: spectator = box coord `≤ δ`,
  top = deep-top `≤ 2δ` under field-A `s·((1/γ)nb)·η ≤ δ`).

### The `hSpre` output (the box-supplier input)
- **`condBox_subset_preimage_gen`** — `condBox (pivotCoordG) (boxGen) δ ⊆ (ψ∘R)⁻¹(cubeBox 2δ)`, taking
  the `Λ₀` bound `hLam` (fixed `γ, nb`) + field-A margin + `hbotne` as inputs.
- **`hSpre_gen`** — the exact `smearedChartDataGen_of_dets`-shaped `hSpre` (`box₀ = fun j => boxGen (hN
  ▸ j)`, `ε = 2δ`, `hN ▸ p = pivotCoordG`), via the `boxGen_double_cast` collapse.

## Item-123 fidelity (verified)
- The Varah bound is SOUND: `Λ₀ = Vρ⁻¹·Vσ` genuinely (through `gram_routing_eq_factor`, needs the Gram
  `≠ 0`), and `Vρ`'s dominance / `Vσ`'s column bound come from the ALL-ROW `WideCarrierBound V` (V has
  exactly `r` rows, so no uncontrolled-row leak — the obstruction Codex flagged for the tall `P₁ᵀP₁` is
  genuinely routed around). The `.val`/deepWidthEquiv index alignment is machine-checked
  (`finSumFinEquiv_apply_left/right`: `inl k` → col val `k < r`, `inr b` → col val `r+b ≥ r`).
- No fabricated bound: `η→0` limit shown (`|Λ₀| = O(η)`, deep-top shear `= O(η²)`).

## What remains for the fully-unconditional `hSmeared ∀L` (precise gap — NOT built)
The **box-supplier assembly** feeding `smearedChartDataGen_of_dets` → `smearedChartGen` →
`hSmeared_smearedGen` → the unconditional `hSmeared ∀L`. Two substantial pieces remain (both flagged by
smearbox, both beyond a "clean hop"):

1. **Uniform-`u` `hLam` (η* threading against the existential `Acc`).** `Lam0uG_entry_bound` /
   `gram_det_ne_of_carrierLayers` (R1) return `Acc, nb` EXISTENTIALLY per-`u`; `hSpre_gen`/`hSpre`
   need a SINGLE `γ, nb` valid ∀`u` in the box. The constants are in fact `u`-independent (they depend
   only on `M, δ, η, q, widths`), but the current existential packaging hides this. Needs
   `wideCarrierBound_suffix`/`wideCarrierBound_prodAux` refactored to return EXPLICIT closed-form
   `Acc, nb` (smearbox's flagged "(b) pick η* … needs Acc exposed as a closed form OR the existential
   threaded"). Then pick `η*` satisfying BOTH R1's `r·η·Acc_R1 < (δ/2)^{L−1}` (Gram ≠ 0 / carrier) AND
   R2's `(r−1)·nb < (δ/2)^{L−1−q} − η·Acc_R2` (γ > 0) AND field-A `s·((1/γ)nb)·η ≤ δ` — all hold for
   small `η` (each `O(η)` or `O(η²)`), but the two-`Acc` (R1 full-frontProd vs R2 waist-suffix) must be
   maxed over.
2. **The `BoundarySmeared` structural extraction.** Derive from `BoundarySmeared M` (+ `1 ≤ minAdm M`):
   the waist `∃ q ≤ L−1, M⟨q⟩ = deepRank` (NOT banked — a chain-native `tach`/`Text` fact), the width
   bound `∀ t, deepRank ≤ M⟨t⟩` (NOT banked), `hN`/`p`/`hminadm` (`minAdm_eq_deepRank_mul_last` is
   banked), `hbotne`, `s = deepRows − deepRank`. The L=2 `smearedChart_of_square`
   (`RouteMSmearedSquareReduce`) does the analog for `r = M0` (square), sidestepping the waist; the
   general-`L` version needs the genuine waist existence.

The BLOCKER (Residual 2, the general-`L` Field-A `hSpre`) is CLOSED. The remaining assembly is the
existential-`Acc` threading (shared with R1) + the `BoundarySmeared` extraction — a distinct, sizeable
wiring effort, not new analytic content.

## Reusable value banked NOW
`wideCarrierBound_suffix` (a shifted carrier bound reusable for any segment product) and the route-4
`Λ₀`-entry bound (`waist_carrier_data` + `Lam0uG_entry_bound`) — a network-free-flavoured, axiom-clean
Field-A entry bound for the smeared chart at ANY depth, GIVEN the front-carrier box + Gram det. Combined
with smearbox's R1, the general-`L` box supplier's ANALYTIC content (both dets + the Field-A containment)
is now fully discharged; only the structural/threading assembly remains.
