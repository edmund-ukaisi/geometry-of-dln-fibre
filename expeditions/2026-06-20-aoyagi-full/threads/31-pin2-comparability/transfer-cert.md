# Transfer certificate — `regStraightenTotalCLM` to a core-reading reg block

Pre-staged paper certificate for the L2-PIN2 repair build (`l2-pin2-fullreg`)'s flagged-hardest piece:
the `regStraightenTotalCLM` invertibility when the reg output `E_full` reads the core slot. **Headline:
the transfer is a SIMPLIFICATION of the existing `_isUnit` lemma, not a new generalization** — the
block-triangular invertibility argument is agnostic to whether the carried (non-reg) slot is the
spectator `S` or the joined `W = C × S`. No new math; the settled facts are staged in build-ready form.

All settled algebra is from thread 31 (`thread.md`); this only re-states it against the exact Lean
objects (`DeepestRegAbsorbIFT.lean`, `DeepestRegSliceFderiv.lean`).

---

## (0) The objects, exactly (current Lean)

- `regInCLM : R →L[ℝ] R × S := (id).prod 0`, i.e. `r ↦ (r, 0)` (`DeepestRegAbsorbIFT.lean:498`).
- `regStraightenTotalCLM (D_E : (R × S) →L[ℝ] R) : (R × (C × S)) →L[ℝ] (R × (C × S))`,
  `δ ↦ (D_E (δ.1, δ.2.2), δ.2.1, δ.2.2)` (`:428`). Reg-out reads `(reg, spec)`; core/spec carried.
- `regStraightenTotalCLM_equiv_of_regBlock_isUnit (D_E) (F : R ≃L[ℝ] R)
   (hF : ↑F = D_E.comp regInCLM) : ∃ e ≃L, ↑e = regStraightenTotalCLM D_E` (`DeepestRegSliceFderiv.lean:616`).
  Proof: linearity `D_E(r,s) = F r + D_E(0,s)`; explicit inverse `(r',(c',s')) ↦
  (F⁻¹(r' − D_E(0,s')), c', s')`. `S` enters ONLY via the carried term `D_E(0, δ.2.2)`.

In the chart `R = (Fin nReg → ℝ)`, `C = (Fin (flatDim (deepestM)) → ℝ)` (core), `S = (Fin nGauge → ℝ)`
(spectator); `F = Fmap` the `regBlockCLE`-built `≃L` (`DeepestGaugeConstruction.lean:742`).

## (1) The generalized shear's total derivative at the origin = `[[F, 0, G],[0,I,0],[0,0,I]]`

The repair's reg output `E_full : R × (C × S) → R` reads ALL slots (`reg, core, spec`); the chart is
`regStraighten q := (E_full q, q.2.1, q.2.2)` (core/spec OUTPUT fixed). Write its derivative at 0 as
`D := fderiv ℝ regStraighten 0`. In block form, rows = (reg-out, core-out, spec-out), columns =
(reg-in, core-in, spec-in):

        D = [[ Dr E_full(0)   Dc E_full(0)   Ds E_full(0) ]      [[ F   0   G ]
             [      0              I             0        ]   =   [ 0   I   0 ]
             [      0              0             I        ]]      [ 0   0   I ]]

- `Dr E_full(0) = F` — PIN1's invertible `regBlockCLE`. (`E_full(·,0,0) = deepestEPivot(·,0)`; the
  reg-slice fderiv is `deepestEPivot_regSlice_fderiv`'s `F`. Thread 31: exact, sympy + Codex.)
- `Dc E_full(0) = 0` — the core-direction block vanishes (the leaks `Y0·T1, T0·Z1` are degree-2;
  `∂E_full/∂T(0) = 0`). Thread 31 + Codex pin1-survival, exact.
- `Ds E_full(0) = G` — the spectator block, possibly nonzero (coordinate-dependent); IRRELEVANT to
  invertibility.
- The core-out / spec-out rows are the literal carries `q.2.1, q.2.2`, derivative `[0,I,0]` / `[0,0,I]`.

(Row/col ordering matches `DeepestSplit = R × (C × S)`: `.1` reg, `.2.1` core, `.2.2` spec — the same
ordering `regStraightenTotalCLM` reads with `fst`, `snd∘snd`, `fst∘snd`, `snd∘snd`.)

## (2) Invertibility — det = det F ≠ 0 by block-triangularity

`D` is block UPPER-triangular with diagonal blocks `(F, I, I)`. Hence `D` is invertible ⟺ `F` is
invertible (the off-diagonal `G` and the zero `Dc` do not affect a triangular determinant / inverse).
`F` is invertible: it is `Fmap`, a `ContinuousLinearEquiv` built by `regBlockCLE` from `IsUnit (Pf
firstLayer)` (= `hPf`, the unit row frame) and `hQf22` (the pivot frame's `B₂₂`-unit block,
`DeepestGaugeConstruction.lean:740`). So `regStraightenTotalCLM`'s generalized form is a genuine `≃L`,
and the IFT/`#72` peel input (`HasStrictFDerivAt regStraighten D 0` with `D` an invertible `≃L`) survives
the `E_zero → E_full` swap. **The headline rlct value is unaffected** — the squeeze becomes the leaf
lemma's true comparability `dlnLoss ≍ Sreg + Score`.

The explicit inverse (matching the existing `_isUnit` shape, with `W := C × S` carried):
`(r', w') ↦ (F⁻¹(r' − D_E(0, w')), w')` where `w' = (c', s')` is carried identically. Verified
`left_inv`/`right_inv` reduce to `F.symm_apply_apply` / `F.apply_symm_apply` + `add_sub_cancel` /
`sub_add_cancel` — IDENTICAL to the existing proof (`:656–663`) with the `(c',s')` pair collapsed to `w'`.

## (3) The clean build target (the one transfer step the formaliser is likeliest to stall on)

Do **NOT** instantiate the existing lemma with `S := C × S` — that inserts a PHANTOM second core slot
`C'` (the def splits `(C × ·)` around its `S`). Instead re-state the straightening with the non-reg slot
**UNSPLIT** as a single `W`. This is STRICTLY SIMPLER than the current lemma (one fewer `Prod` layer):

    -- W := C × S, carried as a single slot.  regInCLM : R →L[ℝ] R × W,  r ↦ (r, 0).
    noncomputable def regStraightenTotalCLM2 (D_E : (R × W) →L[ℝ] R) : (R × W) →L[ℝ] (R × W) :=
      (D_E).prod (ContinuousLinearMap.snd ℝ R W)
      -- δ ↦ (D_E δ, δ.2)

    theorem regStraightenTotalCLM2_equiv_of_regBlock_isUnit
        (D_E : (R × W) →L[ℝ] R) (F : R ≃L[ℝ] R)
        (hF : (F : R →L[ℝ] R) = D_E.comp (regInCLM : R →L[ℝ] R × W)) :
        ∃ e : (R × W) ≃L[ℝ] (R × W),
          (e : (R × W) →L[ℝ] (R × W)) = regStraightenTotalCLM2 D_E := by
      -- D_E (r, w) = F r + D_E (0, w)   (linearity, hF)
      -- explicit inverse:  (r', w') ↦ (F.symm (r' − D_E (0, w')), w')
      -- left/right_inv: exactly the existing _isUnit proof with (c',s') ⟶ w' (one fewer Prod.ext).
      sorry

**Hypotheses the formaliser supplies** (all banked, unchanged): `F := Fmap` (the `regBlockCLE` `≃L`,
from `hPf` + `hQf22`); `hF : ↑F = D_E.comp regInCLM` (the reg-slice fderiv `= F`, from PIN1 + the bridge
`E_full(·, 0) = deepestEPivot(·, 0)` where here `0 : W = (C × S)` is BOTH core-zero and spec-zero); the
core/spec-out carry is `ContinuousLinearMap.snd`, so `regStraighten_core` (`(regStraighten q).2.1 =
q.2.1`) and `regStraighten_spectator` (`.2.2 = q.2.2`) both hold by `δ.2` being carried identically.

**If the formaliser prefers minimal churn** (keep `C`/`S` split in the *type* `DeepestSplit = R×(C×S)`):
the `W`-unsplit `regStraightenTotalCLM2` still applies with `W := C × S`, and the output `(D_E δ, δ.2)`
is DEFEQ to `(D_E δ, δ.2.1, δ.2.2)` — so `regStraighten_core`/`_spectator` are `rfl`. No phantom slot.

## Why this is low-risk

The invertibility argument (block-triangular, `F` unit) is the SAME as the banked `_isUnit` lemma; the
only delta is dropping one `Prod` layer in the carried slot. `F`'s invertibility source (`hPf` +
`hQf22` via `regBlockCLE`) is unchanged from PIN1. The two facts feeding `F = Dr E_full(0)` — the
reg-slice bridge and `Dc E_full(0) = 0` — are exact (thread 31, sympy + decorrelated Codex). No
re-derivation needed; this is the settled math in build-ready shape.
