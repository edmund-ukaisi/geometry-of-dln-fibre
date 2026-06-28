import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction
import DLNFibre.DLN.RLCT.Validate.DeepestLeadingBlock

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2` — the L=2 gauge-slice diffeo bridge

The content of `deepest_diffeo_bridge_L2` (the `DeepestGaugeConstruction.lean:2915` bare `sorry`),
built as the standalone, independently-`#print axioms`-verifiable `deepest_diffeo_bridge_L2_impl`.
The controller wires the 2915 site to `exact … _impl …` (single-writer producer).

Builds from the g146 design certs (`threads/31-pin2-comparability/h2-diffeo-bridge-cert.md`,
`h2-joint-psi-cert.md`, both sympy/numpy-verified ~1e-17, Codex-reviewed). The joint `(T1,Y1)` Ψ:

    K   := Z1 · ⅟P00 · Y0
    W   := I_{M1} + Z1·A1⁻¹·A0⁻¹·Y0
    S1  := T1 − Z1·A1⁻¹·Y1
    T1' := W⁻¹·[ (I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1 ]
    Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')

E2 reg-preservation (`P01' = P01`) is the exact `A0·A0⁻¹ = I` cancel — `[Invertible A0]` from
`deepestPoint_leadingBlock_isUnit` / the regular-block invertibility. The bridge feeds the banked
abstract `rlctAtOn_comp_localDiffeo` + `rlctAtOn_germ_local`.

**SKELETON STAGE (this commit):** `psiRawL2`/`psiL2` defs + 6 sub-lemma signatures + the FINAL
assembly, every body `sorry`. Typechecks against the banked `rlctAtOn_comp_localDiffeo` interface.
Fill order (light-first): S3 fixpoint, S5 E2, S4 fderiv, S2 contDiff [heaviest], S6 comp-identity,
FINAL. Each soundness sub-lemma diff goes to the controller before commit.

NOTE the sub-lemma signatures below are the SHAPES; on filling I confirm the exact `DeepestSplit`
slot-encoding (via `DeepestPsiLens`) and may refine the intermediate forms — the FINAL `_impl`
signature is FIXED (matches `deepest_diffeo_bridge_L2`).
-/

open MeasureTheory Topology
open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## S0 — the joint `(T1, Y1)` action on `DeepestSplit`, its cutoff, and the flat conjugation

The split coordinates `q : DeepestSplit H r (deepestNGauge H r) = Reg × (Core × Spec)` decode to the
per-layer reads: the gauge blocks `readX/readY/readZ (q.1, q.2.2) s` (off `regGaugeSlotEquiv`) and the
per-layer cores `(paramsEquivFlat (deepestM H r)).symm q.2.1 s`. The joint Ψ edits ONLY the last-layer
core block (`T1`) and the last-layer `Y`-read (`Y1`); everything else is fixed.

The certified closed form (`h2-diffeo-bridge-cert.md`, `h2-joint-psi-cert.md`, verified ~1e-17), with
`A_s = 1 + readX s`, all reads `0` at the split origin:

    K   := Z1 · ⅟P00 · Y0           (P00 = A0·A1 + Y0·Z1, the full-product (1,1) block; here we use
                                     the Mathlib inverse `Inv.inv` = nonsing_inv, `0` off-units)
    W   := I + Z1·A1⁻¹·A0⁻¹·Y0
    S1  := T1 − Z1·A1⁻¹·Y1
    T1' := W⁻¹·[ (I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1 ]
    Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')

The raw map is rational (poles where a denominator det vanishes); the global self-map cuts the
*correction* `psiSplitRawL2 q − q` off by a `ContDiffBump` whose support sits in the unit locus
(Codex-confirmed shape: `q + χ q • (raw q − q)`). The flat Ψ is the affine-chart conjugate
`split⁻¹ ∘ Ψ_split ∘ split`. -/

/-- The base point `wstar` in flat coordinates (the deepest point's flat image). -/
noncomputable def wstarL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : Fin (flatDim H) → ℝ :=
  (paramsEquivFlat H) (deepestPoint H r B hB hr hL)

/-- The last-layer core block `T1` read off the core slot `q.2.1` (the block the joint Ψ edits). -/
noncomputable def coreLast (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  (paramsEquivFlat (deepestM H r)).symm q.2.1 (lastLayer hL)

/-- **The mid-interface width bridge** (the `L = 2` coincidence). At `L = 2` the FIRST layer's
`.succ`-interface (`(0 : Fin 2).succ`) and the LAST layer's `.castSucc`-interface
(`(lastLayer hL).castSucc`) are the SAME middle interface, so the reduced widths agree: `H ((0 : Fin L).succ)
− r = H ((lastLayer hL).castSucc) − r`. (FALSE for `L ≥ 3` — there the first/last layers do not share an
interface; this is why the joint `(T1, Y1)` action is `L = 2`-specific.) -/
theorem midWidth_eq_of_L2 (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) (hL2eq : L = 2) :
    H ((⟨0, by omega⟩ : Fin L).succ) - r = H ((lastLayer hL).castSucc) - r := by
  subst hL2eq; congr 1

/-- **The certified joint `(T1, Y1)` action at `L = 2`** (the real closed form, under `hL2eq : L = 2`).
With `A_s = 1 + readX s`, `Y0 = readY 0` (cols bridged to the middle interface by `midWidth_eq_of_L2`),
`Z1 = readZ (lastLayer)`, `Y1 = readY (lastLayer)`, `T1 = coreLast`, `P00 = A0·A1 + Y0·Z1`:

    K   := Z1·P00⁻¹·Y0 ;  W := I + Z1·A1⁻¹·A0⁻¹·Y0 ;  S1 := T1 − Z1·A1⁻¹·Y1
    T1' := W⁻¹·[(I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1] ;  Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')

The core slot is re-encoded by `paramsEquivFlat`-`Function.update` at `lastLayer` ↦ `T1'`; the reg/spec
slots by `regGaugeSlotEquiv.symm` of the `RegGaugeIdx → ℝ` function editing the last-layer `Y`-tags ↦
`Y1'`. Matrix inverses are the Mathlib `Inv.inv` (= `nonsing_inv`, `0` off-units); the rational poles are
cut off in `psiSplitCutL2`. -/
noncomputable def psiSplitRawL2Core (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  let p := (q.1, q.2.2)
  let A0 : Matrix (Fin r) (Fin r) ℝ := 1 + readX H r hr hL p (⟨0, by omega⟩ : Fin L)
  let A1 : Matrix (Fin r) (Fin r) ℝ := 1 + readX H r hr hL p (lastLayer hL)
  let Y0 : Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
    Matrix.reindex (Equiv.refl (Fin r)) (finCongr (midWidth_eq_of_L2 H r hL hL2eq))
      (readY H r hr hL p (⟨0, by omega⟩ : Fin L))
  let Z1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin r) ℝ :=
    readZ H r hr hL p (lastLayer hL)
  let Y1 : Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
    readY H r hr hL p (lastLayer hL)
  let T1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ := coreLast H r hL q
  let P00 : Matrix (Fin r) (Fin r) ℝ := A0 * A1 + Y0 * Z1
  let K := Z1 * P00⁻¹ * Y0
  let W := 1 + Z1 * A1⁻¹ * A0⁻¹ * Y0
  let S1 := T1 - Z1 * A1⁻¹ * Y1
  let T1' : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
    W⁻¹ * ((1 - K) * S1 + Z1 * A1⁻¹ * Y1 + Z1 * A1⁻¹ * A0⁻¹ * Y0 * T1)
  let Y1' : Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
    Y1 + A0⁻¹ * Y0 * (T1 - T1')
  let core' : Fin (flatDim (deepestM H r)) → ℝ :=
    paramsEquivFlat (deepestM H r)
      (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1) (lastLayer hL) T1')
  let g : RegGaugeIdx H r → ℝ := regGaugeSlotEquiv H r hr hL p
  let g' : RegGaugeIdx H r → ℝ := fun idx =>
    match idx with
    | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
        if h : s = lastLayer hL then Y1' i (h ▸ j) else g idx
    | _ => g idx
  let regspec' := (regGaugeSlotEquiv H r hr hL).symm g'
  (regspec'.1, (core', regspec'.2))

/-- The raw joint `(T1, Y1)` action on `DeepestSplit`. At `L = 2` it is the certified closed form
`psiSplitRawL2Core`; for `L ≠ 2` it is the identity (the bridge fires only at `L = 2`, the only depth
where the joint action's mid-interface widths coincide — `midWidth_eq_of_L2`). Keeps the public
signature `L`-generic (the diffeo-side lemmas case-split on `L = 2`). -/
noncomputable def psiSplitRawL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  if h : L = 2 then psiSplitRawL2Core H r hr hL h q else q

/-- The joint-action correction `Ψ_split q − q` (Codex's correction-cutoff datum). -/
noncomputable def psiSplitDeltaL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  psiSplitRawL2 H r hr hL q - q

/-- **S0 — the raw joint `(T1,Y1)` Ψ on flat coordinates.** `split⁻¹ ∘ Ψ_split ∘ split`. -/
noncomputable def psiRawL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
  fun w => (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm
    (psiSplitRawL2 H r hr hL (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w))

/-- A fresh `ContDiffBump` at `0` on the FULL split `DeepestSplit` (Codex's "do not reuse the reg/spec
bump as a full-split bump"). Its inner/outer radii are `unitRadius/4`, `unitRadius/2` — the same
positive radii as the reg/spec `cutoffBump`, so its support sits inside the unit locus pulled back
through the reg/spec projection (the per-layer `1 + readX_s` invertibility). The composite `W`/`P00`
det conditions are `1` at `0` too, so shrinking the radius if needed keeps the support in the joint
unit locus; the chosen radius suffices once `psiSplitRawL2` is filled (the raw correction is `ContDiffAt`
on that support). -/
noncomputable def cutoffBumpSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)) where
  rIn := unitRadius H r hr hL / 4
  rOut := unitRadius H r hr hL / 2
  rIn_pos := by have := unitRadius_pos H r hr hL; linarith
  rIn_lt_rOut := by have := unitRadius_pos H r hr hL; linarith

/-- The χ-cutoff joint action on `DeepestSplit`: `q + χ q • (psiSplitRawL2 q − q)`. The bump `χ`
(`cutoffBumpSplit`, a fresh `ContDiffBump` at `0` on `DeepestSplit` whose support sits in the unit
locus pulled back through the reg/spec projection) makes the correction globally `ContDiff` and `= 1`
near `0` (so it is the honest raw map there). -/
noncomputable def psiSplitCutL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)))
    (q : DeepestSplit H r (deepestNGauge H r)) : DeepestSplit H r (deepestNGauge H r) :=
  q + (χ q : ℝ) • psiSplitDeltaL2 H r hr hL q

/-- **S1 — the χ-cutoff Ψ on flat coordinates.** `split⁻¹ ∘ psiSplitCutL2 ∘ split`. Since the
skeleton's `psiSplitRawL2` is the placeholder `id`, the correction is `0` and `psiL2 = id` for now;
the body shape is fixed so the diffeo-side lemmas (S2/S3/S4) and FINAL wire against the real map once
`psiSplitRawL2` is filled. -/
noncomputable def psiL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
  fun w => (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm
    (psiSplitCutL2 H r hr hL (cutoffBumpSplit H r hr hL)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w))

/-- **`paramsEquivFlat.symm` sends the zero flat-core to the zero core tuple.** -/
theorem paramsEquivFlat_symm_zero (M : Fin (L + 1) → ℕ) :
    (paramsEquivFlat M).symm (0 : Fin (flatDim M) → ℝ) = (fun _ => 0 : Params M) := by
  have h0 : (paramsEquivFlat M) (fun _ => 0 : Params M) = (0 : Fin (flatDim M) → ℝ) := by
    funext i; rfl
  rw [← h0, (paramsEquivFlat M).symm_apply_apply]

/-- **The certified joint action fixes the split origin.** At `q = 0` every read vanishes
(`readX/Y/Z_zero`) and the core slot is `0`, so `Z1 = Y0 = Y1 = T1 = 0`, hence `T1' = 0` (every bracket
term carries a `Z1` or is `(1−K)·0`) and `Y1' = 0` (carries `Y0`); the core re-encode updates `lastLayer`
to the already-`0` block and the `Y`-re-encode edits the already-`0` tags, so both collapse to `0`. -/
theorem psiSplitRawL2Core_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    psiSplitRawL2Core H r hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  have hp : ((0 : DeepestSplit H r (deepestNGauge H r)).1,
      (0 : DeepestSplit H r (deepestNGauge H r)).2.2)
      = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) := rfl
  -- The core slot decodes to the zero tuple; `coreLast 0 = 0`.
  have hcore0 : ((0 : DeepestSplit H r (deepestNGauge H r)).2.1) = 0 := rfl
  have hcoreLast : coreLast H r hL (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    rw [coreLast, hcore0, paramsEquivFlat_symm_zero]
  unfold psiSplitRawL2Core
  simp only [hp, hcore0, readX_zero H r hr hL, readY_zero H r hr hL, readZ_zero H r hr hL,
    hcoreLast, Matrix.reindex_apply, Matrix.submatrix_zero, Matrix.zero_apply,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, zero_sub, add_zero, zero_add,
    mul_zero, neg_zero]
  -- After read-zero: T1' = W⁻¹·0 = 0, Y1' = 0; the re-encodes return the zero slots.
  -- The edited `RegGaugeIdx → ℝ` function is `0` (both `if`-branches give `regGaugeSlotEquiv 0 = 0`).
  have hgz : regGaugeSlotEquiv H r hr hL (0 : (Fin (deepestNReg H r) → ℝ)
      × (Fin (deepestNGauge H r) → ℝ)) = 0 := regGaugeSlotEquiv_zero H r hr hL
  have hgfun : (fun idx : RegGaugeIdx H r =>
      match idx with
      | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
          if _h : s = lastLayer hL then (0 : ℝ) else regGaugeSlotEquiv H r hr hL 0 idx
      | _ => regGaugeSlotEquiv H r hr hL 0 idx) = 0 := by
    funext idx
    obtain ⟨s, rest⟩ := idx
    rcases rest with (rest | rest)
    · rcases rest with rest | ⟨i, j⟩
      · simp only [hgz, Pi.zero_apply]
      · by_cases h : s = lastLayer hL
        · simp only [dif_pos h, Pi.zero_apply]
        · simp only [dif_neg h, hgz, Pi.zero_apply]
    · simp only [hgz, Pi.zero_apply]
  rw [hgfun]
  -- `regGaugeSlotEquiv.symm 0 = 0`, `Function.update (symm 0) _ 0 = symm 0`, `paramsEquivFlat 0 = 0`.
  have hsymmz : (regGaugeSlotEquiv H r hr hL).symm (0 : RegGaugeIdx H r → ℝ)
      = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) := by
    rw [← hgz, (regGaugeSlotEquiv H r hr hL).symm_apply_apply]
  have hupd : Function.update ((paramsEquivFlat (deepestM H r)).symm
      (0 : Fin (flatDim (deepestM H r)) → ℝ)) (lastLayer hL) 0
      = (paramsEquivFlat (deepestM H r)).symm 0 := by
    rw [paramsEquivFlat_symm_zero]; funext s; rcases eq_or_ne s (lastLayer hL) with h | h
    · subst h; rw [Function.update_self]
    · rw [Function.update_of_ne h]
  rw [hupd, hsymmz]
  have hpz : (paramsEquivFlat (deepestM H r)) ((paramsEquivFlat (deepestM H r)).symm 0) = 0 :=
    (paramsEquivFlat (deepestM H r)).apply_symm_apply 0
  rw [hpz]
  rfl

/-- **The raw joint action fixes the split origin** (`psiSplitRawL2 0 = 0`): at `L = 2` the certified
action fixes it (`psiSplitRawL2Core_zero`); for `L ≠ 2` it is the identity. -/
theorem psiSplitRawL2_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    psiSplitRawL2 H r hr hL (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  unfold psiSplitRawL2
  by_cases h : L = 2
  · rw [dif_pos h]; exact psiSplitRawL2Core_zero H r hr hL h
  · rw [dif_neg h]

/-- **The joint-action correction vanishes at the split origin** (`psiSplitDeltaL2 0 = 0`). -/
theorem psiSplitDeltaL2_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    psiSplitDeltaL2 H r hr hL (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  rw [psiSplitDeltaL2, psiSplitRawL2_zero H r hr hL, sub_zero]

/-- **The χ-cutoff joint action fixes the split origin** (`psiSplitCutL2 χ 0 = 0`): the correction
`psiSplitDeltaL2 0 = 0`, so `0 + χ(0) • 0 = 0`. -/
theorem psiSplitCutL2_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r))) :
    psiSplitCutL2 H r hr hL χ (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
  simp only [psiSplitCutL2, psiSplitDeltaL2_zero H r hr hL, smul_zero, add_zero]

/-- **S3 — fixpoint.** `psiL2 wstar = wstar` (at `wstar` all reads → 0 ⟹ the correction vanishes;
χ(wstar)=1). Light. -/
theorem psiL2_fixpoint (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    psiL2 H r B hB hr hL J Pf Qf wstar = wstar := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  have hbase : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar = 0 := by
    rw [hwstar']
    exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  simp only [psiL2, hbase, psiSplitCutL2_zero H r hr hL]
  rw [← hbase, (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm_apply_apply]

/-- **The joint-action correction is `ContDiffAt ⊤` on the cutoff support.** The raw map's blocks
`W⁻¹`, `⅟P00`, `A_s⁻¹` are smooth where their determinants are nonzero — and the cutoff support sits
in that unit locus (`cutoffBumpSplit`'s `tsupport ⊆ {dets ≠ 0}`). So the correction `δ = psiSplitRawL2
− id` is `ContDiffAt ⊤` on `tsupport (cutoffBumpSplit)`. (Skeleton placeholder `psiSplitRawL2 = id`
makes `δ = 0`, `ContDiffAt` by `contDiffAt_const`; once the closed form is filled, this consumes the banked
`contDiffAt_matrix_inv_entry_of_det_ne_zero` + `contDiffAt_matrix_mul_entry` +
`contDiffAt_inv_one_add_readX_entry` on the composite/product-pivot inverses.) -/
theorem contDiffAt_psiSplitDeltaL2_of_mem_tsupport (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r))
    (_hq : q ∈ tsupport (fun y => ((cutoffBumpSplit H r hr hL) y : ℝ))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psiSplitDeltaL2 H r hr hL) q := by
  rcases eq_or_ne L 2 with hL2 | hL2
  · -- **L = 2: the real composite-inverse ContDiff (the heaviest leaf — NOT yet built).** The
    -- correction `δ = psiSplitRawL2Core − id` carries `W⁻¹`, `P00⁻¹`, `A_s⁻¹`, smooth on the unit locus
    -- (`tsupport (cutoffBumpSplit) ⊆ {dets ≠ 0}`), via the banked
    -- `contDiffAt_matrix_inv_entry_of_det_ne_zero` + `contDiffAt_matrix_mul_entry` +
    -- `contDiffAt_inv_one_add_readX_entry` through the encode/decode + reindex casts. Genuine S2.
    sorry
  · -- L ≠ 2: `psiSplitRawL2 = id`, so `δ = id − id = 0`, `ContDiffAt` by `contDiffAt_const`.
    have heq : psiSplitDeltaL2 H r hr hL
        = fun _ : DeepestSplit H r (deepestNGauge H r) =>
            (0 : DeepestSplit H r (deepestNGauge H r)) := by
      funext q'; simp only [psiSplitDeltaL2, psiSplitRawL2, dif_neg hL2, sub_self]
    rw [heq]; exact contDiffAt_const

/-- **The χ-cutoff joint action is globally `ContDiff ⊤`.** `psiSplitCutL2 χ q = q + (χ q) • δ q`; the
`q` term is `ContDiff`, the correction `χ • δ` is `ContDiff` via the banked `contDiff_contDiffBump_smul`
(its raw `δ` is `ContDiffAt` on `tsupport χ`, off-support the bump vanishes locally). -/
theorem contDiff_psiSplitCutL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞)
      (psiSplitCutL2 H r hr hL (cutoffBumpSplit H r hr hL)) := by
  have hcorr : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => ((cutoffBumpSplit H r hr hL) q : ℝ) • psiSplitDeltaL2 H r hr hL q) :=
    contDiff_contDiffBump_smul (cutoffBumpSplit H r hr hL) (psiSplitDeltaL2 H r hr hL)
      (fun x hx => contDiffAt_psiSplitDeltaL2_of_mem_tsupport H r hr hL x hx)
  have heq : psiSplitCutL2 H r hr hL (cutoffBumpSplit H r hr hL)
      = fun q => q + ((cutoffBumpSplit H r hr hL) q : ℝ) • psiSplitDeltaL2 H r hr hL q := rfl
  rw [heq]
  exact contDiff_id.add hcorr

/-- **S2 — global smoothness.** `psiL2` is `ContDiff ℝ ⊤` (the two NEW composite-inverse smoothness
lemmas `W⁻¹`, `⅟P00` on `U_inv` via `contDiffAt_matrix_inv_entry_of_det_ne_zero` + the banked
per-layer `(1+X)⁻¹`, then the χ-cutoff to global; `split` smoothness from `contDiff_deepestSplit`).
HEAVIEST sub-lemma. Proof: `psiL2 = split⁻¹ ∘ psiSplitCutL2 ∘ split`, all three `ContDiff ⊤`. -/
theorem psiL2_contDiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (psiL2 H r B hB hr hL J Pf Qf) := by
  have heq : psiL2 H r B hB hr hL J Pf Qf
      = fun w => (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).symm
          (psiSplitCutL2 H r hr hL (cutoffBumpSplit H r hr hL)
            (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w)) := rfl
  rw [heq]
  exact (contDiff_deepestSplit_symm H r hr hL (wstarL2 H r B hB hr hL)).comp
    ((contDiff_psiSplitCutL2 H r hr hL).comp
      (contDiff_deepestSplit H r hr hL (wstarL2 H r B hB hr hL)))

/-- **The joint-action correction has vanishing strict derivative at the split origin.** The
`(T1,Y1)` correction `psiSplitRawL2 q − q` is `O(read³)` (each delta block is a product with at least
two vanishing factors — `K = O(read²)`, `S1 = O(read)`, `W − I = O(read²)`), so its strict derivative
at `0` is `0`. (Skeleton placeholder `psiSplitRawL2 = id` makes the delta `0` with derivative `0`
directly; once filled, this is the certified higher-order vanishing — proven componentwise by the
product rule, NOT from the reads (which are linear, derivative ≠ 0).) -/
theorem hasStrictFDerivAt_psiSplitDeltaL2_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (psiSplitDeltaL2 H r hr hL)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
  rcases eq_or_ne L 2 with hL2 | hL2
  · -- **L = 2: the real O(read³) deriv-vanishing (the genuine S4 leaf — NOT yet built).** Each
    -- correction block (`T1'−T1`, `Y1'−Y1`) is a sum of products with ≥ 2 vanishing-at-`0` read
    -- factors (`K = O(read²)`, `S1 = O(read)`, `W−I = O(read²)`), so `D(δ)(0) = 0` — componentwise
    -- product rule through the encode/decode + reindex casts (NOT from the reads, which are linear).
    sorry
  · -- L ≠ 2: `psiSplitRawL2 = id`, so `δ = 0`, strict deriv `0` by `hasStrictFDerivAt_const`.
    have heq : psiSplitDeltaL2 H r hr hL
        = fun _ : DeepestSplit H r (deepestNGauge H r) =>
            (0 : DeepestSplit H r (deepestNGauge H r)) := by
      funext q; simp only [psiSplitDeltaL2, psiSplitRawL2, dif_neg hL2, sub_self]
    rw [heq]; exact hasStrictFDerivAt_const _ _

/-- **The χ-cutoff joint action has strict derivative `id` at the split origin.** `psiSplitCutL2 χ q =
q + (χ q) • (psiSplitRawL2 q − q)`; the first term's derivative is `id`, the correction's is `0`
(the scalar–vector product rule: `χ(0) • Dδ(0) + (Dχ(0)) • δ(0)`, and `δ(0) = 0` kills the second
term, `Dδ(0) = 0` the first). Mirrors `hasStrictFDerivAt_coreShearHomeo_symm_zero` (deriv `id` when
the shift's deriv vanishes). -/
theorem hasStrictFDerivAt_psiSplitCutL2_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (χ : ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r))) :
    HasStrictFDerivAt (psiSplitCutL2 H r hr hL χ)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
  -- The correction `q ↦ (χ q) • δ q` has strict deriv 0 at 0: scalar `χ` smooth, `δ 0 = 0`, `Dδ 0 = 0`.
  have hχ : HasStrictFDerivAt (fun q => (χ q : ℝ))
      (fderiv ℝ (fun q => (χ q : ℝ)) 0) (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (χ.contDiff (n := (1 : ℕ∞))).hasStrictFDerivAt (by norm_num)
  have hδ := hasStrictFDerivAt_psiSplitDeltaL2_zero H r hr hL
  have hδ0 : psiSplitDeltaL2 H r hr hL (0 : DeepestSplit H r (deepestNGauge H r)) = 0 :=
    psiSplitDeltaL2_zero H r hr hL
  -- The smul product `χ • δ` has strict deriv `χ(0)•0 + (Dχ 0).smulRight (δ 0) = 0`.
  have hsmul := hχ.smul hδ
  rw [hδ0] at hsmul
  simp only [smul_zero, ContinuousLinearMap.smulRight_zero, add_zero] at hsmul
  -- `psiSplitCutL2 χ = id + (χ • δ)`; deriv = id + 0 = id.
  have hid : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) => q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 :=
    hasStrictFDerivAt_id 0
  have hsum := hid.add hsmul
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq (by filter_upwards with q; rfl)

/-- **S4 — strict derivative = identity at `wstar`.** The `(T1,Y1)` correction is `O(read³)` ⟹
`D(psiRawL2 − id)(wstar) = 0`; χ=1 near `wstar`; `split` deriv `≃L` conjugates to id. Mirror
`hasStrictFDerivAt_coreShearHomeo_symm_zero` + `hasStrictFDerivAt_deepestSplit`. Proof: `psiL2 =
split⁻¹ ∘ psiSplitCutL2 ∘ split`; chain-rule the strict derivatives — `deepestSplitCLE` at `wstar`,
`id` at the origin (`hasStrictFDerivAt_psiSplitCutL2_zero`, via `split wstar = 0`), `deepestSplitCLE⁻¹`
at the origin — and the composite `deepestSplitCLE⁻¹ ∘ id ∘ deepestSplitCLE = id`. -/
theorem psiL2_hasStrictFDerivAt (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    HasStrictFDerivAt (psiL2 H r B hB hr hL J Pf Qf)
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) wstar := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  have hbase : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar = 0 := by
    rw [hwstar']; exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  -- `split` strict deriv at `wstar`.
  have hsplit := hasStrictFDerivAt_deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar
  -- `psiSplitCutL2` strict deriv `id` at `split wstar = 0`.
  have hcut0 := hasStrictFDerivAt_psiSplitCutL2_zero H r hr hL (cutoffBumpSplit H r hr hL)
  have hcut : HasStrictFDerivAt (psiSplitCutL2 H r hr hL (cutoffBumpSplit H r hr hL))
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar) := by rw [hbase]; exact hcut0
  -- `split.symm` strict deriv at `psiSplitCutL2 (split wstar) = 0`.
  have hsymm := hasStrictFDerivAt_deepestSplit_symm H r hr hL (wstarL2 H r B hB hr hL)
    (psiSplitCutL2 H r hr hL (cutoffBumpSplit H r hr hL)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar))
  -- Compose: `split.symm ∘ psiSplitCutL2 ∘ split`.
  have hcomp := (hsymm.comp wstar (hcut.comp wstar hsplit))
  -- The composed derivative simplifies to `id`.
  refine hcomp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact (deepestSplitCLE H r hr hL).symm_apply_apply w

/-- **Near `wstar` the cutoff Ψ equals the honest raw Ψ** (the χ = 1 germ reduction). `split` is
continuous with `split wstar = 0`, and `χ = cutoffBumpSplit` is `= 1` near `0`, so on a neighbourhood
of `wstar` the cutoff `psiSplitCutL2 χ (split w) = split w + 1 • (psiSplitRawL2 (split w) − split w)
= psiSplitRawL2 (split w)`, hence `psiL2 w = psiRawL2 w`. The germ-locality step `comp_identity_L2`
stands on (it lets the LDU composition identity be proved against the honest rational Ψ, not the
cutoff). -/
theorem psiL2_eventuallyEq_psiRawL2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL)) :
    psiL2 H r B hB hr hL J Pf Qf =ᶠ[nhds wstar] psiRawL2 H r B hB hr hL J Pf Qf := by
  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  have hbase : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) wstar = 0 := by
    rw [hwstar']; exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  -- `χ = 1` near `0`, pulled back along the continuous `split` (sends `wstar ↦ 0`).
  have hχ1 : (fun w => ((cutoffBumpSplit H r hr hL)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w) : ℝ)) =ᶠ[nhds wstar] 1 := by
    have hcont : ContinuousAt (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)) wstar :=
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).continuous.continuousAt
    have htend : Filter.Tendsto (deepestSplit H r hr hL (wstarL2 H r B hB hr hL))
        (nhds wstar) (nhds 0) := by rw [← hbase]; exact hcont
    exact htend.eventually ((cutoffBumpSplit H r hr hL).eventuallyEq_one)
  filter_upwards [hχ1] with w hw
  simp only [psiL2, psiRawL2, psiSplitCutL2, psiSplitDeltaL2]
  have hw' : ((cutoffBumpSplit H r hr hL)
      (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) w) : ℝ) = 1 := hw
  rw [hw', one_smul, add_sub_cancel]

/-! ## S5 — E2 reg-preservation (frame-free matrix keystone)

The joint Ψ moves `(T1, Y1) ↦ (T1', Y1')` with `Y1' = Y1 + A0⁻¹·Y0·(T1 − T1')`. The `P01` block of
the framed product is `A0·Y1 + Y0·T1`; the keystone (cert `h2-joint-psi-cert.md`, sympy-verified) is
that the `Y1'`-definition is PRECISELY the E2 solution holding `P01` fixed:

    P01' − P01 = A0·(Y1' − Y1) + Y0·(T1' − T1)
               = A0·(A0⁻¹·Y0·(T1 − T1')) + Y0·(T1' − T1)
               = Y0·(T1 − T1') + Y0·(T1' − T1)        [A0·A0⁻¹ = I]
               = 0.

Frame-free (over `Invertible A0`); `P00 = A0·A1 + Y0·Z1` and `P10 = Z0·A1 + T0·Z1` are `T1, Y1`-free
so fixed automatically. This is the matrix core the eventual `comp_identity_L2` reg-term consumes. -/

/-- **E2 reg-preservation (`P01` fixed).** For any `Invertible A0`, the new last-layer reg block
`Y1' = Y1 + ⅟A0·Y0·(T1 − T1')` keeps `A0·Y1' + Y0·T1' = A0·Y1 + Y0·T1` — the `P01` block of the
framed product is fixed under the joint `(T1, Y1)` move, for any `T1'`. The `A0·⅟A0 = I` cancel. -/
theorem e2_regPreserve {p1 p2 q1 : Type*} [Fintype p1] [Fintype q1] [DecidableEq q1]
    (A0 : Matrix q1 q1 ℝ) [Invertible A0] (Y0 : Matrix q1 p1 ℝ)
    (Y1 : Matrix q1 p2 ℝ) (T1 T1' : Matrix p1 p2 ℝ) :
    A0 * (Y1 + ⅟A0 * Y0 * (T1 - T1')) + Y0 * T1' = A0 * Y1 + Y0 * T1 := by
  have hcancel : A0 * (⅟A0 * Y0 * (T1 - T1')) = Y0 * (T1 - T1') := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  rw [Matrix.mul_add, hcancel, Matrix.mul_sub]
  -- `A0·Y1 + (Y0·T1 − Y0·T1') + Y0·T1' = A0·Y1 + Y0·T1`.
  rw [add_assoc, sub_add_cancel]

/-- **S6 — the eventual composition identity** `Φcore ∘ psiL2 =ᶠ[𝓝 wstar] Φscore`. The genuine
geometric content of the bridge: near `wstar` the cutoff χ = 1 so `psiL2` is the honest joint Ψ; the
reg term is fixed by E2 reg-preservation (`P00, P10` are `T1,Y1`-free, `P01' = P01` by the
`A0·A0⁻¹ = I` cancel — `e2_regPreserve`), and the core term satisfies `coreΦ ∘ Ψ = Score` by the LDU
`Rcore = S0·(I−K)·S1` (`deepestCoreF_coreAbsorb_eq_prodSchur` + the banked
`rcore_schur_factor_of_corner_split`, the `prod_absorbed_eq_rcore` energy chain in
`DeepestCompositionE1`). **GATED on filling `psiSplitRawL2` with the certified `W⁻¹·[…]` joint action
(the skeleton placeholder is `id`); both `e2_regPreserve` and the E1 LDU chain depend on the real
edit.** Stated here (correct shape) as the wiring point; the placeholder map makes it `Φcore = Φscore`
only when `Score = coreΦ ∘ coreAbsorb ∘ split` — which is exactly the real identity, NOT provable from
the `id` placeholder. The `hPtri`/`hQtri` triangularity hypotheses feed the framed-product reg read. -/
theorem comp_identity_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hScoreDef : Score = fun w => ∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
            * endpointQL H hL Qf)).toBlocks₂₂
        - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
              * endpointQL H hL Qf)).toBlocks₂₁
          * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
          * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₂) i j) ^ 2)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL))
    (hL2eq : L = 2) :
    (fun x : Fin (flatDim H) → ℝ =>
        (∑ i, (regStraighten (split x)).1 i ^ 2)
          + deepestCoreF H r (coreAbsorb (split x)).2.1) ∘ (psiL2 H r B hB hr hL J Pf Qf)
      =ᶠ[nhds wstar] Φscore := by
  sorry

/-- **FINAL — the L=2 diffeo bridge** (the content of `deepest_diffeo_bridge_L2`). Signature is
`DeepestGaugeConstruction.lean:2853` PLUS the two triangularity hypotheses `hPtri`/`hQtri` (the
soundness amendment — the verbatim-2853 sig is unsound, E2 false at general frames). The R-param
producer edit lifts THIS (sound) conclusion; the `_L2` caller supplies the triangularity proofs.
Assembles via the banked abstract bridge `rlctAtOn_diffeo_bridge_of`: S6 comp-identity (germ) +
S2 (ContDiff) + S4 (fderiv) + S3 (fixpoint). -/
theorem deepest_diffeo_bridge_L2_impl (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    -- **TRIANGULARITY (soundness, Codex-confirmed E2 wall, consult `e2-frame-soundness`).** The
    -- framed product `P = endpointP0·(prod−B)·endpointQL = (Pf 0)·(prod−B)·(Qf last)` reads its reg
    -- blocks through the GENERIC endpoint frames; E2 (`deepestEFull ∘ Ψ = deepestEFull`) is FALSE at
    -- general frames (the moved (2,2) block leaks into `P01` via `(Pf 0)₀₁·M·(Qf last)₁₀`). Sound
    -- iff `Pf 0` is block-LOWER (top-right `toBlocks₁₂ = 0`) and `Qf last` block-UPPER (bottom-left
    -- `toBlocks₂₁ = 0`) on the `r/rest` split. Discharged at the `_L2` caller by the explicit
    -- triangular normalizers (`deepestPoint_leadingBlock_isUnit` + Core `blockLower/blockUpper`).
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (coreAbsorb : DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (regStraighten : DeepestSplit H r (deepestNGauge H r) → DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hregval : ∀ q : DeepestSplit H r (deepestNGauge H r),
      (regStraighten q).1 = deepestEFull H r hr hL J Pf Qf q)
    (hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL)
    (Score : (Fin (flatDim H) → ℝ) → ℝ)
    (hScoreDef : Score = fun w => ∑ i, ∑ j, (((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
            * endpointQL H hL Qf)).toBlocks₂₂
        - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
              * endpointQL H hL Qf)).toBlocks₂₁
          * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
          * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm w) - B)
                * endpointQL H hL Qf)).toBlocks₁₂) i j) ^ 2)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL))
    (hL2eq : L = 2) :
    rlctAtOn Φscore wstar
      = rlctAtOn
          (fun x : Fin (flatDim H) → ℝ =>
            (∑ i, (regStraighten (split x)).1 i ^ 2)
              + deepestCoreF H r (coreAbsorb (split x)).2.1)
          ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
  -- The basepoint of the conclusion's RHS is `wstar` (`hwstar`).
  rw [← hwstar]
  -- The absorbed-core target function `Φcore`.
  set Φcore : (Fin (flatDim H) → ℝ) → ℝ :=
    fun x => (∑ i, (regStraighten (split x)).1 i ^ 2)
      + deepestCoreF H r (coreAbsorb (split x)).2.1 with hΦcore
  -- S6 comp-identity (germ), S2 (ContDiff), S4 (fderiv at the id CLE), S3 (fixpoint).
  have hcomp : (fun x => Φcore (psiL2 H r B hB hr hL J Pf Qf x)) =ᶠ[nhds wstar] Φscore :=
    comp_identity_L2 H r B hB hr hL hL2 hpos J hJfront Pf Qf hPtri hQtri split coreAbsorb
      regStraighten hsplit hregval hcoreabs Score hScoreDef Φscore hΦscore wstar hwstar hL2eq
  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar (psiL2 H r B hB hr hL J Pf Qf)
    (ContinuousLinearEquiv.refl ℝ (Fin (flatDim H) → ℝ))
    (psiL2_contDiff H r B hB hr hL J Pf Qf)
    (psiL2_hasStrictFDerivAt H r B hB hr hL J Pf Qf wstar hwstar)
    (psiL2_fixpoint H r B hB hr hL J Pf Qf wstar hwstar)
    hcomp

end DLNFibre.DLN.RLCT
