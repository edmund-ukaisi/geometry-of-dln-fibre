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

/-! ### S0b — the joint action as a decode→edit→encode lens (Codex option A, the S2/S4 foundation)

`psiSplitRawL2Core` re-encodes through `paramsEquivFlat`/`regGaugeSlotEquiv`, editing the last-layer
core block (`T1 ↦ T1'`) and the last-layer reg `Y`-tag (`Y1 ↦ Y1'`). To prove `δ = psiSplitRawL2Core
− id` is `ContDiffAt` (S2) and strict-deriv-`0` (S4) without fighting `Function.update`/`match` casts,
express `δ` through two DECODED delta-payloads (`l2CoreΔTuple`, `l2GaugeΔ`) re-encoded by the CLEs
(`paramsEquivFlatCLE`, `regGaugeSlotCLE`). The named last-layer matrices (`l2A0…l2Y1p`, matching the
`let` bodies of `psiSplitRawL2Core` exactly), the `rfl`-confirmed `psiSplitRawL2Core_eq`, and the
decomposition `psiSplitDeltaL2Core_eq_payload` are the load-bearing facts. -/

/-- `paramsEquivFlatCLE.symm` and `paramsEquivFlat.symm` coerce to the same function. -/
theorem paramsEquivFlatCLE_symm_coe (M : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatCLE M).symm = ⇑(paramsEquivFlat M).symm := by
  funext y
  apply (paramsEquivFlat M).injective
  rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatCLE_coe M,
    (paramsEquivFlatCLE M).apply_symm_apply]

/-- `regGaugeSlotCLE.symm` and `regGaugeSlotEquiv.symm` coerce to the same function. -/
theorem regGaugeSlotCLE_symm_coe (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ⇑(regGaugeSlotCLE H r hr hL).symm = ⇑(regGaugeSlotEquiv H r hr hL).symm := by
  funext g
  apply (regGaugeSlotEquiv H r hr hL).injective
  rw [(regGaugeSlotEquiv H r hr hL).apply_symm_apply, ← regGaugeSlotCLE_coe H r hr hL,
    (regGaugeSlotCLE H r hr hL).apply_symm_apply]

/-- The `A0 = 1 + readX_0` block (last-layer joint action, matching `psiSplitRawL2Core`'s `let`). -/
noncomputable def l2A0 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Matrix (Fin r) (Fin r) ℝ :=
  1 + readX H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L)

/-- The `A1 = 1 + readX_last` block. -/
noncomputable def l2A1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Matrix (Fin r) (Fin r) ℝ :=
  1 + readX H r hr hL (q.1, q.2.2) (lastLayer hL)

/-- The `Y0 = readY_0` block, cols bridged to the middle interface (`midWidth_eq_of_L2`). -/
noncomputable def l2Y0 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  Matrix.reindex (Equiv.refl (Fin r)) (finCongr (midWidth_eq_of_L2 H r hL hL2eq))
    (readY H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L))

/-- The `Z1 = readZ_last` block. -/
noncomputable def l2Z1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin r) ℝ :=
  readZ H r hr hL (q.1, q.2.2) (lastLayer hL)

/-- The `Y1 = readY_last` block (the reg block the joint action edits). -/
noncomputable def l2Y1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  readY H r hr hL (q.1, q.2.2) (lastLayer hL)

/-- The `T1 = coreLast` block (the core block the joint action edits). -/
noncomputable def l2T1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ := coreLast H r hL q

/-- The full-product `(1,1)` block `P00 = A0·A1 + Y0·Z1`. -/
noncomputable def l2P00 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : Matrix (Fin r) (Fin r) ℝ :=
  l2A0 H r hr hL q * l2A1 H r hr hL q + l2Y0 H r hr hL hL2eq q * l2Z1 H r hr hL q

/-- The new last-layer core block `T1' = W⁻¹·[(1−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1]`. -/
noncomputable def l2T1p (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  let A0 := l2A0 H r hr hL q; let A1 := l2A1 H r hr hL q; let Y0 := l2Y0 H r hr hL hL2eq q
  let Z1 := l2Z1 H r hr hL q; let Y1 := l2Y1 H r hr hL q; let T1 := l2T1 H r hr hL q
  let P00 := l2P00 H r hr hL hL2eq q
  let K := Z1 * P00⁻¹ * Y0
  let W := 1 + Z1 * A1⁻¹ * A0⁻¹ * Y0
  let S1 := T1 - Z1 * A1⁻¹ * Y1
  W⁻¹ * ((1 - K) * S1 + Z1 * A1⁻¹ * Y1 + Z1 * A1⁻¹ * A0⁻¹ * Y0 * T1)

/-- The new last-layer reg block `Y1' = Y1 + A0⁻¹·Y0·(T1 − T1')`. -/
noncomputable def l2Y1p (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  l2Y1 H r hr hL q
    + (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q
      * (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q)

/-- The edited reg/gauge function `g'` (the last-layer `Y`-tag set to `Y1'`, else `g`). -/
noncomputable def l2g' (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : RegGaugeIdx H r → ℝ := fun idx =>
  match idx with
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : s = lastLayer hL then l2Y1p H r hr hL hL2eq q i (h ▸ j)
        else regGaugeSlotEquiv H r hr hL (q.1, q.2.2) idx
  | _ => regGaugeSlotEquiv H r hr hL (q.1, q.2.2) idx

/-- **`psiSplitRawL2Core` IS the encoded triple** in terms of `l2g'`/`l2T1p` (`rfl` — the named
matrices are exactly the def's `let` bodies). -/
theorem psiSplitRawL2Core_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    psiSplitRawL2Core H r hr hL hL2eq q
      = (((regGaugeSlotEquiv H r hr hL).symm (l2g' H r hr hL hL2eq q)).1,
          (paramsEquivFlat (deepestM H r)
            (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1)
              (lastLayer hL) (l2T1p H r hr hL hL2eq q)),
          ((regGaugeSlotEquiv H r hr hL).symm (l2g' H r hr hL hL2eq q)).2)) := rfl

/-- The decoded **core** delta payload: `0` on every layer except the last, where it is `T1' − T1`. -/
noncomputable def l2CoreΔTuple (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params (deepestM H r) :=
  Function.update (0 : Params (deepestM H r)) (lastLayer hL)
    (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q)

/-- The decoded **reg/gauge** delta payload `g' − g` (nonzero only at the last-layer `Y`-tags). -/
noncomputable def l2GaugeΔ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) : RegGaugeIdx H r → ℝ :=
  l2g' H r hr hL hL2eq q - regGaugeSlotEquiv H r hr hL (q.1, q.2.2)

/-- The core payload encoded by `paramsEquivFlatCLE` is the flat `core' − q.2.1`. -/
theorem paramsEquivFlatCLE_l2CoreΔTuple_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q)
      = paramsEquivFlat (deepestM H r)
          (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1) (lastLayer hL)
            (l2T1p H r hr hL hL2eq q))
        - q.2.1 := by
  let d : Params (deepestM H r) := (paramsEquivFlat (deepestM H r)).symm q.2.1
  let u : Params (deepestM H r) := Function.update d (lastLayer hL) (l2T1p H r hr hL hL2eq q)
  have hd_last : d (lastLayer hL) = l2T1 H r hr hL q := rfl
  have hΔ : l2CoreΔTuple H r hr hL hL2eq q = u - d := by
    funext s
    show l2CoreΔTuple H r hr hL hL2eq q s = u s - d s
    rcases eq_or_ne s (lastLayer hL) with h | h
    · subst h
      rw [show u (lastLayer hL) = l2T1p H r hr hL hL2eq q from Function.update_self _ _ _, hd_last]
      simp only [l2CoreΔTuple, Function.update_self]
    · rw [show u s = d s from Function.update_of_ne h _ _, sub_self]
      show l2CoreΔTuple H r hr hL hL2eq q s = 0
      rw [l2CoreΔTuple, Function.update_of_ne h]; rfl
  rw [hΔ, map_sub, paramsEquivFlatCLE_coe]
  show paramsEquivFlat (deepestM H r) u - paramsEquivFlat (deepestM H r) d
    = paramsEquivFlat (deepestM H r) u - q.2.1
  rw [(paramsEquivFlat (deepestM H r)).apply_symm_apply]

/-- **The decomposition** `psiSplitRawL2Core q − q = (encoded payloads)` (the S2/S4 foundation): the
reg/spec slots are `regGaugeSlotCLE.symm (l2GaugeΔ q)`, the core slot `paramsEquivFlatCLE (l2CoreΔTuple
q)`. -/
theorem psiSplitDeltaL2Core_eq_payload (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    psiSplitRawL2Core H r hr hL hL2eq q - q
      = (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)).1,
          (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q),
            ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)).2)) := by
  have hcore := paramsEquivFlatCLE_l2CoreΔTuple_eq H r hr hL hL2eq q
  have hgg : (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)
      = (regGaugeSlotEquiv H r hr hL).symm (l2g' H r hr hL hL2eq q) - (q.1, q.2.2) := by
    rw [l2GaugeΔ, map_sub, regGaugeSlotCLE_symm_coe]
    congr 1
    rw [(regGaugeSlotEquiv H r hr hL).symm_apply_apply]
  rw [psiSplitRawL2Core_eq, hcore]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [Prod.fst_sub, hgg, Prod.fst_sub]
  · rfl
  · rw [Prod.snd_sub, Prod.snd_sub, hgg, Prod.snd_sub]

/-! ### S4a — matrix-entry strict-derivative-`0` helpers (the `O(read²)` building blocks)

Generic entrywise strict-`fderiv`-`0` facts for matrix products at a point `x` where an outer factor
vanishes (Codex route A): a product `(A·B)_{ij} = ∑_k A_{ik} B_{kj}` has strict derivative `0` at `x`
when one factor vanishes at `x` (value) and has derivative `0` there (the partner being merely
`ContDiffAt`). These reduce the `O(read²)` joint-action corrections (`K`, `R`, `W−1`, `Y1'−Y1`,
`Br−T1`) to the scalar atoms (`hasStrictFDerivAt_triple_mul_zero` &c.). -/

section MatrixEntryDeriv
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `(A·B)_{ij}` strict-`fderiv`-`0`: the LEFT factor row `A_{i·}` vanishes (value + derivative). -/
theorem hasStrictFDerivAt_matrix_mul_entry_of_left_zero
    {m n p : Type*} [Fintype n]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X} (i : m) (j : p)
    (hAd : ∀ k, HasStrictFDerivAt (fun y => A y i k) (0 : X →L[ℝ] ℝ) x)
    (hA0 : ∀ k, A x i k = 0)
    (hB : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y k j) x) :
    HasStrictFDerivAt (fun y => (A y * B y) i j) (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ k : n, HasStrictFDerivAt (fun y => A y i k * B y k j) (0 : X →L[ℝ] ℝ) x := by
    intro k
    have hBd : HasStrictFDerivAt (fun y => B y k j) (fderiv ℝ (fun y => B y k j) x) x :=
      (hB k).hasStrictFDerivAt (by simp)
    have hm := (hAd k).mul hBd
    rw [hA0 k, zero_smul, smul_zero, add_zero] at hm
    exact hm
  have hsum := HasStrictFDerivAt.sum (u := (Finset.univ : Finset n)) (fun k _ => hterm k)
  rw [show (fun y => (A y * B y) i j) = ∑ k : n, (fun y => A y i k * B y k j) from by
    funext y; rw [Matrix.mul_apply, Finset.sum_apply]]
  simpa using hsum

/-- `(A·B)_{ij}` strict-`fderiv`-`0`: the RIGHT factor column `B_{·j}` vanishes (value + derivative). -/
theorem hasStrictFDerivAt_matrix_mul_entry_of_right_zero
    {m n p : Type*} [Fintype n]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X} (i : m) (j : p)
    (hA : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i k) x)
    (hBd : ∀ k, HasStrictFDerivAt (fun y => B y k j) (0 : X →L[ℝ] ℝ) x)
    (hB0 : ∀ k, B x k j = 0) :
    HasStrictFDerivAt (fun y => (A y * B y) i j) (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ k : n, HasStrictFDerivAt (fun y => A y i k * B y k j) (0 : X →L[ℝ] ℝ) x := by
    intro k
    have hAd : HasStrictFDerivAt (fun y => A y i k) (fderiv ℝ (fun y => A y i k) x) x :=
      (hA k).hasStrictFDerivAt (by simp)
    have hm := hAd.mul (hBd k)
    rw [hB0 k, smul_zero, zero_smul, add_zero] at hm
    exact hm
  have hsum := HasStrictFDerivAt.sum (u := (Finset.univ : Finset n)) (fun k _ => hterm k)
  rw [show (fun y => (A y * B y) i j) = ∑ k : n, (fun y => A y i k * B y k j) from by
    funext y; rw [Matrix.mul_apply, Finset.sum_apply]]
  simpa using hsum

/-- `(A·B·C)_{ij}` strict-`fderiv`-`0`: the OUTER factors `A`, `C` both vanish (value) at `x`. -/
theorem hasStrictFDerivAt_matrix_triple_mul_entry_zero
    {m n p qq : Type*} [Fintype n] [Fintype p]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {C : X → Matrix p qq ℝ} {x : X}
    (i : m) (j : qq)
    (hA : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y a b) x)
    (hB : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y a b) x)
    (hC : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => C y a b) x)
    (hA0 : ∀ a b, A x a b = 0) (hC0 : ∀ a b, C x a b = 0) :
    HasStrictFDerivAt (fun y => (A y * B y * C y) i j) (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ l k, HasStrictFDerivAt (fun y => A y i k * B y k l * C y l j)
      (0 : X →L[ℝ] ℝ) x := fun l k =>
    hasStrictFDerivAt_triple_mul_zero (fun y => A y i k) (fun y => B y k l) (fun y => C y l j)
      (hA i k) (hB k l) (hC l j) (hA0 i k) (hC0 l j)
  have hsum := HasStrictFDerivAt.sum (u := (Finset.univ : Finset p)) (fun l _ =>
    HasStrictFDerivAt.sum (u := (Finset.univ : Finset n)) (fun k _ => hterm l k))
  rw [show (fun y => (A y * B y * C y) i j)
      = ∑ l : p, ∑ k : n, (fun y => A y i k * B y k l * C y l j) from by
    funext y
    rw [Matrix.mul_apply,
      show (∑ l : p, ∑ k : n, (fun y => A y i k * B y k l * C y l j)) y
        = ∑ l : p, ∑ k : n, A y i k * B y k l * C y l j from by simp only [Finset.sum_apply]]
    exact Finset.sum_congr rfl (fun l _ => by rw [Matrix.mul_apply, Finset.sum_mul])]
  simpa using hsum

/-! ### S4a' — `ContDiffAt` det / adjugate / inverse-entry variants + the `W⁻¹` derivative

The landed `contDiffAt_matrix_inv_entry_of_det_ne_zero` (DeepestSchurSmooth) needs GLOBAL entrywise
`ContDiff`; the joint-action matrices (`W = 1 + Z1·A1⁻¹·A0⁻¹·Y0`) have entries that are only `ContDiffAt`
(they carry `A_s⁻¹`). These `_at` variants run the same `det⁻¹·adjugate` route with `ContDiffAt`. The
keystone `hasStrictFDerivAt_winv_sub_one_entry_zero` gives `D(W⁻¹−1)(0) = 0` WITHOUT det/adjugate
derivative bookkeeping: on `{det W ≠ 0}` (a nbhd of `0`), `W⁻¹ − 1 = −(W⁻¹·(W−1))`, whose entry has
strict derivative `0` (the right factor `W−1` vanishes value + derivative). -/

/-- `ContDiffAt` determinant of an entrywise-`ContDiffAt` matrix family. -/
theorem contDiffAt_matrix_det_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {A : X → Matrix n n ℝ} {x : X}
    (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).det) x := by
  have heq : (fun y => (A y).det)
      = fun y => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A y (σ i) i := by
    funext y; rw [Matrix.det_apply]
  rw [heq]
  exact ContDiffAt.sum (fun σ _ => (contDiffAt_prod (fun i _ => hA (σ i) i)).const_smul _)

/-- `ContDiffAt` adjugate entry of an entrywise-`ContDiffAt` matrix family. -/
theorem contDiffAt_matrix_adjugate_entry_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {A : X → Matrix n n ℝ} {x : X}
    (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x) (i j : n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).adjugate i j) x := by
  have heq : (fun y => (A y).adjugate i j)
      = fun y => ((A y).updateRow j (Pi.single i 1)).det := by
    funext y; rw [Matrix.adjugate_apply]
  rw [heq]
  refine contDiffAt_matrix_det_of_entries (fun a b => ?_)
  by_cases hab : a = j
  · subst hab
    have : (fun y => ((A y).updateRow a (Pi.single i 1)) a b)
        = fun _ : X => (Pi.single i (1 : ℝ) : n → ℝ) b := by
      funext y; rw [Matrix.updateRow_self]
    rw [this]; exact contDiffAt_const
  · have : (fun y => ((A y).updateRow j (Pi.single i 1)) a b) = fun y => A y a b := by
      funext y; rw [Matrix.updateRow_ne hab]
    rw [this]; exact hA a b

/-- `ContDiffAt` inverse entry on the det-nonzero locus (entrywise-`ContDiffAt` family variant). -/
theorem contDiffAt_matrix_inv_entry_of_det_ne_zero_at {n : Type*} [Fintype n] [DecidableEq n]
    {A : X → Matrix n n ℝ} {x : X}
    (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ i j) x := by
  have hentry : (fun y => (A y)⁻¹ i j) = fun y => (A y).det⁻¹ * (A y).adjugate i j := by
    funext y; rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [hentry]
  exact ((contDiffAt_matrix_det_of_entries hA).inv hdet).mul
    (contDiffAt_matrix_adjugate_entry_of_entries hA i j)

/-- The unit-locus identity `W⁻¹ − 1 = −(W⁻¹·(W−1))`. -/
theorem winv_sub_one_eq {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℝ) (h : IsUnit W.det) : W⁻¹ - 1 = -(W⁻¹ * (W - 1)) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.nonsing_inv_mul W h, neg_sub]

/-- **`D(W⁻¹ − 1)(x) = 0` entrywise** when `det W x ≠ 0`, `W` entrywise `ContDiffAt`, and `W − 1`
vanishes value + strict-derivative at `x` (`W = 1 + O(read²)`). On `{det W ≠ 0}` (a nbhd of `x`),
`W⁻¹ − 1 = −(W⁻¹·(W−1))`, whose entry has strict derivative `0` (the right factor `W−1` vanishes). -/
theorem hasStrictFDerivAt_winv_sub_one_entry_zero {n : Type*} [Fintype n] [DecidableEq n]
    {W : X → Matrix n n ℝ} {x : X} (i j : n)
    (hWentry : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => W y a b) x)
    (hdet : (W x).det ≠ 0)
    (hRd : ∀ a b, HasStrictFDerivAt (fun y => (W y - 1) a b) (0 : X →L[ℝ] ℝ) x)
    (hR0 : ∀ a b, (W x - 1) a b = 0) :
    HasStrictFDerivAt (fun y => ((W y)⁻¹ - 1) i j) (0 : X →L[ℝ] ℝ) x := by
  have hWinv : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (W y)⁻¹ a b) x := fun a b =>
    contDiffAt_matrix_inv_entry_of_det_ne_zero_at hWentry hdet a b
  have hprod : HasStrictFDerivAt (fun y => ((W y)⁻¹ * (W y - 1)) i j) (0 : X →L[ℝ] ℝ) x :=
    hasStrictFDerivAt_matrix_mul_entry_of_right_zero i j
      (fun k => hWinv i k) (fun k => hRd k j) (fun k => hR0 k j)
  have hneg : HasStrictFDerivAt (fun y => -(((W y)⁻¹ * (W y - 1)) i j)) (0 : X →L[ℝ] ℝ) x := by
    simpa using hprod.neg
  refine hneg.congr_of_eventuallyEq ?_
  have hnbhd : {y | (W y).det ≠ 0} ∈ nhds x :=
    (contDiffAt_matrix_det_of_entries hWentry).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hdet)
  filter_upwards [hnbhd] with y hy
  rw [winv_sub_one_eq (W y) (isUnit_iff_ne_zero.mpr hy), Matrix.neg_apply]

end MatrixEntryDeriv

/-- **`paramsEquivFlat.symm` sends the zero flat-core to the zero core tuple.** -/
theorem paramsEquivFlat_symm_zero (M : Fin (L + 1) → ℕ) :
    (paramsEquivFlat M).symm (0 : Fin (flatDim M) → ℝ) = (fun _ => 0 : Params M) := by
  have h0 : (paramsEquivFlat M) (fun _ => 0 : Params M) = (0 : Fin (flatDim M) → ℝ) := by
    funext i; rfl
  rw [← h0, (paramsEquivFlat M).symm_apply_apply]

/-! ### S4b — the named matrices at the split origin (all reads vanish there)

At `q = 0` every read vanishes (`readX/Y/Z_zero`), so `A0 = A1 = 1`, `Y0 = Z1 = Y1 = T1 = 0`. These feed
the `O(read²)` strict-derivative-vanishing of the joint correction (S4). -/

/-- The gauge slot `(q.1, q.2.2)` of the split origin is `0`. -/
theorem gaugeProj_zero (H : Fin (L + 1) → ℕ) (r : ℕ) :
    ((0 : DeepestSplit H r (deepestNGauge H r)).1, (0 : DeepestSplit H r (deepestNGauge H r)).2.2)
      = (0 : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) := rfl

/-- `A0 = 1` at the origin. -/
theorem l2A0_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : l2A0 H r hr hL 0 = 1 := by
  rw [l2A0, gaugeProj_zero, readX_zero H r hr hL, add_zero]

/-- `A1 = 1` at the origin. -/
theorem l2A1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : l2A1 H r hr hL 0 = 1 := by
  rw [l2A1, gaugeProj_zero, readX_zero H r hr hL, add_zero]

/-- `Y0 = 0` at the origin. -/
theorem l2Y0_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2Y0 H r hr hL hL2eq 0 = 0 := by
  rw [l2Y0, gaugeProj_zero, readY_zero H r hr hL]
  simp only [Matrix.reindex_apply, Matrix.submatrix_zero, Pi.zero_apply]

/-- `Z1 = 0` at the origin. -/
theorem l2Z1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : l2Z1 H r hr hL 0 = 0 := by
  rw [l2Z1, gaugeProj_zero, readZ_zero H r hr hL]

/-- `Y1 = 0` at the origin. -/
theorem l2Y1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : l2Y1 H r hr hL 0 = 0 := by
  rw [l2Y1, gaugeProj_zero, readY_zero H r hr hL]

/-- `T1 = 0` at the origin (`coreLast 0 = 0`). -/
theorem l2T1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : l2T1 H r hr hL 0 = 0 := by
  rw [l2T1, coreLast]
  show (paramsEquivFlat (deepestM H r)).symm
    ((0 : DeepestSplit H r (deepestNGauge H r)).2.1) (lastLayer hL) = 0
  rw [show ((0 : DeepestSplit H r (deepestNGauge H r)).2.1) = 0 from rfl,
    paramsEquivFlat_symm_zero]

/-! ### S4c — entrywise `ContDiff` of the named matrices + inverse `ContDiffAt` at the origin

Each named matrix entry is `ContDiff ℝ ⊤` (the reads via `contDiff_read*_entry ∘ contDiff_gaugeProj`,
the core via `contDiff_coreRead_entry`). At the origin the pivots `A0, A1, P00, W` are `1` (so `det = 1
≠ 0`), giving `ContDiffAt` of their inverse entries via the `_at` inverse lemma. These are the
`ContDiffAt` hypotheses the S4 strict-derivative helpers and the S2 smoothness leaf consume. -/

/-- The gauge projection `q ↦ (q.1, q.2.2)` is `ContDiff ⊤`. -/
theorem contDiff_gaugeProj (H : Fin (L + 1) → ℕ) (r : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => (q.1, q.2.2)) :=
  contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)

/-- Each `l2A0` entry is `ContDiff ⊤`. -/
theorem contDiff_l2A0_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2A0 H r hr hL q i j) := by
  have : (fun q => l2A0 H r hr hL q i j)
      = fun q => (1 : Matrix (Fin r) (Fin r) ℝ) i j
          + readX H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L) i j := by
    funext q; rw [l2A0, Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readX_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r))

/-- Each `l2A1` entry is `ContDiff ⊤`. -/
theorem contDiff_l2A1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2A1 H r hr hL q i j) := by
  have : (fun q => l2A1 H r hr hL q i j)
      = fun q => (1 : Matrix (Fin r) (Fin r) ℝ) i j
          + readX H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by
    funext q; rw [l2A1, Matrix.add_apply]
  rw [this]
  exact contDiff_const.add ((contDiff_readX_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r))

/-- Each `l2Z1` entry is `ContDiff ⊤`. -/
theorem contDiff_l2Z1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Z1 H r hr hL q i j) := by
  have : (fun q => l2Z1 H r hr hL q i j)
      = fun q => readZ H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by funext q; rw [l2Z1]
  rw [this]; exact (contDiff_readZ_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r)

/-- Each `l2Y1` entry is `ContDiff ⊤`. -/
theorem contDiff_l2Y1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Y1 H r hr hL q i j) := by
  have : (fun q => l2Y1 H r hr hL q i j)
      = fun q => readY H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by funext q; rw [l2Y1]
  rw [this]; exact (contDiff_readY_entry H r hr hL _ i j).comp (contDiff_gaugeProj H r)

/-- Each `l2T1` entry is `ContDiff ⊤` (the last-layer core read). -/
theorem contDiff_l2T1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2T1 H r hr hL q i j) := by
  have : (fun q => l2T1 H r hr hL q i j)
      = fun q => (paramsEquivFlat (deepestM H r)).symm q.2.1 (lastLayer hL) i j := by
    funext q; rw [l2T1, coreLast]
  rw [this]; exact contDiff_coreRead_entry H r hr hL (lastLayer hL) i j

/-- Each `l2Y0` entry is `ContDiff ⊤` (the col-reindexed first-layer `readY`). -/
theorem contDiff_l2Y0_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Y0 H r hr hL hL2eq q i j) := by
  have : (fun q => l2Y0 H r hr hL hL2eq q i j)
      = fun q => readY H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L) i
          ((finCongr (midWidth_eq_of_L2 H r hL hL2eq)).symm j) := by
    funext q
    rw [l2Y0, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply]
  rw [this]
  exact (contDiff_readY_entry H r hr hL _ i _).comp (contDiff_gaugeProj H r)

/-- `l2P00 = 1` at the origin (`A0·A1 + Y0·Z1 = 1·1 + 0·0`). -/
theorem l2P00_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2P00 H r hr hL hL2eq 0 = 1 := by
  rw [l2P00, l2A0_zero, l2A1_zero, l2Y0_zero, l2Z1_zero, Matrix.mul_one, Matrix.zero_mul, add_zero]

/-- Each `A0⁻¹` entry is `ContDiffAt` at the origin (`det (A0 0) = det 1 = 1 ≠ 0`). -/
theorem contDiffAt_l2A0inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A0 H r hr hL q)⁻¹ i j) 0 := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A0_entry H r hr hL a b).contDiffAt) ?_ i j
  rw [l2A0_zero, Matrix.det_one]; exact one_ne_zero

/-- Each `A1⁻¹` entry is `ContDiffAt` at the origin. -/
theorem contDiffAt_l2A1inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A1 H r hr hL q)⁻¹ i j) 0 := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A1_entry H r hr hL a b).contDiffAt) ?_ i j
  rw [l2A1_zero, Matrix.det_one]; exact one_ne_zero

/-! ### S4d — the named composites (K, R, W, S1, Br), normalizations, and the core payload deriv-0

The `O(read²)` strict-derivative-vanishing of the joint correction's core block `T1' − T1`, via Codex
route A: normalize `T1' − T1 = (W⁻¹−1)·Br + (Br − T1)` with `Br − T1 = −K·S1 + R·T1`, then each summand's
entry is a matrix product with a value+derivative-vanishing factor (`K`, `R`, `W⁻¹−1` are all `O(read²)`
at the origin). The encoded core payload `paramsEquivFlatCLE (l2CoreΔTuple ·)` descends to these per-entry
facts over the honest `Fin (flatDim) → ℝ` codomain (avoiding the `Params`-def whnf wall). -/

-- Named composites (matching l2T1p's lets).
noncomputable def l2K (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹ * l2Y0 H r hr hL hL2eq q

noncomputable def l2R (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q

noncomputable def l2W (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  1 + l2R H r hr hL hL2eq q

noncomputable def l2S1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  l2T1 H r hr hL q - l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1 H r hr hL q

noncomputable def l2Br (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  (1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL hL2eq q
    + l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1 H r hr hL q
    + l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q
      * l2T1 H r hr hL q

-- l2T1p = W⁻¹ * Br (rfl — Br matches the bracket, W matches).
theorem l2T1p_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2T1p H r hr hL hL2eq q = (l2W H r hr hL hL2eq q)⁻¹ * l2Br H r hr hL hL2eq q := rfl

-- Br - T1 = -K·S1 + R·T1.
theorem l2Br_sub_T1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2Br H r hr hL hL2eq q - l2T1 H r hr hL q
      = -(l2K H r hr hL hL2eq q * l2S1 H r hr hL hL2eq q)
        + l2R H r hr hL hL2eq q * l2T1 H r hr hL q := by
  rw [l2Br, l2S1, l2R]
  -- expand (1-K)*(T1 - ZY) = (T1-ZY) - K*(T1-ZY); the ±ZY cancel with the standalone +ZY.
  set Z1 := l2Z1 H r hr hL q
  set A1i := (l2A1 H r hr hL q)⁻¹
  set A0i := (l2A0 H r hr hL q)⁻¹
  set Y0 := l2Y0 H r hr hL hL2eq q
  set Y1 := l2Y1 H r hr hL q
  set T1 := l2T1 H r hr hL q
  set K := l2K H r hr hL hL2eq q
  -- S1 = T1 - Z1*A1i*Y1 (by l2S1 def, set above already substituted)
  show (1 - K) * (T1 - Z1 * A1i * Y1) + Z1 * A1i * Y1
      + Z1 * A1i * A0i * Y0 * T1 - T1
    = -(K * (T1 - Z1 * A1i * Y1)) + Z1 * A1i * A0i * Y0 * T1
  rw [Matrix.sub_mul, Matrix.one_mul]
  -- (T1 - ZY) - K*(T1-ZY) + ZY + R*T1 - T1 = -(K*(T1-ZY)) + R*T1
  abel

-- T1' - T1 = (W⁻¹ - 1)*Br + (Br - T1).
theorem l2T1p_sub_T1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q
      = ((l2W H r hr hL hL2eq q)⁻¹ - 1) * l2Br H r hr hL hL2eq q
        + (l2Br H r hr hL hL2eq q - l2T1 H r hr hL q) := by
  rw [l2T1p_eq]
  set Wi := (l2W H r hr hL hL2eq q)⁻¹
  set Br := l2Br H r hr hL hL2eq q
  set T1 := l2T1 H r hr hL q
  rw [Matrix.sub_mul, Matrix.one_mul]
  abel

-- at-0 values of composites.
theorem l2R_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2R H r hr hL hL2eq 0 = 0 := by
  rw [l2R, l2Z1_zero]; simp [Matrix.zero_mul]

theorem l2W_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2W H r hr hL hL2eq 0 = 1 := by
  rw [l2W, l2R_zero, add_zero]

theorem l2K_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2K H r hr hL hL2eq 0 = 0 := by
  rw [l2K, l2Z1_zero]; simp [Matrix.zero_mul]

-- ContDiffAt-at-0 of P00⁻¹ entries.
theorem contDiffAt_l2P00inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2P00 H r hr hL hL2eq q)⁻¹ i j) 0 := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at (fun a b => ?_) ?_ i j
  · -- l2P00 entry = A0*A1 + Y0*Z1 entry, ContDiffAt (products of ContDiff entries).
    have : (fun q => l2P00 H r hr hL hL2eq q a b)
        = fun q => (l2A0 H r hr hL q * l2A1 H r hr hL q) a b
          + (l2Y0 H r hr hL hL2eq q * l2Z1 H r hr hL q) a b := by
      funext q; rw [l2P00, Matrix.add_apply]
    rw [this]
    refine ContDiffAt.add ?_ ?_
    · exact contDiffAt_matrix_mul_entry (fun a' k => (contDiff_l2A0_entry H r hr hL a' k).contDiffAt)
        (fun k b' => (contDiff_l2A1_entry H r hr hL k b').contDiffAt) a b
    · exact contDiffAt_matrix_mul_entry (fun a' k => (contDiff_l2Y0_entry H r hr hL hL2eq a' k).contDiffAt)
        (fun k b' => (contDiff_l2Z1_entry H r hr hL k b').contDiffAt) a b
  · rw [l2P00_zero, Matrix.det_one]; exact one_ne_zero

-- ContDiff (everywhere) of l2A1⁻¹*l2A0⁻¹ entries at 0 (ContDiffAt) — needed as the R-triple middle.
theorem contDiffAt_l2A1invA0inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) i j) 0 :=
  contDiffAt_matrix_mul_entry (fun a k => contDiffAt_l2A1inv_entry H r hr hL a k)
    (fun k b => contDiffAt_l2A0inv_entry H r hr hL k b) i j

-- K entry strict-deriv-0 (triple Z1·P00⁻¹·Y0, Z1/Y0 outer vanish).
theorem hasStrictFDerivAt_l2K_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => l2K H r hr hL hL2eq q i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => l2K H r hr hL hL2eq q i j)
      = fun q => (l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹ * l2Y0 H r hr hL hL2eq q) i j := by
    funext q; rw [l2K]
  rw [heq]
  refine hasStrictFDerivAt_matrix_triple_mul_entry_zero (A := fun q => l2Z1 H r hr hL q)
    (B := fun q => (l2P00 H r hr hL hL2eq q)⁻¹) (C := fun q => l2Y0 H r hr hL hL2eq q) i j
    (fun a b => (contDiff_l2Z1_entry H r hr hL a b).contDiffAt)
    (fun a b => contDiffAt_l2P00inv_entry H r hr hL hL2eq a b)
    (fun a b => (contDiff_l2Y0_entry H r hr hL hL2eq a b).contDiffAt) ?_ ?_
  · intro a b; simp only [l2Z1_zero, Matrix.zero_apply]
  · intro a b; simp only [l2Y0_zero, Matrix.zero_apply]

-- R entry strict-deriv-0 (Z1·(A1⁻¹A0⁻¹)·Y0 after reassoc, Z1/Y0 outer vanish).
theorem hasStrictFDerivAt_l2R_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => l2R H r hr hL hL2eq q i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => l2R H r hr hL hL2eq q i j)
      = fun q => (l2Z1 H r hr hL q * ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹)
          * l2Y0 H r hr hL hL2eq q) i j := by
    funext q
    have hassoc : l2R H r hr hL hL2eq q
        = l2Z1 H r hr hL q * ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) * l2Y0 H r hr hL hL2eq q := by
      rw [l2R, Matrix.mul_assoc (l2Z1 H r hr hL q) (l2A1 H r hr hL q)⁻¹ (l2A0 H r hr hL q)⁻¹]
    rw [hassoc]
  rw [heq]
  refine hasStrictFDerivAt_matrix_triple_mul_entry_zero (A := fun q => l2Z1 H r hr hL q)
    (B := fun q => (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹)
    (C := fun q => l2Y0 H r hr hL hL2eq q) i j
    (fun a b => (contDiff_l2Z1_entry H r hr hL a b).contDiffAt)
    (fun a b => contDiffAt_l2A1invA0inv_entry H r hr hL a b)
    (fun a b => (contDiff_l2Y0_entry H r hr hL hL2eq a b).contDiffAt) ?_ ?_
  · intro a b; simp only [l2Z1_zero, Matrix.zero_apply]
  · intro a b; simp only [l2Y0_zero, Matrix.zero_apply]

-- R entries ContDiffAt at 0 (Z1*A1⁻¹*A0⁻¹*Y0, products of ContDiffAt entries).
theorem contDiffAt_l2R_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2R H r hr hL hL2eq q i j) 0 := by
  have heq : (fun q => l2R H r hr hL hL2eq q i j)
      = fun q => (l2Z1 H r hr hL q * ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹)
          * l2Y0 H r hr hL hL2eq q) i j := by
    funext q
    have hassoc : l2R H r hr hL hL2eq q
        = l2Z1 H r hr hL q * ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) * l2Y0 H r hr hL hL2eq q := by
      rw [l2R, Matrix.mul_assoc (l2Z1 H r hr hL q) (l2A1 H r hr hL q)⁻¹ (l2A0 H r hr hL q)⁻¹]
    rw [hassoc]
  rw [heq]
  refine contDiffAt_matrix_mul_entry (A := fun q => l2Z1 H r hr hL q
      * ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹)) ?_
    (fun k b => (contDiff_l2Y0_entry H r hr hL hL2eq k b).contDiffAt) i j
  intro a k
  exact contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
    (fun k' b' => contDiffAt_l2A1invA0inv_entry H r hr hL k' b') a k

-- W entries ContDiffAt at 0 (1 + R).
theorem contDiffAt_l2W_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2W H r hr hL hL2eq q i j) 0 := by
  have heq : (fun q => l2W H r hr hL hL2eq q i j)
      = fun q => (1 : Matrix _ _ ℝ) i j + l2R H r hr hL hL2eq q i j := by
    funext q; rw [l2W, Matrix.add_apply]
  rw [heq]; exact contDiffAt_const.add (contDiffAt_l2R_entry H r hr hL hL2eq i j)

-- W - 1 entry value-0 and strict-deriv-0 (W - 1 = R).
theorem l2W_sub_one_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    (l2W H r hr hL hL2eq q - 1) i j = l2R H r hr hL hL2eq q i j := by
  rw [l2W]; simp [Matrix.add_apply, Matrix.sub_apply]

-- S1 entries ContDiffAt at 0.
theorem contDiffAt_l2S1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2S1 H r hr hL hL2eq q i j) 0 := by
  have heq : (fun q => l2S1 H r hr hL hL2eq q i j)
      = fun q => l2T1 H r hr hL q i j
          - (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1 H r hr hL q) i j := by
    funext q; rw [l2S1, Matrix.sub_apply]
  rw [heq]
  refine (contDiff_l2T1_entry H r hr hL i j).contDiffAt.sub ?_
  refine contDiffAt_matrix_mul_entry (A := fun q => l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) ?_
    (fun k b => (contDiff_l2Y1_entry H r hr hL k b).contDiffAt) i j
  intro a k
  exact contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
    (fun k' b' => contDiffAt_l2A1inv_entry H r hr hL k' b') a k

-- Br entries ContDiffAt at 0.
theorem contDiffAt_l2Br_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2Br H r hr hL hL2eq q i j) 0 := by
  -- Br = (1-K)*S1 + Z1*A1⁻¹*Y1 + Z1*A1⁻¹*A0⁻¹*Y0*T1; each term ContDiffAt.
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2eq q)
          * l2S1 H r hr hL hL2eq q) i j) 0 := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
        (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2eq q) ?_
      (fun k b => contDiffAt_l2S1_entry H r hr hL hL2eq k b) i j
    intro a k
    have hsub : (fun q => (1 - l2K H r hr hL hL2eq q) a k)
        = fun q => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) a k - l2K H r hr hL hL2eq q a k := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    refine contDiffAt_const.sub ?_
    have hKeq : (fun q => l2K H r hr hL hL2eq q a k)
        = fun q => (l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹ * l2Y0 H r hr hL hL2eq q) a k := by
      funext q; rw [l2K]
    rw [hKeq]
    refine contDiffAt_matrix_mul_entry (A := fun q => l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0_entry H r hr hL hL2eq k' b').contDiffAt) a k
    intro a' k'
    exact contDiffAt_matrix_mul_entry (fun a'' k'' => (contDiff_l2Z1_entry H r hr hL a'' k'').contDiffAt)
      (fun k'' b'' => contDiffAt_l2P00inv_entry H r hr hL hL2eq k'' b'') a' k'
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1 H r hr hL q) i j) 0 := by
    refine contDiffAt_matrix_mul_entry (A := fun q => l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) ?_
      (fun k b => (contDiff_l2Y1_entry H r hr hL k b).contDiffAt) i j
    intro a k
    exact contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' b' => contDiffAt_l2A1inv_entry H r hr hL k' b') a k
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹
          * l2Y0 H r hr hL hL2eq q * l2T1 H r hr hL q) i j) 0 := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹
          * l2Y0 H r hr hL hL2eq q) ?_
      (fun k b => (contDiff_l2T1_entry H r hr hL k b).contDiffAt) i j
    intro a k
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0_entry H r hr hL hL2eq k' b').contDiffAt) a k
    intro a' k'
    refine contDiffAt_matrix_mul_entry
      (A := fun q => l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) ?_
      (fun k'' b'' => contDiffAt_l2A0inv_entry H r hr hL k'' b'') a' k'
    intro a'' k''
    exact contDiffAt_matrix_mul_entry (fun a3 k3 => (contDiff_l2Z1_entry H r hr hL a3 k3).contDiffAt)
      (fun k3 b3 => contDiffAt_l2A1inv_entry H r hr hL k3 b3) a'' k''
  have heq : (fun q => l2Br H r hr hL hL2eq q i j)
      = fun q => (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2eq q)
          * l2S1 H r hr hL hL2eq q) i j
          + (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1 H r hr hL q) i j
          + (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q
              * l2T1 H r hr hL q) i j := by
    funext q; rw [l2Br, Matrix.add_apply, Matrix.add_apply]
  rw [heq]
  exact (h1.add h2).add h3

-- (W⁻¹ - 1) value 0 at origin.
theorem l2Winv_sub_one_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ((l2W H r hr hL hL2eq 0)⁻¹ - 1) i j = 0 := by
  rw [l2W_zero, inv_one]; simp [Matrix.sub_apply]

-- (W⁻¹-1) entry strict-deriv-0 at 0 (via the keystone lemma; W-1 = R deriv-0).
theorem hasStrictFDerivAt_l2Winv_sub_one_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => ((l2W H r hr hL hL2eq q)⁻¹ - 1) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  refine hasStrictFDerivAt_winv_sub_one_entry_zero (W := l2W H r hr hL hL2eq) i j
    (fun a b => contDiffAt_l2W_entry H r hr hL hL2eq a b) ?_ ?_ ?_
  · rw [l2W_zero, Matrix.det_one]; exact one_ne_zero
  · intro a b
    -- (W - 1) entry = R entry, deriv 0.
    refine (hasStrictFDerivAt_l2R_entry_zero H r hr hL hL2eq a b).congr_of_eventuallyEq ?_
    filter_upwards with q
    rw [l2W_sub_one_apply]
  · intro a b; rw [l2W_sub_one_apply, l2R_zero]; rfl

-- The core payload entry T1' - T1 strict-deriv-0.
theorem hasStrictFDerivAt_l2T1p_sub_T1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt (fun q => (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  -- T1'-T1 = (W⁻¹-1)*Br + (-(K*S1) + R*T1) (normalizations).
  have heq : (fun q => (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) i j)
      = fun q => (((l2W H r hr hL hL2eq q)⁻¹ - (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ)) * l2Br H r hr hL hL2eq q) i j
          + (-(l2K H r hr hL hL2eq q * l2S1 H r hr hL hL2eq q)
              + l2R H r hr hL hL2eq q * l2T1 H r hr hL q) i j := by
    funext q
    rw [l2T1p_sub_T1, l2Br_sub_T1, Matrix.add_apply]
  rw [heq]
  -- Summand 1: (W⁻¹-1)*Br, left factor (W⁻¹-1) value+deriv 0.
  have hP1 : HasStrictFDerivAt
      (fun q => (((l2W H r hr hL hL2eq q)⁻¹ - (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
          (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ)) * l2Br H r hr hL hL2eq q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i j
      (fun k => hasStrictFDerivAt_l2Winv_sub_one_entry_zero H r hr hL hL2eq i k)
      (fun k => l2Winv_sub_one_zero H r hr hL hL2eq i k)
      (fun k => (contDiffAt_l2Br_entry H r hr hL hL2eq k j))
  -- Summand 2: -(K*S1) + R*T1, both deriv 0.
  have hKS1 : HasStrictFDerivAt (fun q => (l2K H r hr hL hL2eq q * l2S1 H r hr hL hL2eq q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i j
      (fun k => hasStrictFDerivAt_l2K_entry_zero H r hr hL hL2eq i k)
      (fun k => by rw [l2K_zero]; simp)
      (fun k => (contDiffAt_l2S1_entry H r hr hL hL2eq k j))
  have hRT1 : HasStrictFDerivAt (fun q => (l2R H r hr hL hL2eq q * l2T1 H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
    hasStrictFDerivAt_matrix_mul_entry_of_left_zero i j
      (fun k => hasStrictFDerivAt_l2R_entry_zero H r hr hL hL2eq i k)
      (fun k => by rw [l2R_zero]; simp)
      (fun k => (contDiff_l2T1_entry H r hr hL k j).contDiffAt)
  have hP2 : HasStrictFDerivAt
      (fun q => (-(l2K H r hr hL hL2eq q * l2S1 H r hr hL hL2eq q)
          + l2R H r hr hL hL2eq q * l2T1 H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
    have hsum := (hKS1.neg).add hRT1
    rw [neg_zero, add_zero] at hsum
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with q
    simp only [Matrix.add_apply, Matrix.neg_apply, Pi.add_apply, Pi.neg_apply]
  have hadd := hP1.add hP2
  simpa using hadd

-- The ENCODED core payload `paramsEquivFlatCLE (l2CoreΔTuple q)` has strict-deriv 0 at 0.
-- Flat-coordinate descent (Route b): the codomain is the HONEST `Fin (flatDim) → ℝ`, which
-- `hasStrictFDerivAt_pi'` drives without the `Params`-def whnf wall. Each flat coord `k` is, by `rfl`,
-- the `l2CoreΔTuple` entry at the decoded `(s,i,j)`; deriv-0 is the per-entry core-payload fact.
-- The l2CoreΔTuple entry at (s,i,j) has strict-deriv 0 (the cast-isolating per-entry lemma):
-- update 0 last (T1'-T1) s i j is (T1'-T1) i j at s=last (deriv 0) else 0.
theorem hasStrictFDerivAt_l2CoreΔTuple_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (s : Fin L) (i : Fin (deepestM H r s.castSucc)) (j : Fin (deepestM H r s.succ)) :
    HasStrictFDerivAt (fun q => l2CoreΔTuple H r hr hL hL2eq q s i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  rcases eq_or_ne s (lastLayer hL) with hs | hs
  · subst hs
    have hentry : (fun q => l2CoreΔTuple H r hr hL hL2eq q (lastLayer hL) i j)
        = fun q => (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) i j := by
      funext q; rw [l2CoreΔTuple, Function.update_self]
    rw [hentry]
    exact hasStrictFDerivAt_l2T1p_sub_T1_entry_zero H r hr hL hL2eq i j
  · have hentry : (fun q => l2CoreΔTuple H r hr hL hL2eq q s i j) = fun _ => (0 : ℝ) := by
      funext q; rw [l2CoreΔTuple, Function.update_of_ne hs]; rfl
    rw [hentry]; exact hasStrictFDerivAt_const _ _

-- The ENCODED core payload `paramsEquivFlatCLE (l2CoreΔTuple q)` has strict-deriv 0 at 0.
-- Flat-coordinate descent (Route b, the schurShiftRaw template): codomain is the honest
-- `Fin (flatDim) → ℝ`; each flat coord k = the l2CoreΔTuple entry at decoded (s,i,j) by `rfl`.
theorem hasStrictFDerivAt_paramsEquivFlatCLE_l2CoreΔTuple_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt (fun q => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  refine hasStrictFDerivAt_pi'.2 (fun k => ?_)
  rw [ContinuousLinearMap.comp_zero]
  set d := (Fintype.equivFin (FlatIdx (deepestM H r))).symm k with hd
  have hcoord : (fun q => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q) k)
      = fun q => l2CoreΔTuple H r hr hL hL2eq q d.1.1 d.1.2 d.2 := by
    funext q
    rw [show (⇑(paramsEquivFlatCLE (deepestM H r)) : Params (deepestM H r) → _)
        = ⇑(paramsEquivFlat (deepestM H r)) from paramsEquivFlatCLE_coe (deepestM H r)]
    rfl
  rw [hcoord]
  exact hasStrictFDerivAt_l2CoreΔTuple_entry_zero H r hr hL hL2eq d.1.1 d.1.2 d.2

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

/-! ### S2a — the joint unit radius (the `cutoffBumpSplit` re-key)

`cutoffBumpSplit`'s support must sit in the JOINT unit locus where the per-layer `1 + readX_s`, the
full-product `P00`, and the Schur `W` are ALL invertible — only then is the raw correction `δ` (which
carries `A_s⁻¹`, `P00⁻¹`, `W⁻¹`) `ContDiffAt` there (S2). The `1 + readX_s` part is `unitRadius`; the
extra `det P00 ≠ 0 ∧ det W ≠ 0` part holds on a ball at `0` (both dets `= 1` at `0`, continuous), only
meaningful at `L = 2`. The joint radius is `unitRadius ⊓ (the extra radius)` at `L = 2`, `unitRadius`
otherwise (the bump stays `L`-generic; the `dite` lives only in this scalar). -/

/-- The `L = 2` extra unit locus: `det P00 ≠ 0 ∧ det W ≠ 0`. -/
def l2ExtraUnitSetSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) :
    Set (DeepestSplit H r (deepestNGauge H r)) :=
  {q | (l2P00 H r hr hL hL2 q).det ≠ 0 ∧ (l2W H r hr hL hL2 q).det ≠ 0}

/-- A ball at `0` inside the `L = 2` extra locus (`P00`, `W` det continuous at `0`, `= 1` there). -/
theorem exists_ball_subset_l2ExtraUnitSetSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) :
    ∃ ε > 0, Metric.ball (0 : DeepestSplit H r (deepestNGauge H r)) ε
      ⊆ l2ExtraUnitSetSplit H r hr hL hL2 := by
  have hP00cont : ContinuousAt (fun q => (l2P00 H r hr hL hL2 q).det) 0 := by
    refine (contDiffAt_matrix_det_of_entries (fun a b => ?_)).continuousAt
    have hpe : (fun q => l2P00 H r hr hL hL2 q a b)
        = fun q => (l2A0 H r hr hL q * l2A1 H r hr hL q) a b
          + (l2Y0 H r hr hL hL2 q * l2Z1 H r hr hL q) a b := by
      funext q; rw [l2P00, Matrix.add_apply]
    rw [hpe]
    exact (contDiffAt_matrix_mul_entry (fun a' k => (contDiff_l2A0_entry H r hr hL a' k).contDiffAt)
        (fun k b' => (contDiff_l2A1_entry H r hr hL k b').contDiffAt) a b).add
      (contDiffAt_matrix_mul_entry (fun a' k => (contDiff_l2Y0_entry H r hr hL hL2 a' k).contDiffAt)
        (fun k b' => (contDiff_l2Z1_entry H r hr hL k b').contDiffAt) a b)
  have hWcont : ContinuousAt (fun q => (l2W H r hr hL hL2 q).det) 0 :=
    (contDiffAt_matrix_det_of_entries
      (fun a b => contDiffAt_l2W_entry H r hr hL hL2 a b)).continuousAt
  have hP00ne : (l2P00 H r hr hL hL2 0).det ≠ 0 := by
    rw [l2P00_zero, Matrix.det_one]; exact one_ne_zero
  have hWne : (l2W H r hr hL hL2 0).det ≠ 0 := by
    rw [l2W_zero, Matrix.det_one]; exact one_ne_zero
  have hnbhd : {q | (l2P00 H r hr hL hL2 q).det ≠ 0 ∧ (l2W H r hr hL hL2 q).det ≠ 0}
      ∈ nhds (0 : DeepestSplit H r (deepestNGauge H r)) :=
    Filter.inter_mem (hP00cont.preimage_mem_nhds (isOpen_ne.mem_nhds hP00ne))
      (hWcont.preimage_mem_nhds (isOpen_ne.mem_nhds hWne))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  exact ⟨ε, hε, hball⟩

/-- The chosen `L = 2` extra radius (positive, ball ⊆ extra locus). -/
noncomputable def l2ExtraRadius (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) : ℝ :=
  (exists_ball_subset_l2ExtraUnitSetSplit H r hr hL hL2).choose

theorem l2ExtraRadius_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) :
    0 < l2ExtraRadius H r hr hL hL2 :=
  (exists_ball_subset_l2ExtraUnitSetSplit H r hr hL hL2).choose_spec.1

theorem ball_l2ExtraRadius_subset (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) :
    Metric.ball (0 : DeepestSplit H r (deepestNGauge H r)) (l2ExtraRadius H r hr hL hL2)
      ⊆ l2ExtraUnitSetSplit H r hr hL hL2 :=
  (exists_ball_subset_l2ExtraUnitSetSplit H r hr hL hL2).choose_spec.2

/-- The joint unit radius: `unitRadius ⊓ (extra)` at `L = 2`, `unitRadius` otherwise. -/
noncomputable def jointUnitRadiusSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : ℝ :=
  if h : L = 2 then min (unitRadius H r hr hL) (l2ExtraRadius H r hr hL h)
  else unitRadius H r hr hL

theorem jointUnitRadiusSplit_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    0 < jointUnitRadiusSplit H r hr hL := by
  unfold jointUnitRadiusSplit
  by_cases h : L = 2
  · rw [dif_pos h]
    exact lt_min (unitRadius_pos H r hr hL) (l2ExtraRadius_pos H r hr hL h)
  · rw [dif_neg h]; exact unitRadius_pos H r hr hL

/-- `jointUnitRadiusSplit ≤ unitRadius` (the reg-read locus radius). -/
theorem jointUnitRadiusSplit_le_unitRadius (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    jointUnitRadiusSplit H r hr hL ≤ unitRadius H r hr hL := by
  unfold jointUnitRadiusSplit
  by_cases h : L = 2
  · rw [dif_pos h]; exact min_le_left _ _
  · rw [dif_neg h]

/-- At `L = 2`, `jointUnitRadiusSplit ≤ l2ExtraRadius`. -/
theorem jointUnitRadiusSplit_le_l2ExtraRadius (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) :
    jointUnitRadiusSplit H r hr hL ≤ l2ExtraRadius H r hr hL hL2 := by
  unfold jointUnitRadiusSplit; rw [dif_pos hL2]; exact min_le_right _ _

/-- A fresh `ContDiffBump` at `0` on the FULL split `DeepestSplit`, keyed to the JOINT unit radius
(`jointUnitRadiusSplit/4`, `/2`), so its support sits in the joint unit locus (`1 + readX_s`, `P00`,
`W` all invertible) — exactly where the raw correction `δ` is `ContDiffAt` (S2). -/
noncomputable def cutoffBumpSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)) where
  rIn := jointUnitRadiusSplit H r hr hL / 4
  rOut := jointUnitRadiusSplit H r hr hL / 2
  rIn_pos := by have := jointUnitRadiusSplit_pos H r hr hL; linarith
  rIn_lt_rOut := by have := jointUnitRadiusSplit_pos H r hr hL; linarith

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

/-! ### S2b — composite ContDiffAt at a support point + the joint correction smoothness leaf -/

-- General-point inverse-entry ContDiffAt (det hyp at q).
theorem contDiffAt_l2A0inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) (hdet : (l2A0 H r hr hL q).det ≠ 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2A0 H r hr hL q')⁻¹ i j) q :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A0_entry H r hr hL a b).contDiffAt) hdet i j

theorem contDiffAt_l2A1inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) (hdet : (l2A1 H r hr hL q).det ≠ 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2A1 H r hr hL q')⁻¹ i j) q :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => (contDiff_l2A1_entry H r hr hL a b).contDiffAt) hdet i j

theorem contDiffAt_l2P00inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hdet : (l2P00 H r hr hL hL2 q).det ≠ 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2P00 H r hr hL hL2 q')⁻¹ i j) q := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at (fun a b => ?_) hdet i j
  have hpe : (fun q' => l2P00 H r hr hL hL2 q' a b)
      = fun q' => (l2A0 H r hr hL q' * l2A1 H r hr hL q') a b
        + (l2Y0 H r hr hL hL2 q' * l2Z1 H r hr hL q') a b := by
    funext q'; rw [l2P00, Matrix.add_apply]
  rw [hpe]
  exact (contDiffAt_matrix_mul_entry (fun a' k => (contDiff_l2A0_entry H r hr hL a' k).contDiffAt)
      (fun k b' => (contDiff_l2A1_entry H r hr hL k b').contDiffAt) a b).add
    (contDiffAt_matrix_mul_entry (fun a' k => (contDiff_l2Y0_entry H r hr hL hL2 a' k).contDiffAt)
      (fun k b' => (contDiff_l2Z1_entry H r hr hL k b').contDiffAt) a b)

-- l2W entries ContDiffAt at q (need det A0, A1 ≠ 0).
theorem contDiffAt_l2W_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2W H r hr hL hL2 q' i j) q := by
  have heq : (fun q' => l2W H r hr hL hL2 q' i j)
      = fun q' => (1 : Matrix _ _ ℝ) i j + l2R H r hr hL hL2 q' i j := by
    funext q'; rw [l2W, Matrix.add_apply]
  rw [heq]
  refine contDiffAt_const.add ?_
  -- R = Z1*A1⁻¹*A0⁻¹*Y0; entries ContDiffAt at q.
  have hRe : (fun q' => l2R H r hr hL hL2 q' i j)
      = fun q' => (l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * (l2A0 H r hr hL q')⁻¹
          * l2Y0 H r hr hL hL2 q') i j := by funext q'; rw [l2R]
  rw [hRe]
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * (l2A0 H r hr hL q')⁻¹) ?_
    (fun k b => (contDiff_l2Y0_entry H r hr hL hL2 k b).contDiffAt) i j
  intro a k
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹) ?_
    (fun k' b' => contDiffAt_l2A0inv_entry_at H r hr hL q hA0 k' b') a k
  intro a' k'
  exact contDiffAt_matrix_mul_entry (fun a'' k'' => (contDiff_l2Z1_entry H r hr hL a'' k'').contDiffAt)
    (fun k'' b'' => contDiffAt_l2A1inv_entry_at H r hr hL q hA1 k'' b'') a' k'

-- l2Winv entries ContDiffAt at q (need det W ≠ 0).
theorem contDiffAt_l2Winv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (hW : (l2W H r hr hL hL2 q).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => (l2W H r hr hL hL2 q')⁻¹ i j) q :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => contDiffAt_l2W_entry_at H r hr hL hL2 q hA0 hA1 a b) hW i j

-- l2S1 entries ContDiffAt at q (need det A1 ≠ 0).
theorem contDiffAt_l2S1_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2S1 H r hr hL hL2 q' i j) q := by
  have heq : (fun q' => l2S1 H r hr hL hL2 q' i j)
      = fun q' => l2T1 H r hr hL q' i j
          - (l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * l2Y1 H r hr hL q') i j := by
    funext q'; rw [l2S1, Matrix.sub_apply]
  rw [heq]
  refine (contDiff_l2T1_entry H r hr hL i j).contDiffAt.sub ?_
  refine contDiffAt_matrix_mul_entry (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹) ?_
    (fun k b => (contDiff_l2Y1_entry H r hr hL k b).contDiffAt) i j
  intro a k
  exact contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
    (fun k' b' => contDiffAt_l2A1inv_entry_at H r hr hL q hA1 k' b') a k

-- l2Br entries ContDiffAt at q (need det A0, A1, P00 ≠ 0).
theorem contDiffAt_l2Br_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2 q).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2Br H r hr hL hL2 q' i j) q := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' : DeepestSplit H r (deepestNGauge H r) =>
        (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2 q')
          * l2S1 H r hr hL hL2 q') i j) q := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
        (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2 q') ?_
      (fun k b => contDiffAt_l2S1_entry_at H r hr hL hL2 q hA1 k b) i j
    intro a k
    have hsub : (fun q' => ((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
          (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2 q') a k)
        = fun q' => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) a k - l2K H r hr hL hL2 q' a k := by
      funext q'; rw [Matrix.sub_apply]
    rw [hsub]
    refine contDiffAt_const.sub ?_
    have hKeq : (fun q' => l2K H r hr hL hL2 q' a k)
        = fun q' => (l2Z1 H r hr hL q' * (l2P00 H r hr hL hL2 q')⁻¹ * l2Y0 H r hr hL hL2 q') a k := by
      funext q'; rw [l2K]
    rw [hKeq]
    refine contDiffAt_matrix_mul_entry (A := fun q' => l2Z1 H r hr hL q' * (l2P00 H r hr hL hL2 q')⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0_entry H r hr hL hL2 k' b').contDiffAt) a k
    intro a' k'
    exact contDiffAt_matrix_mul_entry (fun a'' k'' => (contDiff_l2Z1_entry H r hr hL a'' k'').contDiffAt)
      (fun k'' b'' => contDiffAt_l2P00inv_entry_at H r hr hL hL2 q hP00 k'' b'') a' k'
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * l2Y1 H r hr hL q') i j) q := by
    refine contDiffAt_matrix_mul_entry (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹) ?_
      (fun k b => (contDiff_l2Y1_entry H r hr hL k b).contDiffAt) i j
    intro a k
    exact contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' b' => contDiffAt_l2A1inv_entry_at H r hr hL q hA1 k' b') a k
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' : DeepestSplit H r (deepestNGauge H r) =>
        (l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * (l2A0 H r hr hL q')⁻¹
          * l2Y0 H r hr hL hL2 q' * l2T1 H r hr hL q') i j) q := by
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * (l2A0 H r hr hL q')⁻¹
          * l2Y0 H r hr hL hL2 q') ?_
      (fun k b => (contDiff_l2T1_entry H r hr hL k b).contDiffAt) i j
    intro a k
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * (l2A0 H r hr hL q')⁻¹) ?_
      (fun k' b' => (contDiff_l2Y0_entry H r hr hL hL2 k' b').contDiffAt) a k
    intro a' k'
    refine contDiffAt_matrix_mul_entry
      (A := fun q' => l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹) ?_
      (fun k'' b'' => contDiffAt_l2A0inv_entry_at H r hr hL q hA0 k'' b'') a' k'
    intro a'' k''
    exact contDiffAt_matrix_mul_entry (fun a3 k3 => (contDiff_l2Z1_entry H r hr hL a3 k3).contDiffAt)
      (fun k3 b3 => contDiffAt_l2A1inv_entry_at H r hr hL q hA1 k3 b3) a'' k''
  have heq : (fun q' => l2Br H r hr hL hL2 q' i j)
      = fun q' => (((1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) - l2K H r hr hL hL2 q')
          * l2S1 H r hr hL hL2 q') i j
          + (l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * l2Y1 H r hr hL q') i j
          + (l2Z1 H r hr hL q' * (l2A1 H r hr hL q')⁻¹ * (l2A0 H r hr hL q')⁻¹ * l2Y0 H r hr hL hL2 q'
              * l2T1 H r hr hL q') i j := by
    funext q'; rw [l2Br, Matrix.add_apply, Matrix.add_apply]
  rw [heq]
  exact (h1.add h2).add h3

-- l2T1p entries ContDiffAt at q (need all four dets).
theorem contDiffAt_l2T1p_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2 q).det ≠ 0) (hW : (l2W H r hr hL hL2 q).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2T1p H r hr hL hL2 q' i j) q := by
  have heq : (fun q' => l2T1p H r hr hL hL2 q' i j)
      = fun q' => ((l2W H r hr hL hL2 q')⁻¹ * l2Br H r hr hL hL2 q') i j := by
    funext q'; rw [l2T1p_eq]
  rw [heq]
  exact contDiffAt_matrix_mul_entry
    (fun a k => contDiffAt_l2Winv_entry_at H r hr hL hL2 q hA0 hA1 hW a k)
    (fun k b => contDiffAt_l2Br_entry_at H r hr hL hL2 q hA0 hA1 hP00 k b) i j

-- l2Y1p entries ContDiffAt at q.
theorem contDiffAt_l2Y1p_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2 q).det ≠ 0) (hW : (l2W H r hr hL hL2 q).det ≠ 0)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q' => l2Y1p H r hr hL hL2 q' i j) q := by
  -- l2Y1p = Y1 + A0⁻¹*Y0*(T1 - T1'); entries ContDiffAt.
  have heq : (fun q' => l2Y1p H r hr hL hL2 q' i j)
      = fun q' => l2Y1 H r hr hL q' i j
          + ((l2A0 H r hr hL q')⁻¹ * l2Y0 H r hr hL hL2 q'
              * (l2T1 H r hr hL q' - l2T1p H r hr hL hL2 q')) i j := by
    funext q'; rw [l2Y1p, Matrix.add_apply]
  rw [heq]
  refine (contDiff_l2Y1_entry H r hr hL i j).contDiffAt.add ?_
  refine contDiffAt_matrix_mul_entry
    (A := fun q' => (l2A0 H r hr hL q')⁻¹ * l2Y0 H r hr hL hL2 q') ?_
    (fun k b => ?_) i j
  · intro a k
    exact contDiffAt_matrix_mul_entry (fun a' k' => contDiffAt_l2A0inv_entry_at H r hr hL q hA0 a' k')
      (fun k' b' => (contDiff_l2Y0_entry H r hr hL hL2 k' b').contDiffAt) a k
  · -- (T1 - T1') entry ContDiffAt.
    have : (fun q' => (l2T1 H r hr hL q' - l2T1p H r hr hL hL2 q') k b)
        = fun q' => l2T1 H r hr hL q' k b - l2T1p H r hr hL hL2 q' k b := by
      funext q'; rw [Matrix.sub_apply]
    rw [this]
    exact (contDiff_l2T1_entry H r hr hL k b).contDiffAt.sub
      (contDiffAt_l2T1p_entry_at H r hr hL hL2 q hA0 hA1 hP00 hW k b)

-- l2CoreΔTuple encoded ContDiffAt at q (flat-codomain descent).
theorem contDiffAt_paramsEquivFlatCLE_l2CoreΔTuple_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2 q).det ≠ 0) (hW : (l2W H r hr hL hL2 q).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q')) q := by
  refine contDiffAt_pi' (fun k => ?_)
  set d := (Fintype.equivFin (FlatIdx (deepestM H r))).symm k with hd
  have hcoord : (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q') k)
      = fun q' => l2CoreΔTuple H r hr hL hL2 q' d.1.1 d.1.2 d.2 := by
    funext q'
    rw [show (⇑(paramsEquivFlatCLE (deepestM H r)) : Params (deepestM H r) → _)
        = ⇑(paramsEquivFlat (deepestM H r)) from paramsEquivFlatCLE_coe (deepestM H r)]
    rfl
  rw [hcoord]
  -- l2CoreΔTuple = update 0 last (T1'-T1); entry is (T1'-T1) at last, 0 else.
  obtain ⟨⟨s, i⟩, j⟩ := d
  rcases eq_or_ne s (lastLayer hL) with hs | hs
  · subst hs
    have hentry : (fun q' => l2CoreΔTuple H r hr hL hL2 q' (lastLayer hL) i j)
        = fun q' => l2T1p H r hr hL hL2 q' i j - l2T1 H r hr hL q' i j := by
      funext q'; rw [l2CoreΔTuple, Function.update_self, Matrix.sub_apply]
    rw [hentry]
    exact (contDiffAt_l2T1p_entry_at H r hr hL hL2 q hA0 hA1 hP00 hW i j).sub
      (contDiff_l2T1_entry H r hr hL i j).contDiffAt
  · have hentry : (fun q' => l2CoreΔTuple H r hr hL hL2 q' s i j) = fun _ => (0 : ℝ) := by
      funext q'; rw [l2CoreΔTuple, Function.update_of_ne hs]; rfl
    rw [hentry]; exact contDiffAt_const

-- l2GaugeΔ ContDiffAt at q.
theorem contDiffAt_l2GaugeΔ_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL q).det ≠ 0) (hA1 : (l2A1 H r hr hL q).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2 q).det ≠ 0) (hW : (l2W H r hr hL hL2 q).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (l2GaugeΔ H r hr hL hL2) q := by
  refine contDiffAt_pi' (fun idx => ?_)
  obtain ⟨s, rest⟩ := idx
  rcases rest with (rest | rest)
  · rcases rest with rest | ⟨i, j⟩
    · have h0 : (fun q' => l2GaugeΔ H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inl rest)⟩)
          = fun _ => (0 : ℝ) := by funext q'; simp only [l2GaugeΔ, l2g', Pi.sub_apply]; ring
      rw [h0]; exact contDiffAt_const
    · by_cases h : s = lastLayer hL
      · subst h
        have hY : (fun q' => l2GaugeΔ H r hr hL hL2 q' ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩)
            = fun q' => (l2Y1p H r hr hL hL2 q' - l2Y1 H r hr hL q') i j := by
          funext q'
          have hg : regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2)
              ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩ = l2Y1 H r hr hL q' i j := rfl
          simp only [l2GaugeΔ, l2g', Pi.sub_apply, dif_pos, hg, Matrix.sub_apply]
        rw [hY]
        exact (contDiffAt_l2Y1p_entry_at H r hr hL hL2 q hA0 hA1 hP00 hW i j).sub
          (contDiff_l2Y1_entry H r hr hL i j).contDiffAt
      · have h0 : (fun q' => l2GaugeΔ H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inr (i, j))⟩)
            = fun _ => (0 : ℝ) := by
          funext q'; simp only [l2GaugeΔ, l2g', Pi.sub_apply, dif_neg h]; ring
        rw [h0]; exact contDiffAt_const
  · have h0 : (fun q' => l2GaugeΔ H r hr hL hL2 q' ⟨s, Sum.inr rest⟩) = fun _ => (0 : ℝ) := by
      funext q'; simp only [l2GaugeΔ, l2g', Pi.sub_apply]; ring
    rw [h0]; exact contDiffAt_const

-- l2A0/l2A1 det ≠ 0 from unitSet membership of the gauge slot.
theorem l2A0_det_ne_of_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) (hq : (q.1, q.2.2) ∈ unitSet H r hr hL) :
    (l2A0 H r hr hL q).det ≠ 0 := hq (⟨0, by omega⟩ : Fin L)

theorem l2A1_det_ne_of_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) (hq : (q.1, q.2.2) ∈ unitSet H r hr hL) :
    (l2A1 H r hr hL q).det ≠ 0 := hq (lastLayer hL)

-- tsupport(cutoffBumpSplit) ⊆ {q | (q.1,q.2.2) ∈ unitSet} (the reg-read locus).
theorem tsupport_cutoffBumpSplit_subset_unitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    tsupport (fun q => ((cutoffBumpSplit H r hr hL) q : ℝ))
      ⊆ {q | (q.1, q.2.2) ∈ unitSet H r hr hL} := by
  rw [(cutoffBumpSplit H r hr hL).tsupport_eq]
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right] at hq
  -- ‖(q.1,q.2.2)‖ ≤ ‖q‖ ≤ joint/2 < joint ≤ unitRadius.
  have hpos := jointUnitRadiusSplit_pos H r hr hL
  have hle := jointUnitRadiusSplit_le_unitRadius H r hr hL
  have hrOut : (cutoffBumpSplit H r hr hL).rOut = jointUnitRadiusSplit H r hr hL / 2 := rfl
  rw [hrOut] at hq
  have hproj : ‖(q.1, q.2.2)‖ ≤ ‖q‖ := by
    rw [Prod.norm_def (q.1, q.2.2), Prod.norm_def q, Prod.norm_def q.2]
    exact max_le (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  show (q.1, q.2.2) ∈ unitSet H r hr hL
  apply ball_unitRadius_subset H r hr hL
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖(q.1, q.2.2)‖ ≤ ‖q‖ := hproj
    _ ≤ jointUnitRadiusSplit H r hr hL / 2 := hq
    _ < unitRadius H r hr hL := by linarith

-- tsupport(cutoffBumpSplit) ⊆ l2ExtraUnitSetSplit (L=2 case).
theorem tsupport_cutoffBumpSplit_subset_l2Extra (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2) :
    tsupport (fun q => ((cutoffBumpSplit H r hr hL) q : ℝ))
      ⊆ l2ExtraUnitSetSplit H r hr hL hL2 := by
  rw [(cutoffBumpSplit H r hr hL).tsupport_eq]
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right] at hq
  have hpos := jointUnitRadiusSplit_pos H r hr hL
  have hle := jointUnitRadiusSplit_le_l2ExtraRadius H r hr hL hL2
  have hrOut : (cutoffBumpSplit H r hr hL).rOut = jointUnitRadiusSplit H r hr hL / 2 := rfl
  rw [hrOut] at hq
  apply ball_l2ExtraRadius_subset H r hr hL hL2
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖q‖ ≤ jointUnitRadiusSplit H r hr hL / 2 := hq
    _ < l2ExtraRadius H r hr hL hL2 := by linarith

-- S2 leaf: ContDiffAt of the joint correction on the cutoff support.
theorem contDiffAt_psiSplitDeltaL2_of_mem_tsupport_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hq : q ∈ tsupport (fun y => ((cutoffBumpSplit H r hr hL) y : ℝ))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (psiSplitDeltaL2 H r hr hL) q := by
  -- Extract the four det conditions at q from the support membership.
  have hunit : (q.1, q.2.2) ∈ unitSet H r hr hL :=
    tsupport_cutoffBumpSplit_subset_unitSet H r hr hL hq
  have hextra := tsupport_cutoffBumpSplit_subset_l2Extra H r hr hL hL2 hq
  have hA0 := l2A0_det_ne_of_unitSet H r hr hL q hunit
  have hA1 := l2A1_det_ne_of_unitSet H r hr hL q hunit
  have hP00 : (l2P00 H r hr hL hL2 q).det ≠ 0 := hextra.1
  have hW : (l2W H r hr hL hL2 q).det ≠ 0 := hextra.2
  -- psiSplitDeltaL2 = encoded payloads (dif_pos hL2 + lens decomposition).
  have heq : psiSplitDeltaL2 H r hr hL
      = fun q' => (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')).1,
          (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q'),
            ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')).2)) := by
    funext q'
    rw [psiSplitDeltaL2, psiSplitRawL2, dif_pos hL2]
    exact psiSplitDeltaL2Core_eq_payload H r hr hL hL2 q'
  rw [heq]
  -- The reg/spec encode is ContDiffAt at q (CLE.contDiff ∘ l2GaugeΔ).
  have hrg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' => (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')) q :=
    (regGaugeSlotCLE H r hr hL).symm.contDiff.contDiffAt.comp q
      (contDiffAt_l2GaugeΔ_at H r hr hL hL2 q hA0 hA1 hP00 hW)
  -- The core encode is ContDiffAt at q.
  have hcore : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q')) q :=
    contDiffAt_paramsEquivFlatCLE_l2CoreΔTuple_at H r hr hL hL2 q hA0 hA1 hP00 hW
  -- Assemble the prod.
  exact (contDiffAt_fst.comp q hrg).prodMk ((hcore).prodMk (contDiffAt_snd.comp q hrg))

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
  · -- **L = 2: the composite-inverse ContDiff.** The correction `δ = psiSplitRawL2Core − id` carries
    -- `W⁻¹`, `P00⁻¹`, `A_s⁻¹`, smooth on the joint unit locus (`tsupport (cutoffBumpSplit) ⊆ {all dets
    -- ≠ 0}`) — the re-keyed bump (S2a) + the composite ContDiffAt-at-support-point chain (S2b).
    exact contDiffAt_psiSplitDeltaL2_of_mem_tsupport_L2 H r hr hL hL2 q _hq
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

/-! ### S4e — the gauge payload deriv-0 + the CLE-reduction (joint correction strict-deriv 0) -/

-- l2Y1p - l2Y1 = A0⁻¹ * Y0 * (T1 - T1').
theorem l2Y1p_sub_Y1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q
      = (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q
          * (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) := by
  rw [l2Y1p]; abel

-- (T1 - T1') entry value 0 + strict-deriv 0 at origin.
theorem hasStrictFDerivAt_l2T1_sub_T1p_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt (fun q => (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have hneg := (hasStrictFDerivAt_l2T1p_sub_T1_entry_zero H r hr hL hL2eq i j).neg
  simp only [neg_zero] at hneg
  refine hneg.congr_of_eventuallyEq ?_
  filter_upwards with q
  simp only [Pi.neg_apply, Matrix.sub_apply]; ring

theorem l2T1p_sub_T1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2T1p H r hr hL hL2eq 0 - l2T1 H r hr hL 0 = 0 := by
  rw [l2T1p_sub_T1, l2Br_sub_T1, l2K_zero, l2R_zero]
  simp [Matrix.zero_mul, l2W_zero]

theorem l2T1_sub_T1p_zero_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    (l2T1 H r hr hL 0 - l2T1p H r hr hL hL2eq 0) i j = 0 := by
  have h0 := l2T1p_sub_T1_zero H r hr hL hL2eq
  have : l2T1 H r hr hL 0 - l2T1p H r hr hL hL2eq 0 = 0 := by
    rw [← neg_sub, h0, neg_zero]
  rw [this]; rfl

-- A0⁻¹*Y0 entries ContDiffAt at 0.
theorem contDiffAt_l2A0invY0_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => ((l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q) i j) 0 :=
  contDiffAt_matrix_mul_entry (fun a k => contDiffAt_l2A0inv_entry H r hr hL a k)
    (fun k b => (contDiff_l2Y0_entry H r hr hL hL2eq k b).contDiffAt) i j

-- (l2Y1p - l2Y1) entry strict-deriv-0 (= A0⁻¹*Y0*(T1-T1'), right factor (T1-T1') value+deriv 0).
theorem hasStrictFDerivAt_l2Y1p_sub_Y1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt (fun q => (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  have heq : (fun q => (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j)
      = fun q => (((l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q)
          * (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q)) i j := by
    funext q; rw [l2Y1p_sub_Y1, Matrix.mul_assoc]
  rw [heq]
  exact hasStrictFDerivAt_matrix_mul_entry_of_right_zero i j
    (fun k => contDiffAt_l2A0invY0_entry H r hr hL hL2eq i k)
    (fun k => hasStrictFDerivAt_l2T1_sub_T1p_entry_zero H r hr hL hL2eq k j)
    (fun k => l2T1_sub_T1p_zero_entry H r hr hL hL2eq k j)

-- The gauge payload l2GaugeΔ has strict-deriv 0 at 0 (only last-layer Y-tags nonzero).
theorem hasStrictFDerivAt_l2GaugeΔ_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt (l2GaugeΔ H r hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (RegGaugeIdx H r → ℝ)) 0 := by
  refine hasStrictFDerivAt_pi'.2 (fun idx => ?_)
  rw [ContinuousLinearMap.comp_zero]
  -- l2GaugeΔ q idx = l2g' q idx - g q idx; by cases on idx (only last Y-tag nonzero).
  obtain ⟨s, rest⟩ := idx
  rcases rest with (rest | rest)
  · rcases rest with rest | ⟨i, j⟩
    · -- X-tag: l2GaugeΔ = 0.
      have h0 : (fun q => l2GaugeΔ H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inl rest)⟩) = fun _ => (0 : ℝ) := by
        funext q; simp only [l2GaugeΔ, l2g', Pi.sub_apply]; ring
      rw [h0]; exact hasStrictFDerivAt_const _ _
    · -- Y-tag: 0 off last, (l2Y1p - l2Y1) i (cast j) at last.
      by_cases h : s = lastLayer hL
      · subst h
        have hY : (fun q => l2GaugeΔ H r hr hL hL2eq q ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩)
            = fun q => (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j := by
          funext q
          have hg : regGaugeSlotEquiv H r hr hL (q.1, q.2.2)
              ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩ = l2Y1 H r hr hL q i j := rfl
          simp only [l2GaugeΔ, l2g', Pi.sub_apply, dif_pos, hg, Matrix.sub_apply]
        rw [hY]; exact hasStrictFDerivAt_l2Y1p_sub_Y1_entry_zero H r hr hL hL2eq i j
      · have h0 : (fun q => l2GaugeΔ H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩)
            = fun _ => (0 : ℝ) := by
          funext q; simp only [l2GaugeΔ, l2g', Pi.sub_apply, dif_neg h]; ring
        rw [h0]; exact hasStrictFDerivAt_const _ _
  · -- Z-tag: l2GaugeΔ = 0.
    have h0 : (fun q => l2GaugeΔ H r hr hL hL2eq q ⟨s, Sum.inr rest⟩) = fun _ => (0 : ℝ) := by
      funext q; simp only [l2GaugeΔ, l2g', Pi.sub_apply]; ring
    rw [h0]; exact hasStrictFDerivAt_const _ _

-- The joint correction psiSplitRawL2Core - id has strict-deriv 0 at 0 (CLE-reduction).
theorem hasStrictFDerivAt_psiSplitDeltaL2Core_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt (fun q => psiSplitRawL2Core H r hr hL hL2eq q - q)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
  have heq : (fun q => psiSplitRawL2Core H r hr hL hL2eq q - q)
      = fun q => (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)).1,
          (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q),
            ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)).2)) := by
    funext q; exact psiSplitDeltaL2Core_eq_payload H r hr hL hL2eq q
  rw [heq]
  -- The reg/spec encode regGaugeSlotCLE.symm ∘ l2GaugeΔ has deriv 0.
  have hrg : HasStrictFDerivAt
      (fun q => (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
        ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))) 0 := by
    have hcle := ((regGaugeSlotCLE H r hr hL).symm.toContinuousLinearMap).hasStrictFDerivAt
      (x := l2GaugeΔ H r hr hL hL2eq 0)
    have hcomp := hcle.comp 0 (hasStrictFDerivAt_l2GaugeΔ_zero H r hr hL hL2eq)
    simpa using hcomp
  -- The core encode paramsEquivFlatCLE ∘ l2CoreΔTuple has deriv 0 (landed directly).
  have hcore := hasStrictFDerivAt_paramsEquivFlatCLE_l2CoreΔTuple_zero H r hr hL hL2eq
  have h1 : HasStrictFDerivAt
      (fun q => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)).1)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
    have := (ContinuousLinearMap.fst ℝ (Fin (deepestNReg H r) → ℝ)
      (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp 0 hrg
    simpa using this
  have h3 : HasStrictFDerivAt
      (fun q => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q)).2)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (ContinuousLinearMap.snd ℝ (Fin (deepestNReg H r) → ℝ)
      (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp 0 hrg
    simpa using this
  exact h1.prodMk (hcore.prodMk h3)

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
  · -- **L = 2: the certified O(read²) deriv-vanishing.** `psiSplitDeltaL2 = psiSplitRawL2Core − id`
    -- (dif_pos), whose strict derivative at `0` is `0` by the lens-decomposition CLE-reduction
    -- (`hasStrictFDerivAt_psiSplitDeltaL2Core_zero`): the two decoded payloads (`l2CoreΔTuple`,
    -- `l2GaugeΔ`) are each `O(read²)` (`T1'−T1` normalized via `(W⁻¹−1)·Br + (−K·S1 + R·T1)`;
    -- `Y1'−Y1 = A0⁻¹·Y0·(T1−T1')`), so their CLE encodings have strict derivative `0`.
    have heq : psiSplitDeltaL2 H r hr hL
        = fun q => psiSplitRawL2Core H r hr hL hL2 q - q := by
      funext q; simp only [psiSplitDeltaL2, psiSplitRawL2, dif_pos hL2]
    rw [heq]
    exact hasStrictFDerivAt_psiSplitDeltaL2Core_zero H r hr hL hL2
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

/-- **The absorbed last-layer core IS `(1 − K)·S1`** (the sub-4 keystone, on the inner ball where
`det W ≠ 0`). The last-layer Schur-shifted core read off `psiSplitRawL2Core q` — `T1' − Z1·A1⁻¹·Y1'`
— collapses to `(1 − K)·S1`: substituting `Y1' = Y1 + A0⁻¹·Y0·(T1 − T1')` and `T1' = W⁻¹·Br`,
the `W·W⁻¹ = 1` cancel (from `det W ≠ 0`) turns `(1 + R)·T1' = W·W⁻¹·Br = Br`, and `Br`'s definition
unwinds to `(1 − K)·S1` after the `Z1·A1⁻¹·Y1` and `R·T1` terms cancel. This is the matrix identity the
absorbed-core energy chain (`deepestCoreF_coreAbsorb_eq_prodSchur` → LDU) consumes. -/
theorem l2T1p_sub_Z1A1invY1p_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hW : (l2W H r hr hL hL2eq q).det ≠ 0) :
    l2T1p H r hr hL hL2eq q
        - l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1p H r hr hL hL2eq q
      = (1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL hL2eq q := by
  -- Abbreviations matching the `l2*` defs.
  set Z1 := l2Z1 H r hr hL q with hZ1
  set A1i := (l2A1 H r hr hL q)⁻¹ with hA1i
  set A0i := (l2A0 H r hr hL q)⁻¹ with hA0i
  set Y0 := l2Y0 H r hr hL hL2eq q with hY0
  set Y1 := l2Y1 H r hr hL q with hY1
  set T1 := l2T1 H r hr hL q with hT1
  set T1' := l2T1p H r hr hL hL2eq q with hT1'
  set K := l2K H r hr hL hL2eq q with hK
  set S1 := l2S1 H r hr hL hL2eq q with hS1
  -- `R = Z1·A1⁻¹·A0⁻¹·Y0`, `W = 1 + R`, and the inner-ball cancel `W·W⁻¹ = 1`.
  have hRdef : l2R H r hr hL hL2eq q = Z1 * A1i * A0i * Y0 := rfl
  -- `Y1' = Y1 + A0⁻¹·Y0·(T1 − T1')`.
  have hY1p : l2Y1p H r hr hL hL2eq q = Y1 + A0i * Y0 * (T1 - T1') := rfl
  -- `Z1·A1⁻¹·Y1' = Z1·A1⁻¹·Y1 + R·(T1 − T1')`.
  have hZAY1p : Z1 * A1i * l2Y1p H r hr hL hL2eq q
      = Z1 * A1i * Y1 + l2R H r hr hL hL2eq q * (T1 - T1') := by
    rw [hY1p, Matrix.mul_add, hRdef]
    simp only [Matrix.mul_assoc]
  -- `W·T1' = Br` (the `W·W⁻¹ = 1` cancel).
  have hWWi : l2W H r hr hL hL2eq q * (l2W H r hr hL hL2eq q)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Ne.isUnit hW)
  have hWT1' : l2W H r hr hL hL2eq q * T1' = l2Br H r hr hL hL2eq q := by
    rw [hT1', l2T1p_eq, ← Matrix.mul_assoc, hWWi, Matrix.one_mul]
  -- Assemble: T1' − Z1·A1⁻¹·Y1' = (1+R)·T1' − Z1·A1⁻¹·Y1 − R·T1 = W·T1' − … = Br − … = (1−K)·S1.
  rw [hZAY1p, hRdef] at *
  -- Reduce the LHS to `Br − Z1·A1⁻¹·Y1 − (Z1·A1⁻¹·A0⁻¹·Y0)·T1` using `(1+R)·T1' = W·T1' = Br`.
  have hWdef : l2W H r hr hL hL2eq q = 1 + Z1 * A1i * A0i * Y0 := rfl
  have key : T1' - (Z1 * A1i * Y1 + Z1 * A1i * A0i * Y0 * (T1 - T1'))
      = l2Br H r hr hL hL2eq q - Z1 * A1i * Y1 - Z1 * A1i * A0i * Y0 * T1 := by
    rw [← hWT1', hWdef]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub]
    abel
  rw [key, l2Br]
  -- `Br = (1−K)·S1 + Z1·A1⁻¹·Y1 + (Z1·A1⁻¹·A0⁻¹·Y0)·T1`; the last two cancel.
  rw [Matrix.mul_assoc (Z1 * A1i * A0i) Y0 T1]
  abel

/-! ### S6p — the L=2 reduced-product two-factor unfold (the sub-4 cast wall)

At `L = 2` the reduced layer product `prod (deepestM H r) C` (a left-associated prefix fold over
`Fin 3`) collapses to `C firstLayer · C lastLayer`, transported to the running widths by the layer
`finCongr` reindexes. This is the `prod_eq_prodAux_mul_last` (m = 1) front-peel followed by the
`prodAux 1 = prodAux 0 · layer0 = 1 · layer0` base, with the width-equalities at `L = 2` discharged by
`rfl` (`deepestM s = H s − r`). It is what turns the absorbed-core energy `frobSq(prod(deepestM) C)`
into `frobSq(C₀ · C₁)`, the form the `prod_absorbed_eq_schur_ldu` LDU consumes. -/

/-- **The L=2 reduced product is the two-factor product of the layer cores** (running-width reindexes
from `prod_eq_prodAux_mul_last` at `m = 1`; the prefix `prodAux 1` peels to `1 · reindex(C 0)`). The
reindexes carry the layer-index width casts `(0:Fin 2).castSucc = 0`, `(0:Fin 2).succ = 1`,
`(1:Fin 2).castSucc = 1`, `(1:Fin 2).succ = Fin.last 2`. -/
theorem prod_deepestM_eq_two_of_L2 (H : Fin 3 → ℕ) (r : ℕ)
    (C : Params (L := 2) (deepestM H r)) :
    prod (deepestM H r) C
      = Matrix.reindex
            (finCongr (rfl : deepestM H r 0 = deepestM H r ((0 : Fin 2)).castSucc))
            (finCongr (rfl : deepestM H r 1 = deepestM H r ((0 : Fin 2)).succ))
            (C (0 : Fin 2))
          * Matrix.reindex
            (finCongr (rfl : deepestM H r 1 = deepestM H r ((1 : Fin 2)).castSucc))
            (finCongr (rfl : deepestM H r (Fin.last 2) = deepestM H r ((1 : Fin 2)).succ))
            (C (1 : Fin 2)) := by
  -- Front-peel the last layer (`prod_eq_prodAux_mul_last`, m = 1): `prod = prodAux 1 · reindex(C 1)`.
  rw [prod_eq_prodAux_mul_last (m := 1) (deepestM H r) C rfl rfl]
  congr 1
  -- The prefix `prodAux 1 = prodAux 0 · reindex(C 0)`, and `prodAux 0 = 1`.
  rw [prodAux_succ (deepestM H r) C 0 (by omega) rfl rfl]
  -- Goal: `prodAux 0 · reindex(C 0) = reindex(C 0)`; `prodAux 0 = 1` is defeq, so `one_mul`.
  exact Matrix.one_mul _

/-! ### S6r — joint-move readbacks (the shared foundation for both S6 geometric subs)

`psiSplitRawL2Core` edits ONLY the last-layer `readY` (→ `l2Y1p`) and the last-layer core (→ `l2T1p`);
every other per-layer read is fixed. These readbacks (via the `DeepestPsiLens` round-trips) are what the
reg-invariance + core=Score subs consume to reduce `framedParamsPivot (psiSplitRawL2Core q)` to the
original `framedParamsPivot q` with the two last-layer blocks swapped. -/

-- The gauge slot of psiSplitRawL2Core q is regGaugeSlotEquiv.symm (l2g' q).
theorem psiSplitRawL2Core_gauge (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    ((psiSplitRawL2Core H r hr hL hL2eq q).1, (psiSplitRawL2Core H r hr hL hL2eq q).2.2)
      = (regGaugeSlotEquiv H r hr hL).symm (l2g' H r hr hL hL2eq q) := by
  rw [psiSplitRawL2Core_eq]

-- readX of the moved gauge = original (g' fixes all X-tags).
theorem readX_psiSplitRawL2Core (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (i j : Fin r) :
    readX H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s i j
      = readX H r hr hL (q.1, q.2.2) s i j := by
  rw [psiSplitRawL2Core_gauge, readX_regGaugeSlotEquiv_symm]
  -- l2g' at the X-tag = g idx = regGaugeSlotEquiv (q.1,q.2.2) (X-tag) = readX (q.1,q.2.2) s i j.
  rfl

-- readZ of the moved gauge = original.
theorem readZ_psiSplitRawL2Core (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L)
    (i : Fin (H s.castSucc - r)) (j : Fin r) :
    readZ H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s i j
      = readZ H r hr hL (q.1, q.2.2) s i j := by
  rw [psiSplitRawL2Core_gauge, readZ_regGaugeSlotEquiv_symm]; rfl

-- readY of the moved gauge at a NON-last layer = original.
theorem readY_psiSplitRawL2Core_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL)
    (i : Fin r) (j : Fin (H s.succ - r)) :
    readY H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s i j
      = readY H r hr hL (q.1, q.2.2) s i j := by
  rw [psiSplitRawL2Core_gauge, readY_regGaugeSlotEquiv_symm]
  -- l2g' at the Y-tag ⟨s, inl(inr(i,j))⟩ with s ≠ last → the `else` branch = g idx = readY q s i j.
  show l2g' H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩ = readY H r hr hL (q.1, q.2.2) s i j
  rw [l2g']; simp only [dif_neg hs]; rfl

-- readY of the moved gauge at the LAST layer = l2Y1p (the moved reg block).
theorem readY_psiSplitRawL2Core_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (i : Fin r) (j : Fin (H (lastLayer hL).succ - r)) :
    readY H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) (lastLayer hL) i j
      = l2Y1p H r hr hL hL2eq q i j := by
  rw [psiSplitRawL2Core_gauge, readY_regGaugeSlotEquiv_symm]
  show l2g' H r hr hL hL2eq q ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
      = l2Y1p H r hr hL hL2eq q i j
  rw [l2g']
  simp only [dif_pos rfl]
  rfl

-- coreRead of the moved core slot at a NON-last layer = original.
theorem coreRead_psiSplitRawL2Core_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2Core H r hr hL hL2eq q).2.1 s
      = (paramsEquivFlat (deepestM H r)).symm q.2.1 s := by
  -- (psiSplitRawL2Core q).2.1 = core' = paramsEquivFlat(update(decode q.2.1, last, T1')).
  have hcore : (psiSplitRawL2Core H r hr hL hL2eq q).2.1
      = paramsEquivFlat (deepestM H r)
          (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1)
            (lastLayer hL) (l2T1p H r hr hL hL2eq q)) := by
    rw [psiSplitRawL2Core_eq]
  rw [hcore, coreDecode_paramsEquivFlat, Function.update_of_ne hs]

-- coreRead of the moved core slot at the LAST layer = l2T1p.
theorem coreRead_psiSplitRawL2Core_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2Core H r hr hL hL2eq q).2.1 (lastLayer hL)
      = l2T1p H r hr hL hL2eq q := by
  have hcore : (psiSplitRawL2Core H r hr hL hL2eq q).2.1
      = paramsEquivFlat (deepestM H r)
          (Function.update ((paramsEquivFlat (deepestM H r)).symm q.2.1)
            (lastLayer hL) (l2T1p H r hr hL hL2eq q)) := by
    rw [psiSplitRawL2Core_eq]
  rw [hcore, coreDecode_paramsEquivFlat, Function.update_self]

/-! ### S6f — framedParamsPivot under the joint move (non-last layers identical) -/

-- Matrix-level readbacks (from the entrywise ones).
theorem readX_psiSplitRawL2Core_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    readX H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s
      = readX H r hr hL (q.1, q.2.2) s := by
  ext i j; exact readX_psiSplitRawL2Core H r hr hL hL2eq q s i j

theorem readZ_psiSplitRawL2Core_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) :
    readZ H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s
      = readZ H r hr hL (q.1, q.2.2) s := by
  ext i j; exact readZ_psiSplitRawL2Core H r hr hL hL2eq q s i j

theorem readY_psiSplitRawL2Core_of_ne_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    readY H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s
      = readY H r hr hL (q.1, q.2.2) s := by
  ext i j; exact readY_psiSplitRawL2Core_of_ne H r hr hL hL2eq q s hs i j

-- readY of the moved gauge at the LAST layer = l2Y1p (matrix-level).
theorem readY_psiSplitRawL2Core_last_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    readY H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) (lastLayer hL)
      = l2Y1p H r hr hL hL2eq q := by
  ext i j; exact readY_psiSplitRawL2Core_last H r hr hL hL2eq q i j

/-! ### S6c — the absorbed per-layer cores of the moved point (the sub-4 c₀/c₁ identification)

The absorbed core tuple is `c_s = decode(ψq).2.1 s + schurCorrection(ψq) s = T_s − Z_s·A_s⁻¹·Y_s` (the
Schur-shifted core read off the MOVED gauge). At the last layer the move sends `T ↦ l2T1p`, `Y ↦ l2Y1p`
(reads `Z, A` fixed), so `c_last = l2T1p − l2Z1·l2A1⁻¹·l2Y1p = (1 − K)·S1` (the banked keystone
`l2T1p_sub_Z1A1invY1p_eq`, on the inner ball where `det W ≠ 0`). At the first layer everything is fixed,
so `c_0` is the original layer-0 Schur core. -/

/-- The moved last-layer Schur correction `schurCorrection(ψq) last = −l2Z1·l2A1⁻¹·l2Y1p`: at the last
layer `readZ(ψq) = l2Z1`, `1 + readX(ψq) = l2A1`, `readY(ψq) = l2Y1p`. -/
theorem schurCorrection_psiSplitRawL2Core_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    schurCorrection H r hr hL
        ((psiSplitRawL2Core H r hr hL hL2eq q).1, (psiSplitRawL2Core H r hr hL hL2eq q).2.2)
        (lastLayer hL)
      = -(l2Z1 H r hr hL q) * (l2A1 H r hr hL q)⁻¹ * l2Y1p H r hr hL hL2eq q := by
  rw [schurCorrection, readZ_psiSplitRawL2Core_eq, readX_psiSplitRawL2Core_eq,
    readY_psiSplitRawL2Core_last_eq]
  rfl

/-- **The absorbed last-layer core IS `(1 − K)·S1`** (the sub-4 `c₁`): the moved decode-core `l2T1p`
plus the moved Schur correction `−l2Z1·l2A1⁻¹·l2Y1p` collapses to `(1 − K)·S1` via the banked keystone
`l2T1p_sub_Z1A1invY1p_eq` (`det W ≠ 0`). -/
theorem absorbedCore_psiSplitRawL2Core_last (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (hW : (l2W H r hr hL hL2eq q).det ≠ 0) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2Core H r hr hL hL2eq q).2.1 (lastLayer hL)
        + schurCorrection H r hr hL
            ((psiSplitRawL2Core H r hr hL hL2eq q).1, (psiSplitRawL2Core H r hr hL hL2eq q).2.2)
            (lastLayer hL)
      = (1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL hL2eq q := by
  rw [coreRead_psiSplitRawL2Core_last, schurCorrection_psiSplitRawL2Core_last,
    ← l2T1p_sub_Z1A1invY1p_eq H r hr hL hL2eq q hW]
  -- `l2T1p + (−Z1)·A1⁻¹·Y1' = l2T1p − Z1·A1⁻¹·Y1'`.
  rw [sub_eq_add_neg]
  congr 1
  rw [Matrix.neg_mul, Matrix.neg_mul]

/-- **The absorbed cores agree off the last layer** (the sub-4 `c₀`): at a non-last layer every read +
the decode-core is fixed under the move, so `decode(ψq).2.1 s + schurCorr(ψq) s = decode(q).2.1 s +
schurCorr(q) s`. -/
theorem absorbedCore_psiSplitRawL2Core_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2Core H r hr hL hL2eq q).2.1 s
        + schurCorrection H r hr hL
            ((psiSplitRawL2Core H r hr hL hL2eq q).1, (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s
      = (paramsEquivFlat (deepestM H r)).symm q.2.1 s
        + schurCorrection H r hr hL (q.1, q.2.2) s := by
  rw [coreRead_psiSplitRawL2Core_of_ne H r hr hL hL2eq q s hs]
  congr 1
  -- `schurCorrection(ψq) s = schurCorrection(q) s` for `s ≠ last` (reads fixed).
  rw [schurCorrection, schurCorrection, readZ_psiSplitRawL2Core_eq, readX_psiSplitRawL2Core_eq,
    readY_psiSplitRawL2Core_of_ne_eq H r hr hL hL2eq q s hs]

-- framedParamsPivot of the moved point: per-layer, equals the original EXCEPT last-layer Y/core.
theorem framedParamsPivot_psiSplitRawL2Core_of_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) (s : Fin L) (hs : s ≠ lastLayer hL) :
    framedParamsPivot H r hr hL J P Q (psiSplitRawL2Core H r hr hL hL2eq q) s
      = framedParamsPivot H r hr hL J P Q q s := by
  rw [framedParamsPivot_of_ne_last H r hr hL J P Q (psiSplitRawL2Core H r hr hL hL2eq q) s hs,
    framedParamsPivot_of_ne_last H r hr hL J P Q q s hs]
  show framedLayer H r hr s (P s) (Q s)
      (readX H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s)
      (readY H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s)
      (readZ H r hr hL ((psiSplitRawL2Core H r hr hL hL2eq q).1,
        (psiSplitRawL2Core H r hr hL hL2eq q).2.2) s)
      ((paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2Core H r hr hL hL2eq q).2.1 s)
    = framedLayer H r hr s (P s) (Q s)
      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s) ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)
  rw [readX_psiSplitRawL2Core_eq, readZ_psiSplitRawL2Core_eq,
    readY_psiSplitRawL2Core_of_ne_eq H r hr hL hL2eq q s hs,
    coreRead_psiSplitRawL2Core_of_ne H r hr hL hL2eq q s hs]

/-! ### S6d — the raw 2-factor product reg-block invariance (the e2/leak-kill at the RAW level)

For a 2-factor reindexed product `reindex(G0·G1)` (the L=2 raw layer product), the `{11,12,21}` blocks
read (via `reindex_mul_fromBlocks`) off `G0`'s blocks and `G1`'s blocks: `{11} = G0₁₁·G1₁₁ + G0₁₂·G1₂₁`,
`{21} = G0₂₁·G1₁₁ + G0₂₂·G1₂₁` (both read only `G1`'s `{11},{21}`), and `{12} = G0₁₁·G1₁₂ + G0₁₂·G1₂₂`
(the `A0·Y1' + Y0·T1'` combination — fixed by `e2_regPreserve`). So two last-layers `G1ψ`/`G1q` whose
reindexed `{11},{21}` agree and whose `{12}/{22}` satisfy the e2 relation give products agreeing on
`{11,12,21}`. This is the RAW-level E2/leak-kill (`framed_regBlocks_eq_of_mid` then carries it through the
endpoint frames). -/

/-- **Raw 2-factor product `{11,12,21}` invariance under an e2-preserving last-layer move.** Sharing the
first factor `G0`, if the reindexed last factors agree on `{11}` and `{21}`, and their `{12}/{22}` satisfy
the e2 combination `G0₁₁·G1ψ₁₂ + G0₁₂·G1ψ₂₂ = G0₁₁·G1q₁₂ + G0₁₂·G1q₂₂`, then `reindex(G0·G1ψ)` and
`reindex(G0·G1q)` agree on `{11,12,21}`. -/
theorem reindex_prod_regBlocks_eq_of_e2 {a b c r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eMid : Fin c ≃ Fin r ⊕ Fin (c - r))
    (eC : Fin b ≃ Fin r ⊕ Fin (b - r))
    (G0 G1ψ G1q : Matrix (Fin a) (Fin c) ℝ) (G1ψ' G1q' : Matrix (Fin c) (Fin b) ℝ)
    (h11G : (Matrix.reindex eMid eC G1ψ').toBlocks₁₁ = (Matrix.reindex eMid eC G1q').toBlocks₁₁)
    (h21G : (Matrix.reindex eMid eC G1ψ').toBlocks₂₁ = (Matrix.reindex eMid eC G1q').toBlocks₂₁)
    (he2 : (Matrix.reindex eR eMid G0).toBlocks₁₁ * (Matrix.reindex eMid eC G1ψ').toBlocks₁₂
          + (Matrix.reindex eR eMid G0).toBlocks₁₂ * (Matrix.reindex eMid eC G1ψ').toBlocks₂₂
        = (Matrix.reindex eR eMid G0).toBlocks₁₁ * (Matrix.reindex eMid eC G1q').toBlocks₁₂
          + (Matrix.reindex eR eMid G0).toBlocks₁₂ * (Matrix.reindex eMid eC G1q').toBlocks₂₂) :
    ((Matrix.reindex eR eC (G0 * G1ψ')).toBlocks₁₁ = (Matrix.reindex eR eC (G0 * G1q')).toBlocks₁₁)
      ∧ ((Matrix.reindex eR eC (G0 * G1ψ')).toBlocks₁₂ = (Matrix.reindex eR eC (G0 * G1q')).toBlocks₁₂)
      ∧ ((Matrix.reindex eR eC (G0 * G1ψ')).toBlocks₂₁
          = (Matrix.reindex eR eC (G0 * G1q')).toBlocks₂₁) := by
  rw [reindex_mul_fromBlocks eR eMid eC G0 G1ψ', reindex_mul_fromBlocks eR eMid eC G0 G1q']
  rw [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₁]
  refine ⟨?_, ?_, ?_⟩
  · rw [h11G, h21G]
  · rw [he2]
  · rw [h11G, h21G]

/-! ### S6e — the frame-block fact (block-lower P · M · block-upper Q reads {11,12,21} off M's)

The reg-counterpart to `schur_frame_transform`: for `P = fromBlocks a 0 c D_P` (block-LOWER) and
`Q = fromBlocks e f 0 D_Q` (block-UPPER), the `{11,12,21}` blocks of `P·M·Q` depend on `M = fromBlocks A
B C D` only through `M`'s `{11,12,21}` (= `A, B, C`), NOT its `{22}` (= `D`):
`{11} = a·A·e`, `{12} = a·(A·f + B·D_Q)`, `{21} = (c·A + D_P·C)·e`. So two middles agreeing on
`{11,12,21}` give framed products agreeing on `{11,12,21}` — the E2/leak-kill content of sub-3, frame-free.
This is exactly the moved-(2,2) leak-kill: the joint move changes only `M`'s `{22}` (after `e2_regPreserve`
fixes `M`'s `{12}` = P01), so the reg blocks `{11,12,21}` of the framed product are invariant. -/

/-- **The framed `{11,12,21}` blocks read off the middle's `{11,12,21}`** (block-lower `P` / block-upper
`Q`). Two middles with equal `{11,12,21}` blocks give framed products with equal `{11,12,21}` blocks. -/
theorem framed_regBlocks_eq_of_mid {r s t : Type*}
    [Fintype r] [DecidableEq r] [Fintype s] [Fintype t]
    (a : Matrix r r ℝ) (c : Matrix s r ℝ) (DP : Matrix s s ℝ)
    (e : Matrix r r ℝ) (f : Matrix r t ℝ) (DQ : Matrix t t ℝ)
    (A₁ : Matrix r r ℝ) (B₁ : Matrix r t ℝ) (C₁ : Matrix s r ℝ) (D₁ : Matrix s t ℝ)
    (A₂ : Matrix r r ℝ) (B₂ : Matrix r t ℝ) (C₂ : Matrix s r ℝ) (D₂ : Matrix s t ℝ)
    (hA : A₁ = A₂) (hB : B₁ = B₂) (hC : C₁ = C₂) :
    ((Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A₁ B₁ C₁ D₁
          * Matrix.fromBlocks e f 0 DQ).toBlocks₁₁
        = (Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A₂ B₂ C₂ D₂
            * Matrix.fromBlocks e f 0 DQ).toBlocks₁₁)
      ∧ ((Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A₁ B₁ C₁ D₁
            * Matrix.fromBlocks e f 0 DQ).toBlocks₁₂
          = (Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A₂ B₂ C₂ D₂
              * Matrix.fromBlocks e f 0 DQ).toBlocks₁₂)
      ∧ ((Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A₁ B₁ C₁ D₁
            * Matrix.fromBlocks e f 0 DQ).toBlocks₂₁
          = (Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A₂ B₂ C₂ D₂
              * Matrix.fromBlocks e f 0 DQ).toBlocks₂₁) := by
  -- The framed product's blocks (reuses `schur_frame_transform`'s `hN`-style computation).
  have hN : ∀ (A : Matrix r r ℝ) (B : Matrix r t ℝ) (C : Matrix s r ℝ) (D : Matrix s t ℝ),
      Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D * Matrix.fromBlocks e f 0 DQ
        = Matrix.fromBlocks (a * A * e) (a * A * f + a * B * DQ)
            ((c * A + DP * C) * e) ((c * A + DP * C) * f + (c * B + DP * D) * DQ) := by
    intro A B C D
    rw [show Matrix.fromBlocks a 0 c DP * Matrix.fromBlocks A B C D
          = Matrix.fromBlocks (a * A) (a * B) (c * A + DP * C) (c * B + DP * D) from by
        rw [Matrix.fromBlocks_multiply]; simp only [Matrix.zero_mul, add_zero],
      Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.mul_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hN A₁ B₁ C₁ D₁, hN A₂ B₂ C₂ D₂, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₁₁, hA]
  · rw [hN A₁ B₁ C₁ D₁, hN A₂ B₂ C₂ D₂, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₁₂, hA, hB]
  · rw [hN A₁ B₁ C₁ D₁, hN A₂ B₂ C₂ D₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₁, hA, hC]

/-! ### S6t — the SHARED endpoint-telescope corner split (the `hRegBlocks` core both subs consume)

For a framed point whose per-layer frame is clean (`hframe : framedParamsPivot … = Pf · A · Qf`, the
witnessed-telescope hypothesis) and whose interior interfaces are identity (`hinterface`), the reindexed
framed product corner-splits: `reindex(prod(framedParamsPivot p)) = fromBlocks 1 0 0 0 +
reindex(endpointP0·(prod A − B)·endpointQL)` (given the B-normalization `hS3b`). This is the producer's
`hRegBlocks` step (`DeepestGaugeConstruction`), extracted standalone so BOTH S6 subs reuse it: sub-3
reads the {11,12,21} reg blocks off the split (E2/leak-kill), sub-4 reads the {22}-Schur (frame-transform).
The telescope/interface/`hS3b` hyps match `endpoint_telescoping_eq`'s inputs EXACTLY (controller's
final-wiring discharge is then a direct application). -/

/-- **The corner split** (`hRegBlocks` extracted): `reindex(prod(framedParamsPivot p)) = fromBlocks 1 0
0 0 + reindex(endpointP0·(prod A − B)·endpointQL)`, given the per-layer telescope frame `hframe`, the
interior-interface identity `hinterface`, and the B-normalization `hS3b`. -/
theorem framedReindexProd_corner_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (p : DeepestSplit H r (deepestNGauge H r)) (A : Params H)
    (hframe : ∀ s : Fin L, framedParamsPivot H r hr hL J Pf Qf p s = Pf s * A s * Qf s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ))
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) :
    Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (prod H (framedParamsPivot H r hr hL J Pf Qf p))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0
        + Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A - B) * endpointQL H hL Qf) := by
  -- The witnessed telescope: `prod(framedParamsPivot p) = endpointP0·prod A·endpointQL`.
  have hS2 : prod H (framedParamsPivot H r hr hL J Pf Qf p)
      = endpointP0 H hL Pf * prod H A * endpointQL H hL Qf :=
    endpoint_telescoping_eq H hL A (framedParamsPivot H r hr hL J Pf Qf p) Pf Qf hframe hinterface
  -- `P0·prod A·QL = P0·B·QL + P0·(prod A − B)·QL`.
  have hsplitprod : endpointP0 H hL Pf * prod H A * endpointQL H hL Qf
      = endpointP0 H hL Pf * B * endpointQL H hL Qf
        + endpointP0 H hL Pf * (prod H A - B) * endpointQL H hL Qf := by
    rw [Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
  rw [hS2, hsplitprod]
  -- reindex is additive; the corner summand is `fromBlocks 1 0 0 0` (hS3b).
  have hadd : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * B * endpointQL H hL Qf
            + endpointP0 H hL Pf * (prod H A - B) * endpointQL H hL Qf)
        = Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * B * endpointQL H hL Qf)
          + Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A - B) * endpointQL H hL Qf) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]
  rw [hadd, hS3b]

/-! ### S6 sub-lemmas (the decomposition; assembly proven, two geometric subs sorried) -/

theorem psiRawL2_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (x : Fin (flatDim H) → ℝ) :
    deepestSplit H r hr hL (wstarL2 H r B hB hr hL) (psiRawL2 H r B hB hr hL J Pf Qf x)
      = psiSplitRawL2 H r hr hL
          (deepestSplit H r hr hL (wstarL2 H r B hB hr hL) x) := by
  rw [psiRawL2, (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).apply_symm_apply]

/-- **Reg-energy block reduction under the corner split** (the shared plumbing both reg-energy sums
reuse): once the framed product corner-splits as `fromBlocks 1 0 0 0 + reindex(resid)`, the three
reg-block sums of `deepestEFull_sq_sum_eq_blocks` read the residual blocks directly (the `+1` corner
cancels in {11}, contributes `0` to {12}/{21}). So two points with EQUAL residual {11,12,21} blocks
have equal reg energy. -/
theorem deepestEFull_sq_sum_eq_of_resid_blocks (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q₁ q₂ : DeepestSplit H r (deepestNGauge H r)) (A₁ A₂ : Params H)
    (hframe₁ : ∀ s : Fin L, framedParamsPivot H r hr hL J Pf Qf q₁ s = Pf s * A₁ s * Qf s)
    (hframe₂ : ∀ s : Fin L, framedParamsPivot H r hr hL J Pf Qf q₂ s = Pf s * A₂ s * Qf s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ))
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (h11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf)).toBlocks₁₁)
    (h12 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf)).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf)).toBlocks₁₂)
    (h21 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf)).toBlocks₂₁) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf q₁ i) ^ 2)
      = ∑ i, (deepestEFull H r hr hL J Pf Qf q₂ i) ^ 2 := by
  rw [deepestEFull_sq_sum_eq_blocks H r hr hL J Pf Qf q₁,
    deepestEFull_sq_sum_eq_blocks H r hr hL J Pf Qf q₂,
    framedReindexProd_corner_split H r B hr hL J Pf Qf q₁ A₁ hframe₁ hinterface hS3b,
    framedReindexProd_corner_split H r B hr hL J Pf Qf q₂ A₂ hframe₂ hinterface hS3b]
  set R₁ := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
      (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf) with hR₁
  set R₂ := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
      (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
      (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf) with hR₂
  -- Block-of-sum extraction (entrywise; `Matrix.toBlocks_add` is absent at this pin).
  have e11 : ∀ (M : Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ),
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + M).toBlocks₁₁ - 1 = M.toBlocks₁₁ := by
    intro M; ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.add_apply, Matrix.fromBlocks_apply₁₁, Matrix.of_apply,
      Matrix.sub_apply, Matrix.one_apply]
    split <;> ring
  have e12 : ∀ (M : Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ),
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + M).toBlocks₁₂ = M.toBlocks₁₂ := by
    intro M; ext a b
    simp only [Matrix.toBlocks₁₂, Matrix.add_apply, Matrix.fromBlocks_apply₁₂, Matrix.of_apply,
      Matrix.zero_apply, zero_add]
  have e21 : ∀ (M : Matrix (Fin r ⊕ Fin (H 0 - r)) (Fin r ⊕ Fin (H (Fin.last L) - r)) ℝ),
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 + M).toBlocks₂₁ = M.toBlocks₂₁ := by
    intro M; ext a b
    simp only [Matrix.toBlocks₂₁, Matrix.add_apply, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
      Matrix.zero_apply, zero_add]
  rw [e11 R₁, e11 R₂, e12 R₁, e12 R₂, e21 R₁, e21 R₂, h11, h12, h21]

/-- **The residual `{11,12,21}` blocks read off the raw-middle's `{11,12,21}`** (the frame-handling
half of sub-3, frame-block + reindex-distribution). For block-LOWER `reindex(endpointP0)` (hPtri) and
block-UPPER `reindex(endpointQL)` (hQtri), the `{11,12,21}` of `reindex(endpointP0·(prod A − B)·endpointQL)`
read off `reindex(prod A − B)`'s `{11,12,21}` only. So two raw middles `prod A₁`/`prod A₂` agreeing on
`{11,12,21}` give residuals agreeing on `{11,12,21}`. Pure `reindex_mul_split` distribution +
`framed_regBlocks_eq_of_mid`. -/
theorem resid_regBlocks_eq_of_mid_agree (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (A₁ A₂ : Params H)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hm11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H A₁)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H A₂)).toBlocks₁₁)
    (hm12 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H A₁)).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H A₂)).toBlocks₁₂)
    (hm21 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H A₁)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H A₂)).toBlocks₂₁) :
    ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
          (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf)).toBlocks₁₁)
      ∧ ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf)).toBlocks₁₂
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf)).toBlocks₁₂)
      ∧ ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H A₁ - B) * endpointQL H hL Qf)).toBlocks₂₁
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H A₂ - B) * endpointQL H hL Qf)).toBlocks₂₁) := by
  -- Abbreviate the outer split equivs.
  set eR := rThresholdSplit r (H 0) (hr 0) with heR
  set eC := pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J with heC
  set P0 := endpointP0 H hL Pf with hP0
  set QL := endpointQL H hL Qf with hQL
  -- Distribute the reindex of the triple product into the three reindexed factors (the middle keyed by
  -- `(eR, eC)`, the frames square via `eR`/`eC`).  `reindex(P0·M·QL) = reindex(P0)·reindex(M)·reindex(QL)`.
  have hdist : ∀ A : Params H,
      Matrix.reindex eR eC (P0 * (prod H A - B) * QL)
        = Matrix.reindex eR eR P0 * Matrix.reindex eR eC (prod H A - B) * Matrix.reindex eC eC QL := by
    intro A
    rw [reindex_mul_split eR eC eC (P0 * (prod H A - B)) QL,
      reindex_mul_split eR eR eC P0 (prod H A - B)]
  -- The frames as `fromBlocks` (block-LOWER `P0` via hPtri; block-UPPER `QL` via hQtri).
  have hP0fb : Matrix.reindex eR eR P0
      = Matrix.fromBlocks (Matrix.reindex eR eR P0).toBlocks₁₁ 0
          (Matrix.reindex eR eR P0).toBlocks₂₁ (Matrix.reindex eR eR P0).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eR eR P0)]
    rw [hPtri]
  have hQLfb : Matrix.reindex eC eC QL
      = Matrix.fromBlocks (Matrix.reindex eC eC QL).toBlocks₁₁ (Matrix.reindex eC eC QL).toBlocks₁₂
          0 (Matrix.reindex eC eC QL).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eC eC QL)]
    rw [hQtri]
  -- The two middles `reindex(prod A₁ − B)`, `reindex(prod A₂ − B)` as `fromBlocks`; their {11,12,21}
  -- agree (the common `− reindex B` cancels via `hm11/hm12/hm21` on `reindex(prod A)`).
  have hsub : ∀ A : Params H, Matrix.reindex eR eC (prod H A - B)
      = Matrix.reindex eR eC (prod H A) - Matrix.reindex eR eC B := by
    intro A; ext i j; simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]
  have hMidEq : ∀ (ij : Fin 3),
      True := fun _ => trivial  -- placeholder; the three block eqs are derived inline below
  -- Middle block agreements (subtract the common `reindex B`).
  have hmid11 : (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₁₁
      = (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₁₁ := by
    rw [hsub, hsub]; ext i j
    simp only [Matrix.toBlocks₁₁, Matrix.sub_apply, Matrix.of_apply]
    have := congrFun (congrFun hm11 i) j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
    rw [this]
  have hmid12 : (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₁₂
      = (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₁₂ := by
    rw [hsub, hsub]; ext i j
    simp only [Matrix.toBlocks₁₂, Matrix.sub_apply, Matrix.of_apply]
    have := congrFun (congrFun hm12 i) j
    simp only [Matrix.toBlocks₁₂, Matrix.of_apply] at this
    rw [this]
  have hmid21 : (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₂₁
      = (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₂₁ := by
    rw [hsub, hsub]; ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.sub_apply, Matrix.of_apply]
    have := congrFun (congrFun hm21 i) j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply] at this
    rw [this]
  clear hMidEq
  -- Apply `framed_regBlocks_eq_of_mid` (explicit block args to avoid a `whnf` unification blowup) to
  -- the distributed product, with both middles written as `fromBlocks` of their `toBlocks`.
  have hkey := framed_regBlocks_eq_of_mid
    (Matrix.reindex eR eR P0).toBlocks₁₁ (Matrix.reindex eR eR P0).toBlocks₂₁
    (Matrix.reindex eR eR P0).toBlocks₂₂
    (Matrix.reindex eC eC QL).toBlocks₁₁ (Matrix.reindex eC eC QL).toBlocks₁₂
    (Matrix.reindex eC eC QL).toBlocks₂₂
    (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₁₁
    (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₁₂
    (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₂₁
    (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₂₂
    (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₁₁
    (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₁₂
    (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₂₁
    (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₂₂
    hmid11 hmid12 hmid21
  -- Rewrite the goal's products into the `fromBlocks · fromBlocks · fromBlocks` shape `hkey` proves.
  -- The middle factors → `fromBlocks` of their `toBlocks` (BOTH middles, all occurrences), then frames.
  rw [hdist A₁, hdist A₂,
    show Matrix.reindex eR eC (prod H A₁ - B)
        = Matrix.fromBlocks (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₁₁
            (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₁₂
            (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₂₁
            (Matrix.reindex eR eC (prod H A₁ - B)).toBlocks₂₂ from
          (Matrix.fromBlocks_toBlocks _).symm,
    show Matrix.reindex eR eC (prod H A₂ - B)
        = Matrix.fromBlocks (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₁₁
            (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₁₂
            (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₂₁
            (Matrix.reindex eR eC (prod H A₂ - B)).toBlocks₂₂ from
          (Matrix.fromBlocks_toBlocks _).symm,
    hP0fb, hQLfb]
  exact hkey

/-- **Sub-3 — reg-energy invariance under the joint move.** The reg energy reads only the framed
product's `{11,12,21}` blocks, which the joint move leaves invariant (E2/leak-kill).  Route A
(telescope-bound): the abstract de-framed tuples `Aψ`/`Aq` + the witnessed frames `hframeψ`/`hframeq` +
`hinterface` + the B-normalization `hS3b` feed the corner-split entry point
`deepestEFull_sq_sum_eq_of_resid_blocks`; the residual `{11,12,21}` agreement is the frame-handling
`resid_regBlocks_eq_of_mid_agree` (hPtri/hQtri) fed by the raw-middle `{11,12,21}` agreement
`hm11/hm12/hm21` (controller-discharged via `reindex_prod_regBlocks_eq_of_e2` + the S6r readbacks +
`e2_regPreserve`). -/
theorem deepestEFull_sq_sum_psiSplitRawL2_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (q : DeepestSplit H r (deepestNGauge H r))
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
    (Aψ Aq : Params H)
    (hframeψ : ∀ s : Fin L,
      framedParamsPivot H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL q) s = Pf s * Aψ s * Qf s)
    (hframeq : ∀ s : Fin L, framedParamsPivot H r hr hL J Pf Qf q s = Pf s * Aq s * Qf s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ))
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hm11 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aψ)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aq)).toBlocks₁₁)
    (hm12 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aψ)).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aq)).toBlocks₁₂)
    (hm21 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aψ)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J) (prod H Aq)).toBlocks₂₁) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL q) i) ^ 2)
      = ∑ i, (deepestEFull H r hr hL J Pf Qf q i) ^ 2 := by
  obtain ⟨h11, h12, h21⟩ :=
    resid_regBlocks_eq_of_mid_agree H r B hr hL J Pf Qf Aψ Aq hPtri hQtri hm11 hm12 hm21
  exact deepestEFull_sq_sum_eq_of_resid_blocks H r B hr hL J Pf Qf
    (psiSplitRawL2 H r hr hL q) q Aψ Aq hframeψ hframeq hinterface hS3b h11 h12 h21

-- Sub-lemma 4 (core = Score): the absorbed core energy equals the Schur-complement Score, on the
-- inner ball (where coreAbsorb = honest Schur). [HARDEST: LDU + the framed Score dictionary]

theorem deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
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
    (x : Fin (flatDim H) → ℝ)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hq : q = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)
    (hball : psiSplitRawL2 H r hr hL q ∈ Metric.closedBall
      (0 : DeepestSplit H r (deepestNGauge H r)) ((cutoffBump H r hr hL).rIn))
    (hWdet : (l2W H r hr hL hL2 q).det ≠ 0) :
    deepestCoreF H r (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL q)).2.1 = Score x := by
  -- SCOPED RESIDUAL (route A, sub-4 — feasibility CONFIRMED closeable w/ banked pieces, Codex high). The
  -- chain (each step a banked lemma; the 2 novel pieces — `schur_frame_transform`, `l2T1p_sub_Z1A1invY1p_eq`
  -- — are landed + axiom-clean):
  -- (a) `deepestCoreF_coreAbsorb_eq_prodSchur` (hball): LHS = frobSq(prod(deepestM)(decode(ψq).2.1 _s +
  --     schurCorrection(ψq) _s)). At L=2 the reduced product = c0·c1.
  --     c0 = T0 − Z0·A0⁻¹·Y0 = S0 (layer0 reads fixed under ψ: readX/Z/Y/core);
  --     c1 = l2T1p − Z1·A1⁻¹·l2Y1p = (1−K)·S1 (the keystone `l2T1p_sub_Z1A1invY1p_eq`, det W ≠ 0 from hball).
  -- (b) `prod_absorbed_eq_schur_ldu` / `reindex_mul_schur_factor`: frobSq(S0·(1−K)·S1) = frobSq(Rcore),
  --     Rcore = (2,2)-Schur of reindex(prod(decode x)) [raw layers = fromBlocks(1+X)YZT via
  --     `reindex_fromBlocks_reads_eq_deviation`, DeepestFrameRaw:239 — the per-layer block bridge].
  -- (c) `rcore_eq_schur_of_corner_split` (hS3b removes the +1) then `schur_frame_transform` (hPbr/hQbr,
  --     D_P=D_Q=1) on M̂ = endpointP0·prod·endpointQL: frobSq(Rcore) = Score x.
  -- MISSING for green: the explicit reduced-product-at-L2 unfold (prodAux casts) + the reindex
  -- block-read instantiation + threading hS3b/hPbr/hQbr (to be added at the caller's wiring). The math
  -- is verified; the residual is cast/instantiation bookkeeping.
  -- Step (a): the absorbed-core energy form (banked, on the inner ball `hball`).
  have hstepA : deepestCoreF H r (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL q)).2.1
      = frobSq (prod (deepestM H r)
          (fun s => (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2 H r hr hL q).2.1 s
            + schurCorrection H r hr hL
                ((psiSplitRawL2 H r hr hL q).1, (psiSplitRawL2 H r hr hL q).2.2) s)) :=
    deepestCoreF_coreAbsorb_eq_prodSchur H r hr hL (psiSplitRawL2 H r hr hL q) hball
  rw [hstepA]
  -- STEP 1-2 (banked): identify the absorbed-core tuple `c` per layer.  `psiSplitRawL2 = psiSplitRawL2Core`
  -- at `L = 2`; then `absorbedCore_psiSplitRawL2Core_last` (consumes `hWdet`) gives `c last = (1−K)·S1`,
  -- and `absorbedCore_psiSplitRawL2Core_of_ne` gives `c s = decode(q) s + schurCorr(q) s` for `s ≠ last`.
  have hψeq : psiSplitRawL2 H r hr hL q = psiSplitRawL2Core H r hr hL hL2 q := dif_pos hL2
  have hclast : (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2 H r hr hL q).2.1 (lastLayer hL)
        + schurCorrection H r hr hL
            ((psiSplitRawL2 H r hr hL q).1, (psiSplitRawL2 H r hr hL q).2.2) (lastLayer hL)
      = (1 - l2K H r hr hL hL2 q) * l2S1 H r hr hL hL2 q := by
    rw [hψeq]; exact absorbedCore_psiSplitRawL2Core_last H r hr hL hL2 q hWdet
  have hc0 : ∀ s : Fin L, s ≠ lastLayer hL →
      (paramsEquivFlat (deepestM H r)).symm (psiSplitRawL2 H r hr hL q).2.1 s
        + schurCorrection H r hr hL
            ((psiSplitRawL2 H r hr hL q).1, (psiSplitRawL2 H r hr hL q).2.2) s
      = (paramsEquivFlat (deepestM H r)).symm q.2.1 s + schurCorrection H r hr hL (q.1, q.2.2) s := by
    intro s hs; rw [hψeq]; exact absorbedCore_psiSplitRawL2Core_of_ne H r hr hL hL2 q s hs
  -- STEP 3-4 (the LDU + frame-transform tail): `prod_absorbed_eq_schur_ldu` (identifying S0/S1/K with the
  -- raw `decode x` layer blocks) → `frobSq(Rcore)`, then `rcore_eq_schur_of_corner_split` (hS3b) +
  -- `schur_frame_transform` (hPbr/hQbr) → `Score x`.  THREADED as route-A inputs at the caller (hS3b,
  -- hPbr/hQbr + the decode-x readback ties); the L=2 reduced-product unfold via `prod_deepestM_eq_two_of_L2`.
  -- (hclast/hc0 above bank the absorbed-core identification — STEP 1-2.)
  -- SCOPED RESIDUAL (route A, sub-4 tail). The absorbed-core energy is now `frobSq(prod(deepestM) c)`
  -- with `c s = decode(ψq).2.1 s + schurCorrection(ψq) s` the per-layer Schur-shifted core.
  -- BANKED THIS TIDE (axiom-clean clean-three; in this file, S6c/S6p sections):
  --   • `prod_deepestM_eq_two_of_L2` — the L=2 unfold `prod(deepestM) c = c₀ · c₁` (after `subst hL2`).
  --   • `absorbedCore_psiSplitRawL2Core_last` — `c₁ = (1 − K)·S1` (consumes the keystone
  --     `l2T1p_sub_Z1A1invY1p_eq`, needs `det (l2W q) ≠ 0`).
  --   • `absorbedCore_psiSplitRawL2Core_of_ne` — `c₀ = decode(q).2.1 0 + schurCorr(q) 0` (= the
  --     original layer-0 Schur core S0, layer-0 reads fixed under ψ).
  -- REMAINING (genm-l2fin scoping, 2026-06-28 — sub-3 CLOSED; sub-4 isolated, NOT gating the assembly:
  -- comp_identity_L2/_impl now thread the per-`x` core=Score as `hsub4core`, so this `sorry` blocks only
  -- the standalone sub-4 theorem). The chain, mirroring sub-3's route + the new `resid_*` frame-handling:
  --   STEP 1-2 (most-banked): `subst hL2`; `prod_deepestM_eq_two_of_L2` → `c₀·c₁`;
  --     `absorbedCore_psiSplitRawL2Core_of_ne` (c₀ = layer-0 Schur core, the `s = 0 ≠ last` arm) +
  --     `absorbedCore_psiSplitRawL2Core_last` (c₁ = (1−K)·S1, CONSUMES `hWdet : det (l2W q) ≠ 0`).
  --   STEP 3 (LDU): `prod_absorbed_eq_schur_ldu` identifies `frobSq(S0·(1−K)S1) = frobSq(Rcore)`, Rcore
  --     the (2,2)-Schur of `reindex(prod(decode x))` (raw layers = fromBlocks(1+X)YZT, the per-layer block
  --     bridge `reindex_fromBlocks_reads_eq_deviation`).
  --   STEP 4 (frame→Score): `rcore_eq_schur_of_corner_split` (hS3b removes the +1) then
  --     `schur_frame_transform` (D_P = D_Q = 1 from hPbr/hQbr) on `M̂ = endpointP0·(prod−B)·endpointQL`.
  -- THREAD as route-A inputs (controller discharges at the DeepestGaugeConstruction wiring): `hWdet`
  --   (the W-det coupling — derivable from `hball` + `ball_l2ExtraRadius_subset` IF `cutoffBump.rIn ≤
  --   l2ExtraRadius` and `q`-membership; a GENUINE sub-step, not bookkeeping), `hS3b`, `hPbr`/`hQbr`,
  --   and the raw-layer-block readback ties for `decode x` (so STEP 3's S0/S1/K = the l2* blocks).
  sorry


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
    -- **Sub-3 per-`x` reg-energy invariance** (route-A input; the controller discharges it at the final
    -- wiring by `deepestEFull_sq_sum_psiSplitRawL2_eq` fed the producer's de-framed tuples `A(split x)` +
    -- the witnessed frames + the raw-middle `{11,12,21}` agreement — all in scope in `DeepestGaugeConstruction`).
    (hsub3reg : ∀ x : Fin (flatDim H) → ℝ,
      (∑ i, (deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
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
    -- **Sub-4 per-`x` core=Score** (route-A input; the controller discharges it at the final wiring by
    -- `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` on the inner ball with the frame-transform hyps).
    (hsub4core : ∀ x : Fin (flatDim H) → ℝ,
      deepestCoreF H r (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL (split x))).2.1 = Score x)
    (Φscore : (Fin (flatDim H) → ℝ) → ℝ)
    (hΦscore : Φscore = fun x => (∑ i, (regStraighten (split x)).1 i ^ 2) + Score x)
    (wstar : Fin (flatDim H) → ℝ)
    (hwstar : wstar = (paramsEquivFlat H) (deepestPoint H r B hB hr hL))
    (hL2eq : L = 2) :
    (fun x : Fin (flatDim H) → ℝ =>
        (∑ i, (regStraighten (split x)).1 i ^ 2)
          + deepestCoreF H r (coreAbsorb (split x)).2.1) ∘ (psiL2 H r B hB hr hL J Pf Qf)
      =ᶠ[nhds wstar] Φscore := by

  have hwstar' : wstarL2 H r B hB hr hL = wstar := by rw [wstarL2, hwstar]
  -- (i) psiL2 = psiRawL2 near wstar.
  have hgerm := psiL2_eventuallyEq_psiRawL2 H r B hB hr hL J Pf Qf wstar hwstar
  -- (ii) the inner-ball germ: psiSplitRawL2 (split x) ∈ closedBall 0 rIn near wstar.
  --   split (psiL2 x) → split (psiL2 wstar) = split wstar = 0; and on the germ = psiSplitRawL2 (split x).
  have hcont : Continuous (fun x => deepestSplit H r hr hL (wstarL2 H r B hB hr hL)
      (psiL2 H r B hB hr hL J Pf Qf x)) :=
    (deepestSplit H r hr hL (wstarL2 H r B hB hr hL)).continuous.comp
      (psiL2_contDiff H r B hB hr hL J Pf Qf).continuous
  have hfix : deepestSplit H r hr hL (wstarL2 H r B hB hr hL) (psiL2 H r B hB hr hL J Pf Qf wstar)
      = 0 := by
    rw [psiL2_fixpoint H r B hB hr hL J Pf Qf wstar hwstar, hwstar']
    exact (deepestSplit_mp_basepoint H r hr hL wstar).2
  have htend : Filter.Tendsto (fun x => deepestSplit H r hr hL (wstarL2 H r B hB hr hL)
      (psiL2 H r B hB hr hL J Pf Qf x)) (nhds wstar) (nhds 0) := by
    rw [← hfix]; exact hcont.continuousAt
  have hballgerm : (fun x => deepestSplit H r hr hL (wstarL2 H r B hB hr hL)
        (psiL2 H r B hB hr hL J Pf Qf x))
      ⁻¹' Metric.closedBall (0 : DeepestSplit H r (deepestNGauge H r)) ((cutoffBump H r hr hL).rIn)
      ∈ nhds wstar :=
    htend (Metric.closedBall_mem_nhds 0 (cutoffBump H r hr hL).rIn_pos)
  -- Combine the germs.
  filter_upwards [hgerm, hballgerm] with x hx hxball
  -- Reduce ∘ at x; rewrite psiL2 x = psiRawL2 x, split = deepestSplit.
  show (∑ i, (regStraighten (split (psiL2 H r B hB hr hL J Pf Qf x))).1 i ^ 2)
      + deepestCoreF H r (coreAbsorb (split (psiL2 H r B hB hr hL J Pf Qf x))).2.1 = Φscore x
  rw [hx]
  -- split (psiRawL2 x) = psiSplitRawL2 (split x).
  have hsp : split (psiRawL2 H r B hB hr hL J Pf Qf x)
      = psiSplitRawL2 H r hr hL (split x) := by
    rw [hsplit, hsplit, ← wstarL2, psiRawL2_split H r B hB hr hL J Pf Qf x]
  rw [hsp, hcoreabs, hΦscore]
  -- The reg term: invariant under the joint move (sub-lemma 3 via hregval).
  have hreg : (∑ i, (regStraighten (psiSplitRawL2 H r hr hL (split x))).1 i ^ 2)
      = ∑ i, (regStraighten (split x)).1 i ^ 2 := by
    simp only [hregval]
    exact hsub3reg x
  -- The core term = Score x (sub-lemma 4 on the inner ball, threaded as `hsub4core`).
  have hcore : deepestCoreF H r
      (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL (split x))).2.1 = Score x :=
    hsub4core x
  rw [hreg, hcore]

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
    -- **Sub-3 per-`x` reg-energy invariance** (route-A input; the controller discharges it at the final
    -- wiring by `deepestEFull_sq_sum_psiSplitRawL2_eq` fed the producer's de-framed tuples `A(split x)` +
    -- the witnessed frames + the raw-middle `{11,12,21}` agreement — all in scope in `DeepestGaugeConstruction`).
    (hsub3reg : ∀ x : Fin (flatDim H) → ℝ,
      (∑ i, (deepestEFull H r hr hL J Pf Qf (psiSplitRawL2 H r hr hL (split x)) i) ^ 2)
        = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2)
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
    -- **Sub-4 per-`x` core=Score** (route-A input; the controller discharges it at the final wiring by
    -- `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` on the inner ball with the frame-transform hyps).
    (hsub4core : ∀ x : Fin (flatDim H) → ℝ,
      deepestCoreF H r (deepestCoreAbsorb H r hr hL (psiSplitRawL2 H r hr hL (split x))).2.1 = Score x)
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
    comp_identity_L2 H r B hB hr hL hL2 hpos J hJfront Pf Qf hPtri hQtri split hsub3reg coreAbsorb
      regStraighten hsplit hregval hcoreabs Score hScoreDef hsub4core Φscore hΦscore wstar hwstar hL2eq
  exact rlctAtOn_diffeo_bridge_of Φscore Φcore wstar (psiL2 H r B hB hr hL J Pf Qf)
    (ContinuousLinearEquiv.refl ℝ (Fin (flatDim H) → ℝ))
    (psiL2_contDiff H r B hB hr hL J Pf Qf)
    (psiL2_hasStrictFDerivAt H r B hB hr hL J Pf Qf wstar hwstar)
    (psiL2_fixpoint H r B hB hr hL J Pf Qf wstar hwstar)
    hcomp

end DLNFibre.DLN.RLCT
