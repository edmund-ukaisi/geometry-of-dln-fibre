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
