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

/-! ### S4d — the intermediate matrices `K, R, U, W, S1, Br` (Codex route A, the `O(read²)` blocks)

To prove the entrywise strict-`fderiv`-`0` of `T1' − T1` and `Y1' − Y1`, name the joint-action
intermediates exactly as the `l2T1p`-`let`s (so `l2T1p_eq` is `rfl`): `K = Z1·P00⁻¹·Y0`,
`R = Z1·A1⁻¹·A0⁻¹·Y0`, `U = Z1·A1⁻¹·Y1`, `W = 1 + R`, `S1 = T1 − U`, `Br = (1−K)·S1 + U + R·T1`. The
algebra `T1' − T1 = (W⁻¹ − 1)·Br + (Br − T1)`, `Br − T1 = −(K·S1) + R·T1` (purely additive) reduces the
derivative to the `O(read²)` blocks (`K`, `R`, `W⁻¹ − 1`), each strict-`fderiv`-`0`. -/

/-- `K = Z1·P00⁻¹·Y0` (the `(1,1)`-block Schur correction; `O(read²)`, both outer reads vanish at `0`). -/
noncomputable def l2K (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
      (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹ * l2Y0 H r hr hL hL2eq q

/-- `R = Z1·A1⁻¹·A0⁻¹·Y0 = W − 1` (`O(read²)`, both outer reads vanish at `0`). -/
noncomputable def l2R (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q

/-- `U = Z1·A1⁻¹·Y1` (`O(read²)`). -/
noncomputable def l2U (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * l2Y1 H r hr hL q

/-- `W = 1 + R` (`W 0 = 1`; the joint-action denominator). -/
noncomputable def l2W (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ :=
  1 + l2R H r hr hL hL2eq q

/-- `S1 = T1 − U`. -/
noncomputable def l2S1 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  l2T1 H r hr hL q - l2U H r hr hL q

/-- `Br = (1 − K)·S1 + U + R·T1` (the `W⁻¹`-bracket; `l2T1p = W⁻¹·Br`). -/
noncomputable def l2Br (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    Matrix (Fin (deepestM H r (lastLayer hL).castSucc)) (Fin (deepestM H r (lastLayer hL).succ)) ℝ :=
  (1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL q + l2U H r hr hL q
    + l2R H r hr hL hL2eq q * l2T1 H r hr hL q

/-- `l2T1p = W⁻¹·Br` (`rfl` — `l2K/l2R/l2U/l2W/l2S1/l2Br` are exactly `l2T1p`'s `let` bodies). -/
theorem l2T1p_eq_Winv_Br (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2T1p H r hr hL hL2eq q
      = (l2W H r hr hL hL2eq q)⁻¹ * l2Br H r hr hL hL2eq q := rfl

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

end MatrixEntryDeriv

/-! ### S4a' — `ContDiffAt` matrix inverse for families whose entries are only `ContDiffAt`

The banked `contDiffAt_matrix_inv_entry_of_det_ne_zero` requires GLOBALLY `ContDiff` entries; that suffices
for `A0⁻¹/A1⁻¹/P00⁻¹` (their entries are global), but NOT for `W⁻¹` (whose `W = 1 + Z1·A1⁻¹·A0⁻¹·Y0`
already contains `A1⁻¹/A0⁻¹`, only `ContDiffAt`). The `_at` variants below mirror the global proofs with
`ContDiffAt`. -/

section EntrywiseInvAt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of an entrywise-`ContDiffAt` matrix family is `ContDiffAt x`. -/
theorem contDiffAt_matrix_det_of_entries {A : X → Matrix n n ℝ} {x : X}
    (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).det) x := by
  have heq : (fun y => (A y).det)
      = fun y => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A y (σ i) i := by
    funext y; rw [Matrix.det_apply]
  rw [heq]
  refine ContDiffAt.sum (fun σ _ => ?_)
  refine ContDiffAt.const_smul _ ?_
  exact contDiffAt_prod (fun i _ => hA (σ i) i)

/-- Each adjugate entry of an entrywise-`ContDiffAt` matrix family is `ContDiffAt x`. -/
theorem contDiffAt_matrix_adjugate_entry_of_entries {A : X → Matrix n n ℝ} {x : X}
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

/-- Each entry of `(A y)⁻¹` is `ContDiffAt x` when the entries are `ContDiffAt x` and `det (A x) ≠ 0`. -/
theorem contDiffAt_matrix_inv_entry_of_det_ne_zero_at {A : X → Matrix n n ℝ} {x : X}
    (hA : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹ i j) x := by
  have hentry : (fun y => (A y)⁻¹ i j)
      = fun y => (A y).det⁻¹ * (A y).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [hentry]
  have hdetinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).det⁻¹) x :=
    (contDiffAt_matrix_det_of_entries hA).inv hdet
  exact hdetinv.mul (contDiffAt_matrix_adjugate_entry_of_entries hA i j)

end EntrywiseInvAt

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

/-! ### S4c — entrywise `ContDiffAt` of the named matrices as functions of `q` (the partner inputs)

The matrix-entry strict-`fderiv`-`0` helpers (S4a) need the NON-vanishing partner factor to be
`ContDiffAt` (and the inverse factors `A0⁻¹/A1⁻¹/P00⁻¹/W⁻¹` smooth where their dets are nonzero, which
holds at `q = 0` where every read vanishes so `A0 = A1 = W = P00 = 1`). The reads (`l2A0/A1/Y0/Z1/Y1`)
are globally `ContDiff` (gauge reads composed with the `q ↦ (q.1, q.2.2)` projection), and `l2T1`
(=`coreLast`) is `ContDiff` (`contDiff_coreRead_entry`). The inverses are `ContDiffAt` at `0` by the
banked `contDiffAt_matrix_inv_entry_of_det_ne_zero`. -/

/-- The gauge-slot projection `q ↦ (q.1, q.2.2)` is `ContDiff` (the reads compose with it). -/
theorem contDiff_gaugeProj (H : Fin (L + 1) → ℕ) (r : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r (deepestNGauge H r) =>
      ((q.1, q.2.2) : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))) :=
  contDiff_fst.prodMk (contDiff_snd.snd)

/-- Each `l2A0` entry is globally `ContDiff` (`1 + readX_0` via the projection). -/
theorem contDiff_l2A0_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2A0 H r hr hL q i j) := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2A0 H r hr hL q i j)
      = fun q => (1 : Matrix (Fin r) (Fin r) ℝ) i j
          + readX H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L) i j := by
    funext q; rw [l2A0, Matrix.add_apply]
  rw [heq]
  exact contDiff_const.add ((contDiff_readX_entry H r hr hL (⟨0, by omega⟩ : Fin L) i j).comp
    (contDiff_gaugeProj H r))

/-- Each `l2A1` entry is globally `ContDiff`. -/
theorem contDiff_l2A1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2A1 H r hr hL q i j) := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2A1 H r hr hL q i j)
      = fun q => (1 : Matrix (Fin r) (Fin r) ℝ) i j
          + readX H r hr hL (q.1, q.2.2) (lastLayer hL) i j := by
    funext q; rw [l2A1, Matrix.add_apply]
  rw [heq]
  exact contDiff_const.add ((contDiff_readX_entry H r hr hL (lastLayer hL) i j).comp
    (contDiff_gaugeProj H r))

/-- Each `l2Y0` entry is globally `ContDiff` (`readY_0` reindexed; a `submatrix` of a `ContDiff` read). -/
theorem contDiff_l2Y0_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Y0 H r hr hL hL2eq q i j) := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2Y0 H r hr hL hL2eq q i j)
      = fun q => readY H r hr hL (q.1, q.2.2) (⟨0, by omega⟩ : Fin L) i
          ((finCongr (midWidth_eq_of_L2 H r hL hL2eq)).symm j) := by
    funext q
    rw [l2Y0, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply]
  rw [heq]
  exact (contDiff_readY_entry H r hr hL (⟨0, by omega⟩ : Fin L) i _).comp (contDiff_gaugeProj H r)

/-- Each `l2Z1` entry is globally `ContDiff`. -/
theorem contDiff_l2Z1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Z1 H r hr hL q i j) :=
  (contDiff_readZ_entry H r hr hL (lastLayer hL) i j).comp (contDiff_gaugeProj H r)

/-- Each `l2Y1` entry is globally `ContDiff`. -/
theorem contDiff_l2Y1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2Y1 H r hr hL q i j) :=
  (contDiff_readY_entry H r hr hL (lastLayer hL) i j).comp (contDiff_gaugeProj H r)

/-- Each `l2T1` (=`coreLast`) entry is globally `ContDiff` (`contDiff_coreRead_entry`). -/
theorem contDiff_l2T1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2T1 H r hr hL q i j) :=
  contDiff_coreRead_entry H r hr hL (lastLayer hL) i j

/-! ### S4e — the intermediate matrices at the split origin (`P00 = W = 1`, `K = R = U = S1 = Br = 0`)

At `q = 0` every read vanishes (S4b), so `A0 = A1 = 1` and `Y0 = Z1 = Y1 = T1 = 0`. Hence the products
`K = Z1·P00⁻¹·Y0`, `R = Z1·…·Y0`, `U = Z1·A1⁻¹·Y1` all vanish (a vanishing outer read), `P00 = W = 1`,
`S1 = T1 − U = 0`, `Br = (1−K)·S1 + U + R·T1 = 0`, and `T1' = W⁻¹·Br = 0`. -/

/-- `P00 = 1` at the origin. -/
theorem l2P00_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2P00 H r hr hL hL2eq 0 = 1 := by
  rw [l2P00, l2A0_zero, l2A1_zero, l2Y0_zero, l2Z1_zero, Matrix.one_mul,
    Matrix.mul_zero, add_zero]

/-- `det (P00 0) ≠ 0` (it is `1`). -/
theorem l2P00_det_zero_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    (l2P00 H r hr hL hL2eq 0).det ≠ 0 := by
  rw [l2P00_zero, Matrix.det_one]; exact one_ne_zero

/-- `det (A0 0) ≠ 0`. -/
theorem l2A0_det_zero_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (l2A0 H r hr hL 0).det ≠ 0 := by
  rw [l2A0_zero, Matrix.det_one]; exact one_ne_zero

/-- `det (A1 0) ≠ 0`. -/
theorem l2A1_det_zero_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (l2A1 H r hr hL 0).det ≠ 0 := by
  rw [l2A1_zero, Matrix.det_one]; exact one_ne_zero

/-- `K = 0` at the origin (`Z1 0 = 0`). -/
theorem l2K_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2K H r hr hL hL2eq 0 = 0 := by
  rw [l2K, l2Z1_zero, Matrix.zero_mul, Matrix.zero_mul]

/-- `R = 0` at the origin. -/
theorem l2R_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2R H r hr hL hL2eq 0 = 0 := by
  rw [l2R, l2Z1_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]

/-- `U = 0` at the origin. -/
theorem l2U_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    l2U H r hr hL 0 = 0 := by
  rw [l2U, l2Z1_zero, Matrix.zero_mul, Matrix.zero_mul]

/-- `W = 1` at the origin. -/
theorem l2W_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2W H r hr hL hL2eq 0 = 1 := by
  rw [l2W, l2R_zero, add_zero]

/-- `det (W 0) ≠ 0`. -/
theorem l2W_det_zero_ne (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    (l2W H r hr hL hL2eq 0).det ≠ 0 := by
  rw [l2W_zero, Matrix.det_one]; exact one_ne_zero

/-- `S1 = 0` at the origin. -/
theorem l2S1_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    l2S1 H r hr hL 0 = 0 := by
  rw [l2S1, l2T1_zero, l2U_zero, sub_zero]

/-- `Br = 0` at the origin (each summand carries a vanishing factor). -/
theorem l2Br_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2Br H r hr hL hL2eq 0 = 0 := by
  rw [l2Br, l2S1_zero, l2U_zero, l2R_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, add_zero]

/-- `T1' = 0` at the origin (`W⁻¹·Br = W⁻¹·0 = 0`). -/
theorem l2T1p_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    l2T1p H r hr hL hL2eq 0 = 0 := by
  rw [l2T1p_eq_Winv_Br, l2Br_zero, Matrix.mul_zero]

/-! ### S4f — entrywise `ContDiffAt` at the origin of the inverse and compound matrices

The non-vanishing partner factors in the entry helpers (S4a) must be `ContDiffAt 0`. The inverses
`A0⁻¹/A1⁻¹/P00⁻¹/W⁻¹` are `ContDiffAt 0` (det `= 1 ≠ 0` there); the compound matrices `K/R/U/S1/Br`
are sums/products of those with the globally-`ContDiff` reads. -/

/-- Each `A0⁻¹` entry is `ContDiffAt 0` (det `A0 0 = 1 ≠ 0`). -/
theorem contDiffAt_l2A0_inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A0 H r hr hL q)⁻¹ i j) 0 :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero (fun a b => contDiff_l2A0_entry H r hr hL a b)
    (l2A0_det_zero_ne H r hr hL) i j

/-- Each `A1⁻¹` entry is `ContDiffAt 0`. -/
theorem contDiffAt_l2A1_inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A1 H r hr hL q)⁻¹ i j) 0 :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero (fun a b => contDiff_l2A1_entry H r hr hL a b)
    (l2A1_det_zero_ne H r hr hL) i j

/-- Each `P00` entry is globally `ContDiff` (`A0·A1 + Y0·Z1`, products of `ContDiff` entries). -/
theorem contDiff_l2P00_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => l2P00 H r hr hL hL2eq q i j) := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2P00 H r hr hL hL2eq q i j)
      = fun q => (l2A0 H r hr hL q * l2A1 H r hr hL q) i j
          + (l2Y0 H r hr hL hL2eq q * l2Z1 H r hr hL q) i j := by
    funext q; rw [l2P00, Matrix.add_apply]
  rw [heq]
  refine ContDiff.add ?_ ?_
  · rw [contDiff_iff_contDiffAt]; intro x
    exact contDiffAt_matrix_mul_entry (fun a k => (contDiff_l2A0_entry H r hr hL a k).contDiffAt)
      (fun k b => (contDiff_l2A1_entry H r hr hL k b).contDiffAt) i j
  · rw [contDiff_iff_contDiffAt]; intro x
    exact contDiffAt_matrix_mul_entry
      (fun a k => (contDiff_l2Y0_entry H r hr hL hL2eq a k).contDiffAt)
      (fun k b => (contDiff_l2Z1_entry H r hr hL k b).contDiffAt) i j

/-- Each `P00⁻¹` entry is `ContDiffAt 0`. -/
theorem contDiffAt_l2P00_inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2P00 H r hr hL hL2eq q)⁻¹ i j) 0 :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero (fun a b => contDiff_l2P00_entry H r hr hL hL2eq a b)
    (l2P00_det_zero_ne H r hr hL hL2eq) i j

/-- Each `R` entry is `ContDiffAt 0` (`Z1·A1⁻¹·A0⁻¹·Y0`; reads `ContDiff`, inverses `ContDiffAt 0`). -/
theorem contDiffAt_l2R_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2R H r hr hL hL2eq q i j) 0 := by
  have hZA1 : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) a k) 0 := fun a k =>
    contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' j' => contDiffAt_l2A1_inv_entry H r hr hL k' j') a k
  have hZA1A0 : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) a k) 0 := fun a k =>
    contDiffAt_matrix_mul_entry hZA1 (fun k' j' => contDiffAt_l2A0_inv_entry H r hr hL k' j') a k
  exact contDiffAt_matrix_mul_entry hZA1A0
    (fun k' j' => (contDiff_l2Y0_entry H r hr hL hL2eq k' j').contDiffAt) i j

/-- Each `U` entry is `ContDiffAt 0` (`Z1·A1⁻¹·Y1`). -/
theorem contDiffAt_l2U_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2U H r hr hL q i j) 0 := by
  have hZA1 : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) a k) 0 := fun a k =>
    contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' j' => contDiffAt_l2A1_inv_entry H r hr hL k' j') a k
  exact contDiffAt_matrix_mul_entry hZA1
    (fun k' j' => (contDiff_l2Y1_entry H r hr hL k' j').contDiffAt) i j

/-- Each `K` entry is `ContDiffAt 0` (`Z1·P00⁻¹·Y0`). -/
theorem contDiffAt_l2K_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2K H r hr hL hL2eq q i j) 0 := by
  have hZP : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹) a k) 0 := fun a k =>
    contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' j' => contDiffAt_l2P00_inv_entry H r hr hL hL2eq k' j') a k
  exact contDiffAt_matrix_mul_entry hZP
    (fun k' j' => (contDiff_l2Y0_entry H r hr hL hL2eq k' j').contDiffAt) i j

/-- Each `S1` entry is `ContDiffAt 0` (`T1 − U`). -/
theorem contDiffAt_l2S1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2S1 H r hr hL q i j) 0 := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2S1 H r hr hL q i j)
      = fun q => l2T1 H r hr hL q i j - l2U H r hr hL q i j := by
    funext q; rw [l2S1, Matrix.sub_apply]
  rw [heq]
  exact (contDiff_l2T1_entry H r hr hL i j).contDiffAt.sub (contDiffAt_l2U_entry H r hr hL i j)

/-- Each `(1−K)` entry is `ContDiffAt 0`. -/
theorem contDiffAt_l2OneSubK_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (a k : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (1 - l2K H r hr hL hL2eq q) a k) 0 := by
  have hsub : (fun q : DeepestSplit H r (deepestNGauge H r) => (1 - l2K H r hr hL hL2eq q) a k)
      = fun q => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
          (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) a k - l2K H r hr hL hL2eq q a k := by
    funext q; rw [Matrix.sub_apply]
  rw [hsub]
  exact contDiffAt_const.sub (contDiffAt_l2K_entry H r hr hL hL2eq a k)

/-- Each `(1−K)·S1` entry is `ContDiffAt 0`. -/
theorem contDiffAt_l2OneSubK_mul_S1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (((1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j) 0 :=
  contDiffAt_matrix_mul_entry
    (A := fun q : DeepestSplit H r (deepestNGauge H r) => 1 - l2K H r hr hL hL2eq q)
    (B := fun q : DeepestSplit H r (deepestNGauge H r) => l2S1 H r hr hL q)
    (fun a k => contDiffAt_l2OneSubK_entry H r hr hL hL2eq a k)
    (fun k b => contDiffAt_l2S1_entry H r hr hL k b) i j

/-- Each `R·T1` entry is `ContDiffAt 0`. -/
theorem contDiffAt_l2R_mul_T1_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        ((l2R H r hr hL hL2eq q * l2T1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j) 0 :=
  contDiffAt_matrix_mul_entry
    (A := fun q : DeepestSplit H r (deepestNGauge H r) => l2R H r hr hL hL2eq q)
    (B := fun q : DeepestSplit H r (deepestNGauge H r) => l2T1 H r hr hL q)
    (fun a k => contDiffAt_l2R_entry H r hr hL hL2eq a k)
    (fun k b => (contDiff_l2T1_entry H r hr hL k b).contDiffAt) i j

/-- Each `Br` entry is `ContDiffAt 0` (`(1−K)·S1 + U + R·T1`). -/
theorem contDiffAt_l2Br_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2Br H r hr hL hL2eq q i j) 0 := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2Br H r hr hL hL2eq q i j)
      = fun q => (((1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL q :
            Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j
          + l2U H r hr hL q i j
          + ((l2R H r hr hL hL2eq q * l2T1 H r hr hL q :
            Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j := by
    funext q; rw [l2Br, Matrix.add_apply, Matrix.add_apply]
  rw [heq]
  exact ((contDiffAt_l2OneSubK_mul_S1_entry H r hr hL hL2eq i j).add
    (contDiffAt_l2U_entry H r hr hL i j)).add (contDiffAt_l2R_mul_T1_entry H r hr hL hL2eq i j)

/-- Each `W⁻¹` entry is `ContDiffAt 0` (the `_at` inverse variant — `W` carries `A0⁻¹/A1⁻¹`). -/
theorem contDiffAt_l2W_inv_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2W H r hr hL hL2eq q)⁻¹ i j) 0 := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero_at (fun a b => ?_)
    (l2W_det_zero_ne H r hr hL hL2eq) i j
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2W H r hr hL hL2eq q a b)
      = fun q => (1 : Matrix _ _ ℝ) a b + l2R H r hr hL hL2eq q a b := by
    funext q; rw [l2W, Matrix.add_apply]
  rw [heq]
  exact contDiffAt_const.add (contDiffAt_l2R_entry H r hr hL hL2eq a b)

/-! ### S4f' — entrywise `ContDiffAt` at a GENERAL point `p` (with det hypotheses; for S2)

S2 needs `ContDiffAt` not at the origin but at any `p` in the cutoff support. The inverses are
`ContDiffAt p` exactly where their dets are nonzero at `p`; the compound matrices then follow. These
mirror the at-`0` facts with the det conditions threaded through `p`. -/

/-- Each `A0⁻¹` entry is `ContDiffAt p` when `det (A0 p) ≠ 0`. -/
theorem contDiffAt_l2A0_inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : DeepestSplit H r (deepestNGauge H r)) (hp : (l2A0 H r hr hL p).det ≠ 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A0 H r hr hL q)⁻¹ i j) p :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero (fun a b => contDiff_l2A0_entry H r hr hL a b) hp i j

/-- Each `A1⁻¹` entry is `ContDiffAt p` when `det (A1 p) ≠ 0`. -/
theorem contDiffAt_l2A1_inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : DeepestSplit H r (deepestNGauge H r)) (hp : (l2A1 H r hr hL p).det ≠ 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2A1 H r hr hL q)⁻¹ i j) p :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero (fun a b => contDiff_l2A1_entry H r hr hL a b) hp i j

/-- Each `P00⁻¹` entry is `ContDiffAt p` when `det (P00 p) ≠ 0`. -/
theorem contDiffAt_l2P00_inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r)) (hp : (l2P00 H r hr hL hL2eq p).det ≠ 0) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2P00 H r hr hL hL2eq q)⁻¹ i j) p :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero (fun a b => contDiff_l2P00_entry H r hr hL hL2eq a b)
    hp i j

/-- Each `R` entry is `ContDiffAt p` when `det A0, det A1 ≠ 0` at `p`. -/
theorem contDiffAt_l2R_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL p).det ≠ 0) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2R H r hr hL hL2eq q i j) p := by
  have hZA1 : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) a k) p := fun a k =>
    contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' j' => contDiffAt_l2A1_inv_entry_at H r hr hL p hA1 k' j') a k
  have hZA1A0 : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) a k) p := fun a k =>
    contDiffAt_matrix_mul_entry hZA1 (fun k' j' => contDiffAt_l2A0_inv_entry_at H r hr hL p hA0 k' j')
      a k
  exact contDiffAt_matrix_mul_entry hZA1A0
    (fun k' j' => (contDiff_l2Y0_entry H r hr hL hL2eq k' j').contDiffAt) i j

/-- Each `U` entry is `ContDiffAt p` when `det A1 ≠ 0` at `p`. -/
theorem contDiffAt_l2U_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : DeepestSplit H r (deepestNGauge H r)) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2U H r hr hL q i j) p := by
  have hZA1 : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2A1 H r hr hL q)⁻¹) a k) p := fun a k =>
    contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' j' => contDiffAt_l2A1_inv_entry_at H r hr hL p hA1 k' j') a k
  exact contDiffAt_matrix_mul_entry hZA1
    (fun k' j' => (contDiff_l2Y1_entry H r hr hL k' j').contDiffAt) i j

/-- Each `K` entry is `ContDiffAt p` when `det P00 ≠ 0` at `p`. -/
theorem contDiffAt_l2K_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r)) (hP00 : (l2P00 H r hr hL hL2eq p).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2K H r hr hL hL2eq q i j) p := by
  have hZP : ∀ a k, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (l2Z1 H r hr hL q * (l2P00 H r hr hL hL2eq q)⁻¹) a k) p := fun a k =>
    contDiffAt_matrix_mul_entry (fun a' k' => (contDiff_l2Z1_entry H r hr hL a' k').contDiffAt)
      (fun k' j' => contDiffAt_l2P00_inv_entry_at H r hr hL hL2eq p hP00 k' j') a k
  exact contDiffAt_matrix_mul_entry hZP
    (fun k' j' => (contDiff_l2Y0_entry H r hr hL hL2eq k' j').contDiffAt) i j

/-- Each `S1` entry is `ContDiffAt p` when `det A1 ≠ 0` at `p`. -/
theorem contDiffAt_l2S1_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : DeepestSplit H r (deepestNGauge H r)) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2S1 H r hr hL q i j) p := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2S1 H r hr hL q i j)
      = fun q => l2T1 H r hr hL q i j - l2U H r hr hL q i j := by
    funext q; rw [l2S1, Matrix.sub_apply]
  rw [heq]
  exact (contDiff_l2T1_entry H r hr hL i j).contDiffAt.sub (contDiffAt_l2U_entry_at H r hr hL p hA1 i j)

/-- Each `Br` entry is `ContDiffAt p` when `det A0, A1, P00 ≠ 0` at `p`. -/
theorem contDiffAt_l2Br_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL p).det ≠ 0) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2eq p).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2Br H r hr hL hL2eq q i j) p := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2Br H r hr hL hL2eq q i j)
      = fun q => (((1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL q :
            Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j
          + l2U H r hr hL q i j
          + ((l2R H r hr hL hL2eq q * l2T1 H r hr hL q :
            Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j := by
    funext q; rw [l2Br, Matrix.add_apply, Matrix.add_apply]
  rw [heq]
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (((1 - l2K H r hr hL hL2eq q) * l2S1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j) p :=
    contDiffAt_matrix_mul_entry
      (A := fun q : DeepestSplit H r (deepestNGauge H r) => 1 - l2K H r hr hL hL2eq q)
      (B := fun q : DeepestSplit H r (deepestNGauge H r) => l2S1 H r hr hL q)
      (fun a k => by
        have hsub : (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (1 - l2K H r hr hL hL2eq q) a k)
            = fun q => (1 : Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).castSucc)) ℝ) a k
              - l2K H r hr hL hL2eq q a k := by funext q; rw [Matrix.sub_apply]
        rw [hsub]
        exact contDiffAt_const.sub (contDiffAt_l2K_entry_at H r hr hL hL2eq p hP00 a k))
      (fun k b => contDiffAt_l2S1_entry_at H r hr hL p hA1 k b) i j
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        ((l2R H r hr hL hL2eq q * l2T1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j) p :=
    contDiffAt_matrix_mul_entry
      (A := fun q : DeepestSplit H r (deepestNGauge H r) => l2R H r hr hL hL2eq q)
      (B := fun q : DeepestSplit H r (deepestNGauge H r) => l2T1 H r hr hL q)
      (fun a k => contDiffAt_l2R_entry_at H r hr hL hL2eq p hA0 hA1 a k)
      (fun k b => (contDiff_l2T1_entry H r hr hL k b).contDiffAt) i j
  exact (h1.add (contDiffAt_l2U_entry_at H r hr hL p hA1 i j)).add h3

/-- Each `W` entry is `ContDiffAt p` when `det A0, A1 ≠ 0` at `p`. -/
theorem contDiffAt_l2W_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL p).det ≠ 0) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2W H r hr hL hL2eq q i j) p := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2W H r hr hL hL2eq q i j)
      = fun q => (1 : Matrix _ _ ℝ) i j + l2R H r hr hL hL2eq q i j := by
    funext q; rw [l2W, Matrix.add_apply]
  rw [heq]
  exact contDiffAt_const.add (contDiffAt_l2R_entry_at H r hr hL hL2eq p hA0 hA1 i j)

/-- Each `W⁻¹` entry is `ContDiffAt p` when `det A0, A1 ≠ 0` and `det W ≠ 0` at `p`. -/
theorem contDiffAt_l2W_inv_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL p).det ≠ 0) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (hW : (l2W H r hr hL hL2eq p).det ≠ 0)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2W H r hr hL hL2eq q)⁻¹ i j) p :=
  contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (fun a b => contDiffAt_l2W_entry_at H r hr hL hL2eq p hA0 hA1 a b) hW i j

/-- `l2Y1p = Y1 + A0⁻¹·Y0·(T1 − T1')` (`rfl` from the def). -/
theorem l2Y1p_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2Y1p H r hr hL hL2eq q
      = l2Y1 H r hr hL q + (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q
        * (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) := rfl

/-- Each `T1'` (=`l2T1p`) entry is `ContDiffAt p` when `det A0, A1, P00, W ≠ 0` at `p` (`W⁻¹·Br`). -/
theorem contDiffAt_l2T1p_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL p).det ≠ 0) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2eq p).det ≠ 0) (hW : (l2W H r hr hL hL2eq p).det ≠ 0)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2T1p H r hr hL hL2eq q i j) p := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2T1p H r hr hL hL2eq q i j)
      = fun q => ((l2W H r hr hL hL2eq q)⁻¹ * l2Br H r hr hL hL2eq q) i j := by
    funext q; rw [l2T1p_eq_Winv_Br]
  rw [heq]
  exact contDiffAt_matrix_mul_entry
    (fun a k => contDiffAt_l2W_inv_entry_at H r hr hL hL2eq p hA0 hA1 hW a k)
    (fun k b => contDiffAt_l2Br_entry_at H r hr hL hL2eq p hA0 hA1 hP00 k b) i j

/-- Each `Y1'` (=`l2Y1p`) entry is `ContDiffAt p` when `det A0, A1, P00, W ≠ 0` at `p`
(`Y1 + A0⁻¹·Y0·(T1 − T1')`). -/
theorem contDiffAt_l2Y1p_entry_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (p : DeepestSplit H r (deepestNGauge H r))
    (hA0 : (l2A0 H r hr hL p).det ≠ 0) (hA1 : (l2A1 H r hr hL p).det ≠ 0)
    (hP00 : (l2P00 H r hr hL hL2eq p).det ≠ 0) (hW : (l2W H r hr hL hL2eq p).det ≠ 0)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => l2Y1p H r hr hL hL2eq q i j) p := by
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2Y1p H r hr hL hL2eq q i j)
      = fun q => l2Y1 H r hr hL q i j
          + (((l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q
              * (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) :
            Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j := by
    funext q; rw [l2Y1p_eq, Matrix.add_apply]
  rw [heq]
  refine (contDiff_l2Y1_entry H r hr hL i j).contDiffAt.add ?_
  -- `(A0⁻¹·Y0)·(T1 − T1')` entry: mul-entry of the `ContDiffAt` factors.
  refine contDiffAt_matrix_mul_entry
    (A := fun q : DeepestSplit H r (deepestNGauge H r) =>
      (l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q)
    (B := fun q : DeepestSplit H r (deepestNGauge H r) =>
      l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) (fun a k => ?_) (fun k b => ?_) i j
  · exact contDiffAt_matrix_mul_entry
      (fun a' k' => contDiffAt_l2A0_inv_entry_at H r hr hL p hA0 a' k')
      (fun k' b' => (contDiff_l2Y0_entry H r hr hL hL2eq k' b').contDiffAt) a k
  · have hsub : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) k b)
        = fun q => l2T1 H r hr hL q k b - l2T1p H r hr hL hL2eq q k b := by
      funext q; rw [Matrix.sub_apply]
    rw [hsub]
    exact (contDiff_l2T1_entry H r hr hL k b).contDiffAt.sub
      (contDiffAt_l2T1p_entry_at H r hr hL hL2eq p hA0 hA1 hP00 hW k b)

/-! ### S4g — the `O(read²)` strict-`fderiv`-`0` blocks (`K`, `R`, `W⁻¹ − 1`)

The genuine higher-order vanishing: `K = Z1·P00⁻¹·Y0` and `R = Z1·A1⁻¹·A0⁻¹·Y0` are triple products
with the two outer READS (`Z1`, `Y0`) vanishing at `0`, so each entry has strict-`fderiv`-`0` (the
triple helper; the inner factors merely `ContDiffAt`). `W⁻¹ − 1 = −(W⁻¹·R)` on `{det W ≠ 0}` (a nbhd of
`0`), and `R` value+deriv vanish, so `W⁻¹ − 1` is strict-`fderiv`-`0` (right-zero helper + `eventuallyEq`). -/

/-- Each `K` entry has strict-`fderiv`-`0` at `0` (`Z1·(P00⁻¹)·Y0`, outer reads `Z1`,`Y0` vanish). -/
theorem hasStrictFDerivAt_l2K_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => l2K H r hr hL hL2eq q i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
  hasStrictFDerivAt_matrix_triple_mul_entry_zero
    (A := fun q => l2Z1 H r hr hL q) (B := fun q => (l2P00 H r hr hL hL2eq q)⁻¹)
    (C := fun q => l2Y0 H r hr hL hL2eq q) i j
    (fun a b => (contDiff_l2Z1_entry H r hr hL a b).contDiffAt)
    (fun a b => contDiffAt_l2P00_inv_entry H r hr hL hL2eq a b)
    (fun a b => (contDiff_l2Y0_entry H r hr hL hL2eq a b).contDiffAt)
    (fun a b => by simp only [l2Z1_zero, Matrix.zero_apply])
    (fun a b => by simp only [l2Y0_zero, Matrix.zero_apply])

/-- Each `R` entry has strict-`fderiv`-`0` at `0` (`Z1·(A1⁻¹·A0⁻¹)·Y0`, outer reads vanish). -/
theorem hasStrictFDerivAt_l2R_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => l2R H r hr hL hL2eq q i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  -- Regroup `Z1·A1⁻¹·A0⁻¹·Y0 = Z1·(A1⁻¹·A0⁻¹)·Y0` (triple, middle `A1⁻¹·A0⁻¹`).
  have hmid : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹) a b) 0 := fun a b =>
    contDiffAt_matrix_mul_entry (fun a' k' => contDiffAt_l2A1_inv_entry H r hr hL a' k')
      (fun k' b' => contDiffAt_l2A0_inv_entry H r hr hL k' b') a b
  have hbase := hasStrictFDerivAt_matrix_triple_mul_entry_zero
    (A := fun q => l2Z1 H r hr hL q)
    (B := fun q => (l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹)
    (C := fun q => l2Y0 H r hr hL hL2eq q) i j
    (fun a b => (contDiff_l2Z1_entry H r hr hL a b).contDiffAt) hmid
    (fun a b => (contDiff_l2Y0_entry H r hr hL hL2eq a b).contDiffAt)
    (fun a b => by simp only [l2Z1_zero, Matrix.zero_apply])
    (fun a b => by simp only [l2Y0_zero, Matrix.zero_apply])
  -- `Z1·(A1⁻¹·A0⁻¹)·Y0 = Z1·A1⁻¹·A0⁻¹·Y0 = R` entrywise (left-assoc associativity).
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards with q
  show ((l2Z1 H r hr hL q * ((l2A1 H r hr hL q)⁻¹ * (l2A0 H r hr hL q)⁻¹))
      * l2Y0 H r hr hL hL2eq q) i j = l2R H r hr hL hL2eq q i j
  rw [l2R, ← Matrix.mul_assoc]

/-- `W⁻¹ − 1 = −(W⁻¹·R)` on `{det W ≠ 0}` (`nonsing_inv_mul`: `W⁻¹·W = 1`, `W = 1 + R`). -/
theorem l2Winv_sub_one_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hdet : (l2W H r hr hL hL2eq q).det ≠ 0) :
    (l2W H r hr hL hL2eq q)⁻¹ - 1 = -((l2W H r hr hL hL2eq q)⁻¹ * l2R H r hr hL hL2eq q) := by
  have hWR : l2R H r hr hL hL2eq q = l2W H r hr hL hL2eq q - 1 := by
    rw [l2W]; abel
  have hinvmul : (l2W H r hr hL hL2eq q)⁻¹ * l2W H r hr hL hL2eq q = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  rw [hWR, Matrix.mul_sub, Matrix.mul_one, hinvmul, neg_sub]

/-- Each `W⁻¹ − 1` entry has strict-`fderiv`-`0` at `0` (right-zero helper on `−(W⁻¹·R)`, `R` vanishes
value+deriv; lifted by `eventuallyEq` on the open `{det W ≠ 0}`). -/
theorem hasStrictFDerivAt_l2Winv_sub_one_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i j : Fin (deepestM H r (lastLayer hL).castSucc)) :
    HasStrictFDerivAt (fun q => ((l2W H r hr hL hL2eq q)⁻¹ - 1) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  -- The `−(W⁻¹·R)` entry has strict-deriv-`0` (right-zero helper: `R` value+deriv `0`, `W⁻¹` partner).
  have hWR : HasStrictFDerivAt
      (fun q => (-((l2W H r hr hL hL2eq q)⁻¹ * l2R H r hr hL hL2eq q)) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
    have hmul : HasStrictFDerivAt
        (fun q => ((l2W H r hr hL hL2eq q)⁻¹ * l2R H r hr hL hL2eq q) i j)
        (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
      hasStrictFDerivAt_matrix_mul_entry_of_right_zero (i := i) (j := j)
        (fun k => contDiffAt_l2W_inv_entry H r hr hL hL2eq i k)
        (fun k => hasStrictFDerivAt_l2R_entry_zero H r hr hL hL2eq k j)
        (fun k => by simp only [l2R_zero, Matrix.zero_apply])
    have heq : (fun q => (-((l2W H r hr hL hL2eq q)⁻¹ * l2R H r hr hL hL2eq q)) i j)
        = fun q => -(((l2W H r hr hL hL2eq q)⁻¹ * l2R H r hr hL hL2eq q) i j) := by
      funext q; rw [Matrix.neg_apply]
    rw [heq]
    simpa using hmul.neg
  -- On `{det W ≠ 0}` (a nbhd of `0` since `det W` is `ContDiffAt 0` and `det W 0 = 1 ≠ 0`),
  -- `W⁻¹ − 1 = −(W⁻¹·R)`.
  refine hWR.congr_of_eventuallyEq ?_
  have hdetCD : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (l2W H r hr hL hL2eq q).det) 0 := by
    refine contDiffAt_matrix_det_of_entries (fun a b => ?_)
    have heq : (fun q : DeepestSplit H r (deepestNGauge H r) => l2W H r hr hL hL2eq q a b)
        = fun q => (1 : Matrix _ _ ℝ) a b + l2R H r hr hL hL2eq q a b := by
      funext q; rw [l2W, Matrix.add_apply]
    rw [heq]
    exact contDiffAt_const.add (contDiffAt_l2R_entry H r hr hL hL2eq a b)
  have hne : ∀ᶠ q in nhds (0 : DeepestSplit H r (deepestNGauge H r)),
      (l2W H r hr hL hL2eq q).det ≠ 0 := by
    have hca : ContinuousAt (fun q => (l2W H r hr hL hL2eq q).det) 0 :=
      hdetCD.continuousAt
    have : (l2W H r hr hL hL2eq (0 : DeepestSplit H r (deepestNGauge H r))).det ≠ 0 :=
      l2W_det_zero_ne H r hr hL hL2eq
    exact hca.eventually_ne this
  filter_upwards [hne] with q hq
  rw [l2Winv_sub_one_eq H r hr hL hL2eq q hq]

/-! ### S4h — the matrix normalization `T1' − T1 = (W⁻¹ − 1)·Br + (Br − T1)`

Purely additive/distributive matrix identities (no `W`-invertibility needed): `Br − T1 = −(K·S1) + R·T1`
(via `S1 = T1 − U` and `(1−K)·S1 = S1 − K·S1`), and `T1' − T1 = W⁻¹·Br − T1 = (W⁻¹−1)·Br + (Br − T1)`
(via `(W⁻¹−1)·Br = W⁻¹·Br − Br`). These split the entry derivative into the `O(read²)` blocks. -/

/-- `Br − T1 = −(K·S1) + R·T1` (additive: `(1−K)·S1 + U = (T1 − U) − K·S1 + U = T1 − K·S1`). -/
theorem l2Br_sub_T1_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2Br H r hr hL hL2eq q - l2T1 H r hr hL q
      = -(l2K H r hr hL hL2eq q * l2S1 H r hr hL q)
        + l2R H r hr hL hL2eq q * l2T1 H r hr hL q := by
  rw [l2Br, l2S1, Matrix.sub_mul, Matrix.one_mul]
  -- `(T1 − U) − K·(T1 − U) + U + R·T1 − T1`. Reduce: `(T1 − U) + U − T1 = 0`, leaving `−K·(T1−U) + R·T1`.
  -- But `S1 = T1 − U`, so `−K·S1`. Use `abel` after isolating the `−(K * (T1 − U))` term.
  have hexpand : l2T1 H r hr hL q - l2U H r hr hL q
        - l2K H r hr hL hL2eq q * (l2T1 H r hr hL q - l2U H r hr hL q)
        + l2U H r hr hL q + l2R H r hr hL hL2eq q * l2T1 H r hr hL q
        - l2T1 H r hr hL q
      = -(l2K H r hr hL hL2eq q * (l2T1 H r hr hL q - l2U H r hr hL q))
        + l2R H r hr hL hL2eq q * l2T1 H r hr hL q := by abel
  rw [hexpand]

/-- `T1' − T1 = (W⁻¹ − 1)·Br + (Br − T1)` (additive: `(W⁻¹−1)·Br = W⁻¹·Br − Br`). -/
theorem l2T1p_sub_T1_eq (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q
      = ((l2W H r hr hL hL2eq q)⁻¹ - 1) * l2Br H r hr hL hL2eq q
        + (l2Br H r hr hL hL2eq q - l2T1 H r hr hL q) := by
  rw [l2T1p_eq_Winv_Br, Matrix.sub_mul, Matrix.one_mul]
  abel

/-! ### S4i — the two payload-block entry strict-`fderiv`-`0` facts (`T1' − T1`, `Y1' − Y1`)

Assemble: `(T1'−T1)_{ij} = ((W⁻¹−1)·Br)_{ij} + (−(K·S1)+R·T1)_{ij}` (the normalization), each entry-helper
on a block whose left factor (`W⁻¹−1`, `K`, `R`) vanishes value+deriv at `0`. `(Y1'−Y1)_{ij} =
(A0⁻¹·Y0·(T1−T1'))_{ij}`, with `Y0` (right of `A0⁻¹·Y0`) value+deriv... no — `Y0` is a read (deriv ≠ 0);
the vanishing comes from the RIGHT factor `(T1−T1')`, which is `0` value+deriv (right-zero helper). -/

/-- Each `(K·S1)` entry has strict-`fderiv`-`0` at `0` (left `K` vanishes value+deriv, `S1` `ContDiffAt`). -/
theorem hasStrictFDerivAt_l2K_mul_S1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        ((l2K H r hr hL hL2eq q * l2S1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
  hasStrictFDerivAt_matrix_mul_entry_of_left_zero (i := i) (j := j)
    (fun k => hasStrictFDerivAt_l2K_entry_zero H r hr hL hL2eq i k)
    (fun k => by simp only [l2K_zero, Matrix.zero_apply])
    (fun k => contDiffAt_l2S1_entry H r hr hL k j)

/-- Each `(R·T1)` entry has strict-`fderiv`-`0` at `0` (left `R` vanishes value+deriv). -/
theorem hasStrictFDerivAt_l2R_mul_T1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        ((l2R H r hr hL hL2eq q * l2T1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
  hasStrictFDerivAt_matrix_mul_entry_of_left_zero (i := i) (j := j)
    (fun k => hasStrictFDerivAt_l2R_entry_zero H r hr hL hL2eq i k)
    (fun k => by simp only [l2R_zero, Matrix.zero_apply])
    (fun k => (contDiff_l2T1_entry H r hr hL k j).contDiffAt)

/-- Each `((W⁻¹−1)·Br)` entry has strict-`fderiv`-`0` at `0` (left `W⁻¹−1` vanishes value+deriv). -/
theorem hasStrictFDerivAt_l2WinvSub1_mul_Br_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        ((((l2W H r hr hL hL2eq q)⁻¹ - 1) * l2Br H r hr hL hL2eq q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 :=
  hasStrictFDerivAt_matrix_mul_entry_of_left_zero (i := i) (j := j)
    (fun k => hasStrictFDerivAt_l2Winv_sub_one_entry_zero H r hr hL hL2eq i k)
    (fun k => by
      simp only [Matrix.sub_apply, l2W_zero, inv_one, sub_self, Matrix.zero_apply])
    (fun k => contDiffAt_l2Br_entry H r hr hL hL2eq k j)

/-- **Each `T1' − T1` entry has strict-`fderiv`-`0` at `0`** (the core payload-block; the
normalization `T1'−T1 = (W⁻¹−1)·Br + (−(K·S1) + R·T1)`, each summand strict-`fderiv`-`0`). -/
theorem hasStrictFDerivAt_l2T1p_sub_T1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin (deepestM H r (lastLayer hL).castSucc)) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  -- Rewrite the entry via the two matrix normalizations.
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) i j)
      = fun q => ((((l2W H r hr hL hL2eq q)⁻¹ - 1) * l2Br H r hr hL hL2eq q :
            Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
              (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j
          + (-((l2K H r hr hL hL2eq q * l2S1 H r hr hL q :
              Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
                (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j
            + ((l2R H r hr hL hL2eq q * l2T1 H r hr hL q :
              Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
                (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j) := by
    funext q
    rw [l2T1p_sub_T1_eq, Matrix.add_apply, l2Br_sub_T1_eq, Matrix.add_apply, Matrix.neg_apply]
  rw [heq]
  -- `−(K·S1)` entry strict-deriv-`0` (the negation of the `K·S1` block fact).
  have hnegKS1 : HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        -((l2K H r hr hL hL2eq q * l2S1 H r hr hL q :
          Matrix (Fin (deepestM H r (lastLayer hL).castSucc))
            (Fin (deepestM H r (lastLayer hL).succ)) ℝ)) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_l2K_mul_S1_entry_zero H r hr hL hL2eq i j).neg
  have hsum := (hasStrictFDerivAt_l2WinvSub1_mul_Br_entry_zero H r hr hL hL2eq i j).add
    (hnegKS1.add (hasStrictFDerivAt_l2R_mul_T1_entry_zero H r hr hL hL2eq i j))
  simpa only [add_zero, Pi.add_apply] using hsum

/-- **Each `Y1' − Y1` entry has strict-`fderiv`-`0` at `0`** (the reg payload-block;
`Y1'−Y1 = (A0⁻¹·Y0)·(T1−T1')`, right factor `(T1−T1')` vanishes value+deriv). -/
theorem hasStrictFDerivAt_l2Y1p_sub_Y1_entry_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (i : Fin r) (j : Fin (deepestM H r (lastLayer hL).succ)) :
    HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
  -- `Y1'−Y1 = (A0⁻¹·Y0)·(T1−T1')` entrywise.
  have heq : (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j)
      = fun q => (((l2A0 H r hr hL q)⁻¹ * l2Y0 H r hr hL hL2eq q)
          * (l2T1 H r hr hL q - l2T1p H r hr hL hL2eq q) :
          Matrix (Fin r) (Fin (deepestM H r (lastLayer hL).succ)) ℝ) i j := by
    funext q
    rw [l2Y1p_eq, Matrix.sub_apply, Matrix.add_apply, add_sub_cancel_left]
  rw [heq]
  -- Right-zero helper: partner `A0⁻¹·Y0` `ContDiffAt`; right `(T1−T1')` value+deriv `0`.
  refine hasStrictFDerivAt_matrix_mul_entry_of_right_zero (i := i) (j := j) (fun k => ?_)
    (fun k => ?_) (fun k => ?_)
  · exact contDiffAt_matrix_mul_entry (fun a k' => contDiffAt_l2A0_inv_entry H r hr hL a k')
      (fun k' b => (contDiff_l2Y0_entry H r hr hL hL2eq k' b).contDiffAt) i k
  · -- `(T1 − T1')_{kj}` strict-deriv-`0` = negation of `(T1'−T1)_{kj}`.
    have hneg : HasStrictFDerivAt (fun q : DeepestSplit H r (deepestNGauge H r) =>
        -((l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) k j))
        (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] ℝ) 0 := by
      have := (hasStrictFDerivAt_l2T1p_sub_T1_entry_zero H r hr hL hL2eq k j).neg
      rwa [neg_zero] at this
    refine hneg.congr_of_eventuallyEq ?_
    filter_upwards with q
    rw [Matrix.sub_apply, Matrix.sub_apply, neg_sub]
  · -- `(T1 − T1')_{kj} 0 = 0` (both `T1 0 = 0`, `T1' 0 = 0`).
    show (l2T1 H r hr hL 0 - l2T1p H r hr hL hL2eq 0) k j = 0
    rw [l2T1_zero, l2T1p_zero, sub_zero]; rfl

/-! ### S4j — the encoded core payload `paramsEquivFlatCLE (l2CoreΔTuple)` has strict-`fderiv`-`0`

Flat-coordinate route (mirrors `hasStrictFDerivAt_schurShiftRaw_zero`): each flat coordinate `k` decodes
(by `rfl`) to `(l2CoreΔTuple q) d.1.1 d.1.2 d.2`, which (`Function.update 0 lastLayer (T1'−T1)`) is
`(T1'−T1) d.1.2 d.2` if `d.1.1 = lastLayer` (strict-`fderiv`-`0` by the core payload-block fact) and `0`
otherwise (`const`). `paramsEquivFlatCLE = paramsEquivFlat` as functions. -/

/-- The encoded core payload `paramsEquivFlat (l2CoreΔTuple)` has strict-`fderiv`-`0` at `0`. -/
theorem hasStrictFDerivAt_paramsEquivFlat_l2CoreΔTuple_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt
      (fun q => paramsEquivFlat (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  refine hasStrictFDerivAt_pi'.2 (fun k => ?_)
  rw [ContinuousLinearMap.comp_zero]
  -- The flat coordinate decodes to `(l2CoreΔTuple q) d.1.1 d.1.2 d.2` (by `rfl`).
  set d := (Fintype.equivFin (FlatIdx (deepestM H r))).symm k with hd
  have hcoord : (fun q => paramsEquivFlat (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q) k)
      = fun q => l2CoreΔTuple H r hr hL hL2eq q d.1.1 d.1.2 d.2 := rfl
  rw [hcoord]
  -- Make `d` opaque, then destructure so the `lastLayer` case can substitute the layer.
  clear_value d
  obtain ⟨⟨s₀, i₀⟩, j₀⟩ := d
  rcases eq_or_ne s₀ (lastLayer hL) with hlast | hlast
  · -- Last layer: the update writes `T1' − T1`. Substituting `s₀ = lastLayer` aligns the widths.
    subst hlast
    have heq : (fun q => l2CoreΔTuple H r hr hL hL2eq q (lastLayer hL) i₀ j₀)
        = fun q => (l2T1p H r hr hL hL2eq q - l2T1 H r hr hL q) i₀ j₀ := by
      funext q
      rw [l2CoreΔTuple, Function.update_self]
    rw [heq]
    exact hasStrictFDerivAt_l2T1p_sub_T1_entry_zero H r hr hL hL2eq i₀ j₀
  · -- Other layers: the update leaves `0`.
    have heq : (fun q => l2CoreΔTuple H r hr hL hL2eq q s₀ i₀ j₀)
        = fun _ : DeepestSplit H r (deepestNGauge H r) => (0 : ℝ) := by
      funext q
      rw [l2CoreΔTuple, Function.update_of_ne hlast]; rfl
    rw [heq]
    exact hasStrictFDerivAt_const _ _

/-- The encoded core payload via the CLE has strict-`fderiv`-`0` at `0` (`paramsEquivFlatCLE = paramsEquivFlat`). -/
theorem hasStrictFDerivAt_paramsEquivFlatCLE_l2CoreΔTuple_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt
      (fun q => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (flatDim (deepestM H r)) → ℝ)) 0 := by
  refine (hasStrictFDerivAt_paramsEquivFlat_l2CoreΔTuple_zero H r hr hL hL2eq).congr_of_eventuallyEq ?_
  filter_upwards with q
  rw [paramsEquivFlatCLE_coe]

/-! ### S4k — the gauge payload `l2GaugeΔ` has strict-`fderiv`-`0`

`l2GaugeΔ q = l2g' q − regGaugeSlotEquiv (q.1, q.2.2)`. Per `RegGaugeIdx` coordinate (`hasStrictFDerivAt_pi'`):
non-Y-tags and non-last-layer Y-tags give `l2g' = regGaugeSlotEquiv` (difference `0`, `const`); a
last-layer Y-tag gives `l2Y1p i (h ▸ j) − l2Y1 i j = (Y1'−Y1)` (the reg payload-block fact). Then
`regGaugeSlotCLE.symm` (a CLE) composes. -/

/-- The gauge payload `l2GaugeΔ` has strict-`fderiv`-`0` at `0`. -/
theorem hasStrictFDerivAt_l2GaugeΔ_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt (l2GaugeΔ H r hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (RegGaugeIdx H r → ℝ)) 0 := by
  refine hasStrictFDerivAt_pi'.2 (fun idx => ?_)
  rw [ContinuousLinearMap.comp_zero]
  obtain ⟨s, tag⟩ := idx
  rcases tag with tagXY | tagZ
  · rcases tagXY with tagX | ⟨i, j⟩
    · -- X-tag: `l2g'` falls to the `_` branch, `= regGaugeSlotEquiv`; difference `0`.
      have h0 : (fun q : DeepestSplit H r (deepestNGauge H r) =>
            l2GaugeΔ H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inl tagX)⟩) = fun _ => (0 : ℝ) := by
        funext q
        show l2g' H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inl tagX)⟩
          - regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inl (Sum.inl tagX)⟩ = 0
        rw [show l2g' H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inl tagX)⟩
          = regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inl (Sum.inl tagX)⟩ from rfl, sub_self]
      rw [h0]; exact hasStrictFDerivAt_const _ _
    · -- Y-tag: case on `s = lastLayer`.
      by_cases hs : s = lastLayer hL
      · subst hs
        -- `l2g' = l2Y1p i j`, `regGaugeSlotEquiv = readY = l2Y1 i j`; difference `(Y1'−Y1) i j`.
        have hval : (fun q : DeepestSplit H r (deepestNGauge H r) =>
              l2GaugeΔ H r hr hL hL2eq q ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩)
            = fun q => (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j := by
          funext q
          show l2g' H r hr hL hL2eq q ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
            - regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
            = (l2Y1p H r hr hL hL2eq q - l2Y1 H r hr hL q) i j
          rw [Matrix.sub_apply]
          congr 1
          show (if h : (lastLayer hL) = lastLayer hL then l2Y1p H r hr hL hL2eq q i (h ▸ j)
              else _) = l2Y1p H r hr hL hL2eq q i j
          rw [dif_pos rfl]
        rw [hval]
        exact hasStrictFDerivAt_l2Y1p_sub_Y1_entry_zero H r hr hL hL2eq i j
      · -- Non-last Y-tag: `l2g'` `dif_neg` falls to `regGaugeSlotEquiv`; difference `0`.
        have h0 : (fun q : DeepestSplit H r (deepestNGauge H r) =>
              l2GaugeΔ H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩) = fun _ => (0 : ℝ) := by
          funext q
          show l2g' H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩
            - regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩ = 0
          rw [show l2g' H r hr hL hL2eq q ⟨s, Sum.inl (Sum.inr (i, j))⟩
            = regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩ from by
            show (if h : s = lastLayer hL then l2Y1p H r hr hL hL2eq q i (h ▸ j)
                else regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩)
              = regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩
            rw [dif_neg hs], sub_self]
        rw [h0]; exact hasStrictFDerivAt_const _ _
  · -- Z-tag: `_` branch, difference `0`.
    have h0 : (fun q : DeepestSplit H r (deepestNGauge H r) =>
          l2GaugeΔ H r hr hL hL2eq q ⟨s, Sum.inr tagZ⟩) = fun _ => (0 : ℝ) := by
      funext q
      show l2g' H r hr hL hL2eq q ⟨s, Sum.inr tagZ⟩
        - regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inr tagZ⟩ = 0
      rw [show l2g' H r hr hL hL2eq q ⟨s, Sum.inr tagZ⟩
        = regGaugeSlotEquiv H r hr hL (q.1, q.2.2) ⟨s, Sum.inr tagZ⟩ from rfl, sub_self]
    rw [h0]; exact hasStrictFDerivAt_const _ _

/-- The gauge payload via `regGaugeSlotCLE.symm` has strict-`fderiv`-`0` at `0`. -/
theorem hasStrictFDerivAt_regGaugeSlotCLE_symm_l2GaugeΔ_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    HasStrictFDerivAt
      (fun q => (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2eq q))
      (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
        ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))) 0 := by
  have hinner := hasStrictFDerivAt_l2GaugeΔ_zero H r hr hL hL2eq
  have houter := (regGaugeSlotCLE H r hr hL).symm.toContinuousLinearMap.hasStrictFDerivAt
    (x := l2GaugeΔ H r hr hL hL2eq 0)
  have hcle := houter.comp (x := (0 : DeepestSplit H r (deepestNGauge H r))) hinner
  -- The composed derivative `CLE.symm ∘ 0 = 0`.
  simpa using hcle

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

/-! ### The joint-unit locus and its radius (the S2 re-key)

The cutoff support must sit in the locus where ALL the joint-action denominators are invertible:
the per-pivot `1 + readX_s` (`unitSet`, pulled back through the `q ↦ (q.1, q.2.2)` projection) AND, at
`L = 2`, `det P00 ≠ 0` and `det W ≠ 0`. All three hold at `0` (`P00 = W = 1`); the W/P00 conditions are
`ContinuousOn` the readX-locus (where `A0⁻¹/A1⁻¹` are defined), so the joint locus is open and contains
`0` — yielding a positive radius `jointUnitRadius` to which `cutoffBumpSplit` is keyed. -/

/-- The joint-unit locus on `DeepestSplit`: the per-pivot unit set (via the gauge projection), and at
`L = 2` also `det P00 ≠ 0` and `det W ≠ 0`. -/
def jointUnitSet (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Set (DeepestSplit H r (deepestNGauge H r)) :=
  {q | (q.1, q.2.2) ∈ unitSet H r hr hL}
    ∩ {q | ∀ h : L = 2, (l2P00 H r hr hL h q).det ≠ 0 ∧ (l2W H r hr hL h q).det ≠ 0}

/-- `0 ∈ jointUnitSet` (`P00 = W = 1` at `0`, and `0` is in the per-pivot unit set). -/
theorem mem_jointUnitSet_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (0 : DeepestSplit H r (deepestNGauge H r)) ∈ jointUnitSet H r hr hL := by
  constructor
  · show ((0 : DeepestSplit H r (deepestNGauge H r)).1,
        (0 : DeepestSplit H r (deepestNGauge H r)).2.2) ∈ unitSet H r hr hL
    rw [gaugeProj_zero]; exact mem_unitSet_zero H r hr hL
  · intro h
    exact ⟨l2P00_det_zero_ne H r hr hL h, l2W_det_zero_ne H r hr hL h⟩

/-- `jointUnitSet` is open. -/
theorem isOpen_jointUnitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    IsOpen (jointUnitSet H r hr hL) := by
  -- The readX-unit part: preimage of the open `unitSet` under the continuous gauge projection.
  have hUnitOpen : IsOpen {q : DeepestSplit H r (deepestNGauge H r) |
      (q.1, q.2.2) ∈ unitSet H r hr hL} :=
    (isOpen_unitSet H r hr hL).preimage (contDiff_gaugeProj H r).continuous
  rcases eq_or_ne L 2 with hL2 | hL2
  · -- L = 2: intersect with `{det P00 ≠ 0} ∩ {det W ≠ 0}`, both `ContinuousOn` the readX-locus.
    -- `det P00` is globally continuous (`P00 = A0·A1 + Y0·Z1`, no inverses).
    have hP00cont : Continuous (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2P00 H r hr hL hL2 q).det) :=
      (continuous_matrix (fun i j => (contDiff_l2P00_entry H r hr hL hL2 i j).continuous)).matrix_det
    have hP00open : IsOpen {q : DeepestSplit H r (deepestNGauge H r) |
        (l2P00 H r hr hL hL2 q).det ≠ 0} := hP00cont.isOpen_preimage _ isOpen_ne
    -- `det W` is `ContinuousOn` the readX-locus (where `A0⁻¹/A1⁻¹` exist): at each locus point `q`,
    -- the entries are `ContDiffAt`, so `det` (a polynomial of entries) is `ContDiffAt`, hence continuous.
    have hWcontOn : ContinuousOn (fun q : DeepestSplit H r (deepestNGauge H r) =>
        (l2W H r hr hL hL2 q).det)
        {q | (q.1, q.2.2) ∈ unitSet H r hr hL} := by
      intro q hq
      refine (contDiffAt_matrix_det_of_entries (A := fun q => l2W H r hr hL hL2 q) (x := q)
        (fun i j => ?_)).continuousAt.continuousWithinAt
      exact contDiffAt_l2W_entry_at H r hr hL hL2 q (hq (⟨0, by omega⟩ : Fin L)) (hq (lastLayer hL)) i j
    have hWopen : IsOpen ({q : DeepestSplit H r (deepestNGauge H r) |
          (q.1, q.2.2) ∈ unitSet H r hr hL}
        ∩ (fun q => (l2W H r hr hL hL2 q).det) ⁻¹' {x | x ≠ 0}) :=
      hWcontOn.isOpen_inter_preimage hUnitOpen isOpen_ne
    have hrw : jointUnitSet H r hr hL
        = ({q : DeepestSplit H r (deepestNGauge H r) | (q.1, q.2.2) ∈ unitSet H r hr hL}
            ∩ {q | (l2P00 H r hr hL hL2 q).det ≠ 0})
          ∩ ({q | (q.1, q.2.2) ∈ unitSet H r hr hL}
            ∩ (fun q => (l2W H r hr hL hL2 q).det) ⁻¹' {x | x ≠ 0}) := by
      ext q
      simp only [jointUnitSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hu, hPW⟩
        obtain ⟨hP, hW⟩ := hPW hL2
        exact ⟨⟨hu, hP⟩, hu, hW⟩
      · rintro ⟨⟨hu, hP⟩, _, hW⟩
        refine ⟨hu, fun h => ?_⟩
        -- `h : L = 2`; `hL2 : L = 2`; the det facts are the same by `Subsingleton`-of-`Eq`.
        obtain rfl : h = hL2 := rfl
        exact ⟨hP, hW⟩
    rw [hrw]
    exact (hUnitOpen.inter hP00open).inter hWopen
  · -- L ≠ 2: the joint set is just the readX-locus (the `∀ h : L = 2` part is vacuous).
    have hrw : jointUnitSet H r hr hL
        = {q : DeepestSplit H r (deepestNGauge H r) | (q.1, q.2.2) ∈ unitSet H r hr hL} := by
      ext q
      simp only [jointUnitSet, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun heq => absurd heq hL2⟩⟩
    rw [hrw]; exact hUnitOpen

/-- A positive radius `ε` with `ball 0 ε ⊆ jointUnitSet`. -/
theorem exists_ball_subset_jointUnitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ ε > 0, Metric.ball (0 : DeepestSplit H r (deepestNGauge H r)) ε ⊆ jointUnitSet H r hr hL :=
  Metric.isOpen_iff.mp (isOpen_jointUnitSet H r hr hL) 0 (mem_jointUnitSet_zero H r hr hL)

/-- The chosen joint-unit radius `ε > 0` (with `ball 0 ε ⊆ jointUnitSet`). -/
noncomputable def jointUnitRadius (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : ℝ :=
  (exists_ball_subset_jointUnitSet H r hr hL).choose

theorem jointUnitRadius_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) : 0 < jointUnitRadius H r hr hL :=
  (exists_ball_subset_jointUnitSet H r hr hL).choose_spec.1

theorem ball_jointUnitRadius_subset (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Metric.ball (0 : DeepestSplit H r (deepestNGauge H r)) (jointUnitRadius H r hr hL)
      ⊆ jointUnitSet H r hr hL :=
  (exists_ball_subset_jointUnitSet H r hr hL).choose_spec.2

/-- A fresh `ContDiffBump` at `0` on the FULL split `DeepestSplit` (Codex's "do not reuse the reg/spec
bump as a full-split bump"). Its inner/outer radii are `jointUnitRadius/4`, `jointUnitRadius/2`, so its
(closed) support sits inside the JOINT-unit locus `jointUnitSet` — where every joint-action denominator
(`1 + readX_s`, and at `L = 2` also `P00`, `W`) is invertible — making the rational correction
`ContDiffAt` on the support. -/
noncomputable def cutoffBumpSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiffBump (0 : DeepestSplit H r (deepestNGauge H r)) where
  rIn := jointUnitRadius H r hr hL / 4
  rOut := jointUnitRadius H r hr hL / 2
  rIn_pos := by have := jointUnitRadius_pos H r hr hL; linarith
  rIn_lt_rOut := by have := jointUnitRadius_pos H r hr hL; linarith

/-- The (closed) support of the joint cutoff bump sits inside the joint-unit locus:
`tsupport χ = closedBall 0 (ε/2) ⊆ ball 0 ε ⊆ jointUnitSet`. -/
theorem tsupport_cutoffBumpSplit_subset_jointUnitSet (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    tsupport (⇑(cutoffBumpSplit H r hr hL)) ⊆ jointUnitSet H r hr hL := by
  rw [(cutoffBumpSplit H r hr hL).tsupport_eq]
  refine subset_trans ?_ (ball_jointUnitRadius_subset H r hr hL)
  intro x hx
  rw [Metric.mem_closedBall] at hx
  rw [Metric.mem_ball]
  have hpos := jointUnitRadius_pos H r hr hL
  show dist x 0 < jointUnitRadius H r hr hL
  have hrout : (cutoffBumpSplit H r hr hL).rOut = jointUnitRadius H r hr hL / 2 := rfl
  rw [hrout] at hx
  linarith

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
  · -- **L = 2: the genuine composite-inverse ContDiff (S2).** At `q ∈ tsupport ⊆ jointUnitSet` all four
    -- joint dets are nonzero; `δ = psiSplitRawL2Core − id` rewrites (lens) to the payload triple, each
    -- payload `ContDiffAt q` (core flat-decode, gauge `pi'`), assembled by `prodMk` + the CLE.
    -- Extract the det conditions from `q ∈ tsupport ⊆ jointUnitSet`.
    have hmem : q ∈ jointUnitSet H r hr hL :=
      tsupport_cutoffBumpSplit_subset_jointUnitSet H r hr hL _hq
    have hA0 : (l2A0 H r hr hL q).det ≠ 0 := by
      have := hmem.1 (⟨0, by omega⟩ : Fin L); rwa [l2A0]
    have hA1 : (l2A1 H r hr hL q).det ≠ 0 := by
      have := hmem.1 (lastLayer hL); rwa [l2A1]
    obtain ⟨hP00, hW⟩ := hmem.2 hL2
    -- Rewrite `δ` to the payload triple at `q` (the lens decomposition).
    have hδeq : psiSplitDeltaL2 H r hr hL
        = fun q' => (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')).1,
            (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q'),
              ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')).2)) := by
      funext q'
      rw [psiSplitDeltaL2, psiSplitRawL2, dif_pos hL2]
      exact psiSplitDeltaL2Core_eq_payload H r hr hL hL2 q'
    rw [hδeq]
    -- Core payload `ContDiffAt q` (flat-decode; each flat coord is a `l2T1p` entry or const-0).
    have hcore : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q')) q := by
      have hcoe : (fun q' => paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q'))
          = fun q' => paramsEquivFlat (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q') := by
        funext q'; rw [paramsEquivFlatCLE_coe]
      rw [hcoe]
      refine contDiffAt_pi.2 (fun k => ?_)
      set d := (Fintype.equivFin (FlatIdx (deepestM H r))).symm k with hd
      have hcoord : (fun q' => paramsEquivFlat (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q') k)
          = fun q' => l2CoreΔTuple H r hr hL hL2 q' d.1.1 d.1.2 d.2 := rfl
      rw [hcoord]
      clear_value d
      obtain ⟨⟨s₀, i₀⟩, j₀⟩ := d
      rcases eq_or_ne s₀ (lastLayer hL) with hlast | hlast
      · subst hlast
        have heq : (fun q' => l2CoreΔTuple H r hr hL hL2 q' (lastLayer hL) i₀ j₀)
            = fun q' => (l2T1p H r hr hL hL2 q' - l2T1 H r hr hL q') i₀ j₀ := by
          funext q'; rw [l2CoreΔTuple, Function.update_self]
        rw [heq]
        have hsub : (fun q' : DeepestSplit H r (deepestNGauge H r) =>
            (l2T1p H r hr hL hL2 q' - l2T1 H r hr hL q') i₀ j₀)
            = fun q' => l2T1p H r hr hL hL2 q' i₀ j₀ - l2T1 H r hr hL q' i₀ j₀ := by
          funext q'; rw [Matrix.sub_apply]
        rw [hsub]
        exact (contDiffAt_l2T1p_entry_at H r hr hL hL2 q hA0 hA1 hP00 hW i₀ j₀).sub
          (contDiff_l2T1_entry H r hr hL i₀ j₀).contDiffAt
      · have heq : (fun q' => l2CoreΔTuple H r hr hL hL2 q' s₀ i₀ j₀)
            = fun _ : DeepestSplit H r (deepestNGauge H r) => (0 : ℝ) := by
          funext q'; rw [l2CoreΔTuple, Function.update_of_ne hlast]; rfl
        rw [heq]; exact contDiffAt_const
    -- Gauge payload `ContDiffAt q` (per `RegGaugeIdx`; last Y-tag = `l2Y1p − l2Y1`, else const).
    have hgaugeΔ : ContDiffAt ℝ (⊤ : ℕ∞) (l2GaugeΔ H r hr hL hL2) q := by
      refine contDiffAt_pi.2 (fun idx => ?_)
      obtain ⟨s, tag⟩ := idx
      rcases tag with tagXY | tagZ
      · rcases tagXY with tagX | ⟨i, j⟩
        · have h0 : (fun q' : DeepestSplit H r (deepestNGauge H r) =>
                l2GaugeΔ H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inl tagX)⟩) = fun _ => (0 : ℝ) := by
            funext q'
            show l2g' H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inl tagX)⟩
              - regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inl (Sum.inl tagX)⟩ = 0
            rw [show l2g' H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inl tagX)⟩
              = regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inl (Sum.inl tagX)⟩ from rfl,
              sub_self]
          rw [h0]; exact contDiffAt_const
        · by_cases hs : s = lastLayer hL
          · subst hs
            have hval : (fun q' : DeepestSplit H r (deepestNGauge H r) =>
                  l2GaugeΔ H r hr hL hL2 q' ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩)
                = fun q' => l2Y1p H r hr hL hL2 q' i j - l2Y1 H r hr hL q' i j := by
              funext q'
              show l2g' H r hr hL hL2 q' ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
                - regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨lastLayer hL, Sum.inl (Sum.inr (i, j))⟩
                = l2Y1p H r hr hL hL2 q' i j - l2Y1 H r hr hL q' i j
              congr 1
              show (if h : (lastLayer hL) = lastLayer hL then l2Y1p H r hr hL hL2 q' i (h ▸ j)
                  else _) = l2Y1p H r hr hL hL2 q' i j
              rw [dif_pos rfl]
            rw [hval]
            exact (contDiffAt_l2Y1p_entry_at H r hr hL hL2 q hA0 hA1 hP00 hW i j).sub
              (contDiff_l2Y1_entry H r hr hL i j).contDiffAt
          · have h0 : (fun q' : DeepestSplit H r (deepestNGauge H r) =>
                  l2GaugeΔ H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inr (i, j))⟩) = fun _ => (0 : ℝ) := by
              funext q'
              show l2g' H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inr (i, j))⟩
                - regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩ = 0
              rw [show l2g' H r hr hL hL2 q' ⟨s, Sum.inl (Sum.inr (i, j))⟩
                = regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩ from by
                show (if h : s = lastLayer hL then l2Y1p H r hr hL hL2 q' i (h ▸ j)
                    else regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩)
                  = regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inl (Sum.inr (i, j))⟩
                rw [dif_neg hs], sub_self]
            rw [h0]; exact contDiffAt_const
      · have h0 : (fun q' : DeepestSplit H r (deepestNGauge H r) =>
              l2GaugeΔ H r hr hL hL2 q' ⟨s, Sum.inr tagZ⟩) = fun _ => (0 : ℝ) := by
          funext q'
          show l2g' H r hr hL hL2 q' ⟨s, Sum.inr tagZ⟩
            - regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inr tagZ⟩ = 0
          rw [show l2g' H r hr hL hL2 q' ⟨s, Sum.inr tagZ⟩
            = regGaugeSlotEquiv H r hr hL (q'.1, q'.2.2) ⟨s, Sum.inr tagZ⟩ from rfl, sub_self]
        rw [h0]; exact contDiffAt_const
    -- The gauge payload via the CLE, then its two projections.
    have hgauge : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q' => (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')) q :=
      ((regGaugeSlotCLE H r hr hL).symm.contDiff.contDiffAt).comp q hgaugeΔ
    have hg1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q' => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')).1) q :=
      (contDiffAt_fst).comp q hgauge
    have hg2 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q' => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q')).2) q :=
      (contDiffAt_snd).comp q hgauge
    exact hg1.prodMk (hcore.prodMk hg2)
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
  · -- **L = 2: the certified `O(read²)` deriv-vanishing.** `δ = psiSplitRawL2Core − id`, which the
    -- lens decomposition `psiSplitDeltaL2Core_eq_payload` writes as the encoded payloads
    -- `(regGaugeCLE.symm(gaugeΔ).1, (paramsFlatCLE(coreΔ), regGaugeCLE.symm(gaugeΔ).2))`; each
    -- payload's strict-`fderiv`-`0` was proven (S4j/S4k), assembled by `.prodMk`.
    -- Rewrite `δ` to the payload triple (at `L = 2`).
    have hδeq : psiSplitDeltaL2 H r hr hL
        = fun q => (((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q)).1,
            (paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q),
              ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q)).2)) := by
      funext q
      rw [psiSplitDeltaL2, psiSplitRawL2, dif_pos hL2]
      exact psiSplitDeltaL2Core_eq_payload H r hr hL hL2 q
    rw [hδeq]
    -- The gauge payload (into `Reg × Spec`) and its two projections.
    have hgauge := hasStrictFDerivAt_regGaugeSlotCLE_symm_l2GaugeΔ_zero H r hr hL hL2
    have hg1 : HasStrictFDerivAt
        (fun q => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q)).1)
        (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
      have := (ContinuousLinearMap.fst ℝ (Fin (deepestNReg H r) → ℝ)
        (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp
        (x := (0 : DeepestSplit H r (deepestNGauge H r))) hgauge
      simpa using this
    have hg2 : HasStrictFDerivAt
        (fun q => ((regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q)).2)
        (0 : DeepestSplit H r (deepestNGauge H r) →L[ℝ] (Fin (deepestNGauge H r) → ℝ)) 0 := by
      have := (ContinuousLinearMap.snd ℝ (Fin (deepestNReg H r) → ℝ)
        (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt.comp
        (x := (0 : DeepestSplit H r (deepestNGauge H r))) hgauge
      simpa using this
    -- The core payload.
    have hcore := hasStrictFDerivAt_paramsEquivFlatCLE_l2CoreΔTuple_zero H r hr hL hL2
    -- Assemble the triple `(g1, (core, g2))`; the derivative is `0.prodMk (0.prodMk 0) = 0`.
    have hpair := hg1.prodMk (hcore.prodMk hg2)
    simpa using hpair
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
