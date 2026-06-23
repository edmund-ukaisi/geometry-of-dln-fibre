import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct` — the gauge-sliced framed product `∏C` (#44c)

The shared concrete object both PIN 1 (`Ereg`, the regular residual) and PIN 2 (`loss_squeeze`, the
frame bridge) consume: the **framed product** `∏C_s`, where each layer
`C_s = fromBlocks (1 + X_s) Y_s Z_s T_s` is the gauge-sliced normal-form deviation (the `block_elimination`
frame puts `w0` at `blockdiag[I_r,0]`; the deviation reads the gauge blocks `(X_s, Y_s, Z_s)` off the
reg+spec slots via `gaugeSlotRead`/`regGaugeSlotEquiv` and the reduced `T_s` off the core slot).

Per the #92 producer contract: `∏C` is the CLEAN product of the per-layer normal forms (the interior
`block_elimination` frames are trivial — #77 (iii), interior layers already block-normal — so the
per-layer framing telescopes; only the two boundary frames carry units, absorbed by the endpoint
conjugation `conjugation_frobenius_comparable`). The framed product is `prod H C` for the reconstructed
gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.

## Status

SCAFFOLD (decision-independent piece): the per-layer framed reconstruction `framedLayer`
(`fromBlocks` reindexed to a `Params H` layer via `rThresholdSplit`) + the framed tuple `framedParams`.
The `∏C` residual (`Ereg`) extraction + the `dlnLoss = ‖∏C − D‖²` bridge are the coupled pieces
(gated on the #77 (iii) decl-confirm + the `Ereg = E_pivot` (B)-ruling); built once confirmed.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `ContDiff` of the gauge read (the `regGaugeSlotEquiv` linearity, for `_contdiff`)

`regGaugeSlotEquiv` (crux2 #78) is packaged as a `Homeomorph` (coordinate relabels), so its linearity is
not exposed — but the SAME relabels have `ContinuousLinearEquiv` forms in Mathlib v4.29
(`ContinuousLinearEquiv.{sumPiEquivProdPi, piCongrLeft}`), whose underlying `Homeomorph` IS the one
`regGaugeSlotEquiv` uses (`__ := Homeomorph.…`). So a CLE mirror `regGaugeSlotCLE` coerces to the SAME
function (defeq), giving `ContDiff` of `regGaugeSlotEquiv` (hence of the `readX/Y/Z` entries) via
`ContinuousLinearEquiv.contDiff`. This is a fact ABOUT crux2's def, not a change to it. -/

/-- The `ContinuousLinearEquiv` mirror of `regGaugeSlotEquiv` (same underlying Homeomorph/function). -/
noncomputable def regGaugeSlotCLE (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ≃L[ℝ] (RegGaugeIdx H r → ℝ) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
      (fun _ => ℝ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm

/-- `regGaugeSlotCLE` and `regGaugeSlotEquiv` coerce to the SAME function (the CLE and Homeomorph share
the underlying relabel). -/
theorem regGaugeSlotCLE_coe (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (regGaugeSlotCLE H r hr hL : _ → _) = regGaugeSlotEquiv H r hr hL := rfl

/-- The gauge read `regGaugeSlotEquiv` is `ContDiff ⊤` (it is the CLE `regGaugeSlotCLE`). -/
theorem contDiff_regGaugeSlotEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => regGaugeSlotEquiv H r hr hL p) := by
  rw [← regGaugeSlotCLE_coe H r hr hL]
  exact (regGaugeSlotCLE H r hr hL).contDiff

/-- Each `readX` entry is `ContDiff ⊤` (a coordinate of the `ContDiff` gauge read). -/
theorem contDiff_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readX H r hr hL p s i j) := by
  simp only [readX, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- Each `readY` entry is `ContDiff ⊤`. -/
theorem contDiff_readY_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i : Fin r)
    (j : Fin (H s.succ - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readY H r hr hL p s i j) := by
  simp only [readY, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- Each `readZ` entry is `ContDiff ⊤`. -/
theorem contDiff_readZ_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i : Fin (H s.castSucc - r))
    (j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readZ H r hr hL p s i j) := by
  simp only [readZ, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- **The per-layer framed normal-form matrix** `C_s = fromBlocks (1 + X_s) Y_s Z_s T_s`, reindexed
from the block split `Fin r ⊕ Fin (H_s − r)` to the layer dimension `Fin (H_s)` (via `rThresholdSplit`),
so it types as a `Params H` layer `Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. The gauge blocks
`(X_s, Y_s, Z_s)` are the regular/spectator gauge entries (off `gaugeSlotRead`); `T_s` is the reduced
core block. -/
noncomputable def framedLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (X : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
    (Z : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ) :
    Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ :=
  Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
    (rThresholdSplit r (H s.succ) (hr s.succ)).symm
    (Matrix.fromBlocks (1 + X) Y Z T)

/-- **The framed parameter tuple** `C : Params H` reconstructed from a `DeepestSplit` point: each layer
is `framedLayer` of the gauge blocks `(X_s, Y_s, Z_s)` (read off the reg+spectator slot via
`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
The framed product `∏C = prod H (framedParams q)` is the shared object; `dlnLoss = ‖∏A − B‖²` relates to
`‖∏C − D‖²` through the endpoint conjugation (the #77 (iii) telescoping). Decision-independent (the
product `∏C` is well-defined regardless of (iii)/(B); those affect how it relates to `dlnLoss`/`Ereg`). -/
noncomputable def framedParams (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s)
      ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)

/-- **The `T = 0` framed reconstruction** (the `deepestEPivot` reconstruction half). Reconstructs the
gauge-sliced layer tuple from the `(reg, gauge)` slots ALONE, with the reduced core block `T_s := 0`
(the core is `coreAbsorb`'s domain — `deepestEPivot` is the regular residual of `∏C|_{T=0}`, the
core-INDEPENDENT pivot part, per the #115/g222 cert). Each layer is `framedLayer` of the read blocks
`(X_s, Y_s, Z_s)` with the `(1,1)` block zeroed. Layout-independent: it does not depend on the final
`Fin nReg` pack convention (the open obstruction), only on the gauge read `readX/Y/Z`. -/
noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
      (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
`framedLayer 0 0 0 0 = reindex (fromBlocks 1 0 0 0)` (the deepest value `blockdiag[I_r, 0]`). The base
fact for `deepestEPivot`'s `_base` (the residual of `∏ blockdiag[I_r,0]` is `0`). -/
theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    framedParamsReg H r hr hL 0 s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
    readZ_zero H r hr hL s, add_zero]

/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
`ContDiff` (the read entries + `const`). The `_contdiff` layer input to `contDiff_prod_entry`. -/
theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
  -- The entry is `(fromBlocks (1+X) Y Z 0) (e₁.symm i) (e₂.symm j)`; case-split on the sum indices.
  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
      = fun p => Matrix.fromBlocks (1 + readX H r hr hL p s) (readY H r hr hL p s)
          (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
          ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i)
          ((rThresholdSplit r (H s.succ) (hr s.succ)) j) := by
    funext p
    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
  rw [hentry]
  rcases (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i with a | a <;>
    rcases (rThresholdSplit r (H s.succ) (hr s.succ)) j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, Matrix.zero_apply]
  · -- (1 + X) entry: `(if a = b then 1 else 0) + readX … a b` — the `if` is a constant in `p`.
    exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)
  · exact contDiff_readY_entry H r hr hL s a b
  · exact contDiff_readZ_entry H r hr hL s a b
  · exact contDiff_const

/-! ## PIN 2 frame bridge — the telescoping (#80, next chunk)

The geometric bridge `dlnLoss H B (paramsSymm w) ≍ ‖∏(framed C) − D‖²` reduces to: the **endpoint-frame
telescoping** `prod H A = P_0⁻¹ · (prod H C) · Q_{L-1}⁻¹` (under #95-(I): interior frames `= I` via
`deepestPoint_interior_eq_corM`, boundary-inner `= I` via `deepestPoint_layer{0,Last}_*_vanish`, so the
interior interfaces `Q_s⁻¹·P_{s+1}⁻¹ = 1` collapse) → `conjugation_frobenius_comparable` (the endpoint
conjugation, banked) → `fullProduct_loss_squeeze` (the block split, banked) + the gauge-read identities.

**The statement SHAPE is solved** (the cast obstacle): state it with EXISTENTIAL endpoints —
`∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
IsUnit P0 ∧ IsUnit QL ∧ prod H C = P0 * prod H A * QL`, with hypotheses: per-layer frames
`P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ`, `Q : … (Fin (H s.succ)) …`,
`hframe : ∀ s, C s = P s * A s * Q s`, `hunit : ∀ s, IsUnit (P s) ∧ IsUnit (Q s)`, and the
INTERFACE-VANISHING conditions `Q s * P s' = 1` for adjacent `s + 1 = s'` (the #95-(I) frame-triviality
makes the interfaces `I`). Existential `P0, QL` are naturally typed where `prod` lives (`H 0`, `H (last)`)
— this DODGES the `H 0` vs `H ⟨0,_⟩.castSucc` cast that breaks an explicit-endpoint statement (probed,
typechecks). The PROOF is the cast-heavy `prodAux` induction: invariant `prodAux H C k = P0 *
prodAux H A k * (frame at k)`, interior interfaces cancelling by the `Q s * P s' = 1` conditions. The
endpoint conjugation + block split are banked (`conjugation_frobenius_comparable`,
`fullProduct_loss_squeeze`); only this induction remains for PIN 2's bridge. -/

/-! ## `ContDiff` of the layer product (the `deepestEPivot._contdiff` infrastructure)

`deepestEPivot` is `pack ∘ residual ∘ reindex ∘ prod ∘ framedParamsReg`; its `ContDiff ⊤` reduces to
`ContDiff ⊤ (fun x => prod H (g x))` for `g = framedParamsReg` (each layer affine in the slots, so
`ContDiff`). The product is the dependent-Fin `prodAux` fold — `ContDiff` ENTRY-WISE (matrix = nested
`Pi`; `contDiff_pi'` twice), mirroring the green `continuous_prodAux`: base `prodAux 0 = 1` const, step
`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). No
`ContDiff.matrix_mul` lemma exists in v4.29 — the entry-wise route sidesteps it. -/

/-- **`ContDiff` of the partial-product ENTRIES** under a smooth reconstruction `g : X → Params H`
(each layer ENTRY `ContDiff ⊤`). Entry-wise to dodge the matrix-norm-instance friction (`Matrix` has
no canonical `NormedSpace` — `ContDiff` of a matrix-VALUED map needs an opt-in norm; the entries are
plain ℝ-valued). Induction on `k`, mirroring `continuous_prodAux`: the matrix-mul step is
`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). -/
theorem contDiff_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g x s i j))
    (k : ℕ) (hk : k < L + 1) :
    ∀ (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => prodAux H (g x) k hk i j) := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      -- `prodAux 0 = 1`; each entry is `0` or `1`, constant.
      have : (fun x => prodAux H (g x) 0 hk i j)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j := rfl
      rw [this]; exact contDiff_const
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
      have hentry : (fun x => prodAux H (g x) (k + 1) hk i j)
          = fun x => ∑ m, prodAux H (g x) k hk' i m
              * ((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) := by
        funext x; rfl
      rw [hentry]
      refine ContDiff.sum (fun m _ => ?_)
      refine (ih hk' i m).mul ?_
      -- The cast `⟨k,hk'⟩ = ⟨k,hkL⟩.castSucc` is `Fin.mk` proof-irrelevance (defeq), so the cast layer
      -- entry IS `g x ⟨k,hkL⟩ m j` up to the `eq_mpr/cast` normal form; `ContDiff` by `hg`.
      have := hg ⟨k, hkL⟩
      simp only [e1, e2, eq_mpr_eq_cast, cast_eq] at this ⊢
      exact this _ _

/-- **`ContDiff` of the full layer-product entries** (`contDiff_prodAux_entry` at `k = L`). -/
theorem contDiff_prod_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g x s i j))
    (i : Fin (H 0)) (j : Fin (H (Fin.last L))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => prod H (g x) i j) :=
  contDiff_prodAux_entry H g hg L (Nat.lt_succ_self L) i j

end DLNFibre.DLN.RLCT
