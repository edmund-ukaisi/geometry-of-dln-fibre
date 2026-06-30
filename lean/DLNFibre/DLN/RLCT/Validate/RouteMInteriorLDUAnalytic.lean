import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLDUContract

/-!
# `RouteMInteriorLDUAnalytic` — the analytic chart facts for the LDU-lensed interior chart

The prerequisite analytic atom for the LDU-lensed interior achiever contract
(`RouteMInteriorLDUContract`): continuity of the `kLDU` lens. The other three contract slots
(`interiorLDU_Umeas`/`_Ubound`/`_image`) each rest on continuity/measurability of the LDU-lensed
STRUCT chart chain (`x ↦ VvalGen (x p) (genBlkFlatStruct (kLDU x))` / `x ↦ phiFlatLDU (kLDU) x`),
which is open infrastructure at this tip — see the thread report's "flagged gap" section. They are
NOT thin one-liner wires over the present API and are deliberately NOT asserted here (the `_Ubound`
a.e.-positivity is the soundness pin: it additionally needs the nonzero-polynomial encoding of the
lensed unit, i.e. `kLens`/`matrixSplit` over `MvPolynomial`, which the ℝ-only LDU machinery does not
yet provide).

* `continuous_kLDU` — the K-slot LDU reparametrization is continuous (∀M). `kLDU` is built
  coordinatewise from `kLens (readK x k)` (a continuous matrix lens) on the K-slots and the identity
  projection `x q` elsewhere; `continuous_pi` + a per-coordinate split on the `x`-INDEPENDENT
  `chartIdxEquiv` scrutinee.

Sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-! ## Continuity of the matrix LDU lens `kLens` -/

/-- **`lduCoreMap` is continuous** — it has a Fréchet derivative at every point
(`lduCoreMap_hasFDerivAt`), hence is differentiable, hence continuous. -/
theorem continuous_lduCoreMap {t : ℕ} : Continuous (lduCoreMap (t := t)) :=
  (Differentiable.continuous (fun z => (lduCoreMap_hasFDerivAt z).differentiableAt))

/-- **`kLens` is continuous** — `kLens = matrixSplit.symm ∘ lduCoreMap ∘ matrixSplit`, a composite of
two finite-dimensional ℝ-linear equivalences (continuous) and the differentiable `lduCoreMap`. -/
theorem continuous_kLens {t : ℕ} : Continuous (kLens (t := t)) := by
  have hsplit : Continuous (matrixSplit (t := t)) :=
    matrixSplit.toLinearMap.continuous_of_finiteDimensional
  have hsymm : Continuous (matrixSplit (t := t)).symm :=
    (matrixSplit (t := t)).symm.toLinearMap.continuous_of_finiteDimensional
  have : kLens (t := t) = fun K => matrixSplit.symm (lduCoreMap (matrixSplit K)) := rfl
  rw [this]
  exact hsymm.comp (continuous_lduCoreMap.comp hsplit)

/-! ## Continuity of `kLDU` -/

/-- The K-block reader, as a function of the flat vector `x`, is continuous: each entry
`readK x k i j = x (fixed index)` is a coordinate projection. -/
theorem continuous_readK_fun (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L) :
    Continuous (fun x : Fin (routeMAmbient M) → ℝ => readK M (tach M) ha x k) := by
  refine continuous_matrix (fun i j => ?_)
  exact continuous_apply _

/-- **`continuous_kLDU` — the K-slot LDU reparametrization is continuous (∀M).** Per coordinate `q`
(via `continuous_pi`), the `chartIdxEquiv`-scrutinee is `x`-independent, so the `match` splits into the
K-branch (`kLens (readK x k) i j`, a continuous matrix lens of `x`) and the pass-through branches
(`x q`, a projection). -/
theorem continuous_kLDU (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Continuous (kLDU M (tach M) ha) := by
  refine continuous_pi (fun q => ?_)
  -- The scrutinee `chartIdxEquiv … q` does not depend on `x`; case-split it.
  rcases hq : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with ⟨k, s⟩
  -- pass-through helper for every non-K branch
  cases s with
  | inl sfr =>
    -- the frame slot splits as `(((K ⊕ X) ⊕ N) ⊕ E)`; only K hits `kLens`
    rcases hframe : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) sfr
      with (((qK | qX) | qN) | qE)
    · -- K-role: `kLens (readK x k) ij.1 ij.2`
      have hfun : (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q)
          = fun x => kLens (readK M (tach M) ha x k) (finProdFinEquiv.symm qK).1
              (finProdFinEquiv.symm qK).2 := by
        funext x; simp only [kLDU, hq, hframe]
      rw [hfun]
      exact (continuous_kLens.comp (continuous_readK_fun M ha k)).matrix_elem _ _
    · -- X-role: pass-through `x q`
      have hfun : (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q)
          = fun x => x q := by funext x; simp only [kLDU, hq, hframe]
      rw [hfun]; exact continuous_apply _
    · -- N-role: pass-through `x q`
      have hfun : (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q)
          = fun x => x q := by funext x; simp only [kLDU, hq, hframe]
      rw [hfun]; exact continuous_apply _
    · -- E-role: pass-through `x q`
      have hfun : (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q)
          = fun x => x q := by funext x; simp only [kLDU, hq, hframe]
      rw [hfun]; exact continuous_apply _
  | inr sl =>
    -- lift slot: pass-through `x q`
    have hfun : (fun x : Fin (routeMAmbient M) → ℝ => kLDU M (tach M) ha x q)
        = fun x => x q := by funext x; simp only [kLDU, hq]
    rw [hfun]; exact continuous_apply _

end DLNFibre.DLN.RLCT
