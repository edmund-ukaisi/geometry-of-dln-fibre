import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet
import DLNFibre.DLN.RLCT.Validate.RouteMFactorFDeriv
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# `RouteMEngineReshape` — the engine-block reshape CLEs (`SchurInc`/`LDUParam` ≃L a coordinate Pi)

The foundational per-boundary brick for the BFactors construction (route #1):
the engine block types `SchurInc t r c` (a `Matrix×(Matrix×(Matrix×Matrix))` increment tuple) and
`LDUParam t` (a `Pi×(Pi×Pi)` tuple) are `ContinuousLinearEquiv`-isomorphic to a flat coordinate Pi
`(roleIdx → ℝ)`. Composing such a reshape with the banked `RouteMRoleCLE.flatBlockSplitCLE` (the
`chartIdxEquiv`-derived `(Fin N → ℝ) ≃L (Block → ℝ) × (Rest → ℝ)`) yields the per-boundary CLE
`E : (Fin N → ℝ) ≃L (SchurInc/LDUParam) × Rest` that `schur`/`lduChartFactor` conjugate by.

* `schurIncReshapeCLE` — `SchurInc t r c ≃L (roleIdx → ℝ)` via the four banked `matrixCoordCLE`s +
  `prodCongr` + `sumPiEquivProdPi`.
* `lduParamReshapeCLE` — `LDUParam t ≃L ((LowIdx t ⊕ Fin t) ⊕ UpIdx t → ℝ)` via `sumPiEquivProdPi`
  (the three role-Pi's regrouped; no matrices — `LDUParam` is already a Pi-product).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the finite pi-CLE combinators; no analysis).
-/

open Matrix

noncomputable section

namespace DLNFibre.DLN.RLCT

/-- **The matrix↔coordinate-Pi reshape CLE** `Matrix (Fin a) (Fin b) ℝ ≃L (Fin a × Fin b → ℝ)`
(`Matrix.ofLinearEquiv` + `LinearEquiv.curry`, upgraded to a `≃L` since finite-dim). Local copy (the
`DeepestGaugeConstruction.matrixPiCLE` import-closure clashes with `RouteMFlatLive`'s — a duplicate
`continuous_dlnLoss` in `DeepestGaugeChart` vs `LossContinuity`; coexists with the chart). -/
def matrixCoordCLE (a b : ℕ) :
    Matrix (Fin a) (Fin b) ℝ ≃L[ℝ] (Fin a × Fin b → ℝ) :=
  (((Matrix.ofLinearEquiv ℝ).symm.trans
    (LinearEquiv.curry ℝ ℝ (Fin a) (Fin b)).symm) : Matrix (Fin a) (Fin b) ℝ ≃ₗ[ℝ]
      (Fin a × Fin b → ℝ)).toContinuousLinearEquiv

@[simp] theorem matrixCoordCLE_apply (a b : ℕ) (M : Matrix (Fin a) (Fin b) ℝ) (p : Fin a × Fin b) :
    matrixCoordCLE a b M p = M p.1 p.2 := rfl

/-- **The Schur-increment reshape CLE** `SchurInc t r c ≃L (roleIdx → ℝ)`, the K/X/N/E matrix blocks
flattened to a coordinate Pi. The codomain index `((Fin t×Fin t) ⊕ ((Fin t×Fin c) ⊕ ((Fin r×Fin t) ⊕
(Fin r×Fin c))))` is RIGHT-nested to match `SchurInc`'s `K × (N × (X × E))` nesting, so
`sumPiEquivProdPi` right-nested gives the four-fold product of role-Pi's, the four `matrixCoordCLE`s
reshape each matrix block. -/
def schurIncReshapeCLE (t r c : ℕ) :
    SchurInc t r c ≃L[ℝ]
      (((Fin t × Fin t) ⊕ ((Fin t × Fin c) ⊕ ((Fin r × Fin t) ⊕ (Fin r × Fin c)))) → ℝ) := by
  -- innermost: `(X × E) ≃L (XΠ × EΠ) ≃L ((XIdx ⊕ EIdx) → ℝ)`
  have eXE : (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ) ≃L[ℝ]
      (((Fin r × Fin t) ⊕ (Fin r × Fin c)) → ℝ) :=
    ((matrixCoordCLE r t).prodCongr (matrixCoordCLE r c)).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin r × Fin t) (Fin r × Fin c) (fun _ => ℝ)).symm
  -- next: `(N × (X × E)) ≃L (NΠ × ((XE)Π)) ≃L ((NIdx ⊕ (XEIdx)) → ℝ)`
  have eNXE :
      (Matrix (Fin t) (Fin c) ℝ × (Matrix (Fin r) (Fin t) ℝ × Matrix (Fin r) (Fin c) ℝ)) ≃L[ℝ]
      (((Fin t × Fin c) ⊕ ((Fin r × Fin t) ⊕ (Fin r × Fin c))) → ℝ) :=
    ((matrixCoordCLE t c).prodCongr eXE).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin t × Fin c)
        ((Fin r × Fin t) ⊕ (Fin r × Fin c)) (fun _ => ℝ)).symm
  -- outer: `K × (N × (X × E)) ≃L (KΠ × ((NXE)Π)) ≃L ((KIdx ⊕ (NXEIdx)) → ℝ)`
  exact ((matrixCoordCLE t t).prodCongr eNXE).trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin t × Fin t)
      ((Fin t × Fin c) ⊕ ((Fin r × Fin t) ⊕ (Fin r × Fin c))) (fun _ => ℝ)).symm

/-- **The LDU-param reshape CLE** `LDUParam t ≃L (roleIdx → ℝ)`. `LDUParam t` is a Pi-product, so
two `sumPiEquivProdPi.symm` collect the three role-Pi's into one Pi over the sum index
`LowIdx ⊕ (Fin t ⊕ UpIdx)`. -/
def lduParamReshapeCLE (t : ℕ) :
    LDUParam t ≃L[ℝ] ((LowIdx t ⊕ (Fin t ⊕ UpIdx t)) → ℝ) := by
  -- inner: `(Fin t → ℝ) × (UpIdx → ℝ) ≃L ((Fin t ⊕ UpIdx) → ℝ)`
  have eQU : ((Fin t → ℝ) × (UpIdx t → ℝ)) ≃L[ℝ] ((Fin t ⊕ UpIdx t) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin t) (UpIdx t) (fun _ => ℝ)).symm
  -- outer: `(LowIdx → ℝ) × ((Fin t ⊕ UpIdx) → ℝ) ≃L ((LowIdx ⊕ (Fin t ⊕ UpIdx)) → ℝ)`
  exact ((ContinuousLinearEquiv.refl ℝ (LowIdx t → ℝ)).prodCongr eQU).trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (LowIdx t) (Fin t ⊕ UpIdx t) (fun _ => ℝ)).symm

/-! ## Non-vacuity: the reshapes elaborate as genuine CLEs (fire on a concrete `t,r,c`) -/

/-- Non-vacuity: `schurIncReshapeCLE` / `lduParamReshapeCLE` are genuine CLEs — they map the engine
block types into the flat coordinate Pi (the per-boundary `E`-block bridge). -/
example (z : SchurInc 2 1 1) (w : LDUParam 2) :
    (((Fin 2 × Fin 2) ⊕ ((Fin 2 × Fin 1) ⊕ ((Fin 1 × Fin 2) ⊕ (Fin 1 × Fin 1)))) → ℝ)
      × ((LowIdx 2 ⊕ (Fin 2 ⊕ UpIdx 2)) → ℝ) :=
  (schurIncReshapeCLE 2 1 1 z, lduParamReshapeCLE 2 w)

end DLNFibre.DLN.RLCT

end
