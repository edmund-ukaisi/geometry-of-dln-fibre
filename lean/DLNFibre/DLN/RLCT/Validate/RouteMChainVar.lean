import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps

/-!
# `RouteMChainVar` — the VARIABLE-`N` chain block map (the OPTION-1 chain correction)

The banked `chainUnitMap N` (`RouteMGenChainBridge`) is the chaining `(W, C) ↦ (W, C − N·W)` with `N`
FIXED. For the OPTION-1 achiever-chart bridge (`thread.md` UPDATE-8, `codex/bridge-design-*`), `N_s` is
itself a coordinate, so the chain factor must read `N` from its own block and leave it unchanged:

  `chainVarMap (N, W, C) = (N, W, C − N·W)`,
  fderiv `(dN, dW, dC) ↦ (dN, dW, dC − (N·dW + dN·W))`,  det `1` (block-lower-triangular).

`N`, `W` are read/write identity components; the only nonlinear coupling is the bilinear `N·W` into `C`.
The fderiv is `id` plus a strictly-block-lower-triangular shear into the `C`-block, so `|det| = 1`. This
is the semantic chain factor the bridge needs; the fixed-`N` `chainUnitMap` is its specialization.

* `chainVarMap` / `chainVarD` — the map / its CLM fderiv (the product-rule output, so `hasFDerivAt` is
  immediate).
* `chainVarMap_hasFDerivAt` — `chainVarMap` has fderiv `chainVarD` at every point.
* `chainVarD_abs_det` — `|det (chainVarD z)| = 1` (unitriangular shear).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + determinant; no S2).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- The variable-`N` chain block space `Matrix (Fin t)(Fin c) × Matrix (Fin c)(Fin m') ×
Matrix (Fin t)(Fin m')` — the triple `(N, W, C)`. -/
abbrev ChainVarBlk (t c m' : ℕ) : Type :=
  Matrix (Fin t) (Fin c) ℝ × Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ

/-- **The variable-`N` chain map** `(N, W, C) ↦ (N, W, C − N·W)` — `N`, `W` carried unchanged, the
bilinear coupling `N·W` subtracted from `C`. -/
noncomputable def chainVarMap {t c m' : ℕ} (z : ChainVarBlk t c m') : ChainVarBlk t c m' :=
  (z.1, z.2.1, z.2.2 - z.1 * z.2.1)

/-- The CLM fderiv of `chainVarMap` (the product-rule output). -/
noncomputable def chainVarD {t c m' : ℕ} (z : ChainVarBlk t c m') :
    ChainVarBlk t c m' →L[ℝ] ChainVarBlk t c m' :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    (((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)).prod
      (((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
        - ((matMulBilin t c m').precompR (ChainVarBlk t c m') z.1
            ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
          + (matMulBilin t c m').precompL (ChainVarBlk t c m')
              (ContinuousLinearMap.fst ℝ _ _) z.2.1)))

/-- **The variable-`N` chain map has fderiv `chainVarD z`** at every point — the product rule on the
three output blocks (`N`, `W` projections; `C − N·W` via the matrix-mult bilinear `matMulBilin`). -/
theorem chainVarMap_hasFDerivAt {t c m' : ℕ} (z : ChainVarBlk t c m') :
    HasFDerivAt chainVarMap (chainVarD z) z := by
  have hN : HasFDerivAt (fun w : ChainVarBlk t c m' => w.1) (ContinuousLinearMap.fst ℝ _ _) z :=
    hasFDerivAt_fst
  have hW : HasFDerivAt (fun w : ChainVarBlk t c m' => w.2.1)
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) z :=
    hasFDerivAt_fst.comp z hasFDerivAt_snd
  have hC : HasFDerivAt (fun w : ChainVarBlk t c m' => w.2.2)
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) z :=
    hasFDerivAt_snd.comp z hasFDerivAt_snd
  exact hN.prodMk (hW.prodMk (hC.sub (HasFDerivAt.matMul hN hW)))

/-- **The variable-`N` chain map's fderiv has abs-det `1`** — it is `id` plus a strictly-block-lower-
triangular shear: the `(N, W)`-block maps by identity (the `fst` / `fst∘snd` projections), the coupling
`−(N·dW + dN·W)` lands only in the `C`-block (off-diagonal), and the `C`-block maps by identity
(`snd∘snd`). Conjugating by `prodAssoc` to `((N,W), C)`, this is `lowerTri id id (coupling)`, det
`1·1 = 1`. -/
theorem chainVarD_abs_det {t c m' : ℕ} (z : ChainVarBlk t c m') :
    |LinearMap.det (chainVarD z).toLinearMap| = 1 := by
  set A := Matrix (Fin t) (Fin c) ℝ
  set B := Matrix (Fin c) (Fin m') ℝ
  set C := Matrix (Fin t) (Fin m') ℝ
  -- the coupling functional `h : (A × B) →ₗ C`, `(dN, dW) ↦ −(z.1·dW + dN·z.2.1)`, built from CLMs
  -- so linearity is automatic.
  set h : (A × B) →ₗ[ℝ] C :=
    (-((((matMulBilin t c m' z.1).comp (ContinuousLinearMap.snd ℝ A B))
        + (((matMulBilin t c m').flip z.2.1).comp (ContinuousLinearMap.fst ℝ A B))) :
        (A × B) →L[ℝ] C)).toLinearMap with hh
  have hdet : LinearMap.det (chainVarD z).toLinearMap = 1 := by
    rw [show (chainVarD z).toLinearMap
        = ((LinearEquiv.prodAssoc ℝ A B C : ((A × B) × C) ≃ₗ[ℝ] (A × B × C)) :
              ((A × B) × C) →ₗ[ℝ] (A × B × C)) ∘ₗ
            (lowerTri (LinearMap.id (R := ℝ) (M := A × B)) (LinearMap.id (R := ℝ) (M := C)) h) ∘ₗ
            ((LinearEquiv.prodAssoc ℝ A B C).symm : (A × B × C) →ₗ[ℝ] ((A × B) × C)) from ?_]
    · rw [LinearMap.det_conj, lowerTri_det, LinearMap.det_id, LinearMap.det_id, mul_one]
    · apply LinearMap.ext
      intro v
      obtain ⟨vn, vw, vc⟩ := v
      rw [chainVarD]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply, matMulBilin_apply,
        lowerTri, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, hh,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.flip_apply]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      rfl
  rw [hdet, abs_one]

end DLNFibre.DLN.RLCT
