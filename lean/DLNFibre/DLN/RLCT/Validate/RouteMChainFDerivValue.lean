import DLNFibre.DLN.RLCT.Validate.RouteMChainDiff

/-!
# `RouteMChainFDerivValue` — the fderiv VALUE of a `chainA` layer (opaque-width, the staircase atom)

Sub-piece 1 of the opaque-`M` fderiv-as-staircase construction
(`staircase-twosided-wrapper-statement-card`): the per-layer chain matrix `chainA h N W C` has an
EXPLICIT `HasFDerivAt` value, not only differentiability (`RouteMChainDiff.diffAt_chainA`). Where
`diffAt_chainA` differentiates per-entry (dodging the Sum-indexed no-norm wall), this records the
corresponding fderiv CLM `chainAFDeriv`: its `(r, j)` entry, read through `finSplit r`, is the
differential of the kept block `C − N·W` (on `Sum.inl`) or of the lift block `W` (on `Sum.inr`). The
kept-block differential is the product-rule CLM
`C' − ((matMulBilin).precompR (N x) W' + (matMulBilin).precompL N' (W x))`.

This is the network-free, opaque-width fderiv VALUE the staircase diagonal blocks (radial/Schur⊗LDU)
are then identified WITH (the remaining engine-identification sub-piece). It dodges the
Sum-matrix-no-norm wall the same way `diffAt_chainA` does — per entry into `ℝ`.

* `chainAFDeriv` — the fderiv CLM, per entry the kept/lift differential via `finSplit`.
* `hasFDerivAt_chainA` — `HasFDerivAt (fun x => chainA h (N x) (W x) (C x)) (chainAFDeriv …) u`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus + the banked matrix fderiv).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The fderiv CLM of a `chainA` layer.** The continuous linear map whose `(r, j)` entry — read
through the kept/lift split `finSplit r` — is the differential of the kept block `C − N·W`
(`Sum.inl i`) or of the lift block `W` (`Sum.inr a`). Assembled per-entry from the product-rule CLM
(`HasFDerivAt.matMul`'s `precompR`/`precompL`) so each coordinate lands in `ℝ` (no-norm-wall dodge).
-/
noncomputable def chainAFDeriv {Nn M' t c m' : ℕ} (h : t + c = M')
    (Nf : (Fin Nn → ℝ) → Matrix (Fin t) (Fin c) ℝ) (Wf : (Fin Nn → ℝ) → Matrix (Fin c) (Fin m') ℝ)
    (dN : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin t) (Fin c) ℝ)
    (dW : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin c) (Fin m') ℝ)
    (dC : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin t) (Fin m') ℝ) (u : Fin Nn → ℝ) :
    (Fin Nn → ℝ) →L[ℝ] Matrix (Fin M') (Fin m') ℝ :=
  -- the kept-block differential CLM `D(C − N·W)`; the lift block carries `dW` (reindexed onto rows)
  let keptD : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin t) (Fin m') ℝ :=
    dC - ((matMulBilin t c m').precompR (Fin Nn → ℝ) (Nf u) dW
      + (matMulBilin t c m').precompL (Fin Nn → ℝ) dN (Wf u))
  ContinuousLinearMap.pi (fun r : Fin M' =>
    ContinuousLinearMap.pi (fun j : Fin m' =>
      Sum.elim
        (fun i : Fin t => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.proj i).comp keptD))
        (fun a : Fin (M' - t) => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.proj (Fin.cast (by omega : M' - t = c) a)).comp dW))
        (finSplit (show t ≤ M' by omega) r)))

/-- **The fderiv VALUE of a `chainA` layer.** If `Nf`, `Wf`, `Cf` have fderivs `dN`, `dW`, `dC` at
`u`, then `fun x => chainA h (Nf x) (Wf x) (Cf x)` has fderiv `chainAFDeriv h Nf Wf dN dW dC u`.
Proven per entry (`hasFDerivAt_pi''` twice, the `finSplit` kept/lift case split +
`chainA_apply_castAdd`/`_natAdd`), matching each entry against the `chainAFDeriv` coordinate —
dodging the Sum-indexed no-norm wall as `diffAt_chainA` does. The kept entries are the product-rule
differential of `C − N·W`; the lift entries are `dW`. -/
theorem hasFDerivAt_chainA {Nn M' t c m' : ℕ} (h : t + c = M')
    (Nf : (Fin Nn → ℝ) → Matrix (Fin t) (Fin c) ℝ) (Wf : (Fin Nn → ℝ) → Matrix (Fin c) (Fin m') ℝ)
    (Cf : (Fin Nn → ℝ) → Matrix (Fin t) (Fin m') ℝ)
    (dN : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin t) (Fin c) ℝ)
    (dW : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin c) (Fin m') ℝ)
    (dC : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin t) (Fin m') ℝ) (u : Fin Nn → ℝ)
    (hN : HasFDerivAt Nf dN u) (hW : HasFDerivAt Wf dW u) (hC : HasFDerivAt Cf dC u) :
    HasFDerivAt (fun x => chainA h (Nf x) (Wf x) (Cf x)) (chainAFDeriv h Nf Wf dN dW dC u) u := by
  -- the kept-block map `C − N·W` has fderiv `keptD` (product rule on `N·W`, then sub)
  have hkept : HasFDerivAt (fun x => Cf x - Nf x * Wf x)
      (dC - ((matMulBilin t c m').precompR (Fin Nn → ℝ) (Nf u) dW
        + (matMulBilin t c m').precompL (Fin Nn → ℝ) dN (Wf u))) u :=
    hC.sub (HasFDerivAt.matMul hN hW)
  apply hasFDerivAt_pi''
  intro r
  apply hasFDerivAt_pi''
  intro j
  -- reduce `(proj j).comp ((proj r).comp chainAFDeriv)` to the `Sum.elim … (finSplit r)` coordinate
  -- (`proj_pi` is `rfl`), then case-split the row by the kept/lift split.
  rw [show (ContinuousLinearMap.proj j).comp
      ((ContinuousLinearMap.proj r).comp (chainAFDeriv h Nf Wf dN dW dC u))
      = Sum.elim
        (fun i : Fin t => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.proj i).comp
            (dC - ((matMulBilin t c m').precompR (Fin Nn → ℝ) (Nf u) dW
              + (matMulBilin t c m').precompL (Fin Nn → ℝ) dN (Wf u)))))
        (fun a : Fin (M' - t) => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.proj (Fin.cast (by omega : M' - t = c) a)).comp dW))
        (finSplit (show t ≤ M' by omega) r) from rfl]
  set s := (finSplit (show t ≤ M' by omega)) r with hs
  have hr : r = (finSplit (show t ≤ M' by omega)).symm s := by rw [hs, Equiv.symm_apply_apply]
  clear_value s
  subst hr
  cases s with
  | inl i =>
    have hidx : (finSplit (show t ≤ M' by omega)).symm (Sum.inl i)
        = Fin.cast h (Fin.castAdd c i) := by
      simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
        finSumFinEquiv_apply_left, finCongr_apply]; apply Fin.ext; simp
    rw [Sum.elim_inl,
      show (fun x => chainA h (Nf x) (Wf x) (Cf x)
            ((finSplit (show t ≤ M' by omega)).symm (Sum.inl i)) j)
        = fun x => (Cf x - Nf x * Wf x) i j from by funext x; rw [hidx, chainA_apply_castAdd]]
    exact (ContinuousLinearMap.proj j : (Fin m' → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp u
      ((ContinuousLinearMap.proj i : (Fin t → (Fin m' → ℝ)) →L[ℝ] (Fin m' → ℝ)).hasFDerivAt.comp u
        hkept)
  | inr a =>
    have hidx : (finSplit (show t ≤ M' by omega)).symm (Sum.inr a)
        = Fin.cast h (Fin.natAdd t (Fin.cast (by omega : M' - t = c) a)) := by
      simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
        finSumFinEquiv_apply_right, finCongr_apply]; apply Fin.ext; simp
    rw [Sum.elim_inr,
      show (fun x => chainA h (Nf x) (Wf x) (Cf x)
            ((finSplit (show t ≤ M' by omega)).symm (Sum.inr a)) j)
        = fun x => Wf x (Fin.cast (by omega : M' - t = c) a) j from by
      funext x; rw [hidx, chainA_apply_natAdd]]
    exact (ContinuousLinearMap.proj j : (Fin m' → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp u
      ((ContinuousLinearMap.proj (Fin.cast (by omega : M' - t = c) a)
        : (Fin c → (Fin m' → ℝ)) →L[ℝ] (Fin m' → ℝ)).hasFDerivAt.comp u hW)

/-! ## Non-vacuity: the fderiv-value lemma fires on a genuine linear-reader layer

The atom is usable: feeding genuine differentiable readers (here the identity map on `Fin Nn → ℝ`
projected into the matrix blocks via constant placements) produces the `chainA` fderiv. Confirms the
hypotheses `hN`/`hW`/`hC` are satisfiable and the conclusion fires end-to-end. -/

/-- **Non-vacuity.** With constant readers, the `chainA` layer is constant in `x`, so its fderiv is
`chainAFDeriv` at the (zero-derivative) base — the lemma fires, confirming it is not vacuous. -/
example {Nn M' t c m' : ℕ} (h : t + c = M')
    (N0 : Matrix (Fin t) (Fin c) ℝ) (W0 : Matrix (Fin c) (Fin m') ℝ)
    (C0 : Matrix (Fin t) (Fin m') ℝ) (u : Fin Nn → ℝ) :
    HasFDerivAt (fun _ : Fin Nn → ℝ => chainA h N0 W0 C0)
      (chainAFDeriv h (fun _ => N0) (fun _ => W0) 0 0 0 u) u :=
  hasFDerivAt_chainA h (fun _ => N0) (fun _ => W0) (fun _ => C0) 0 0 0 u
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) (hasFDerivAt_const _ _)

end DLNFibre.DLN.RLCT
