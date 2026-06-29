import DLNFibre.DLN.RLCT.Validate.RouteMFactorFDeriv
import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMChainDiff` — b-FrameM-2 assembly (2): the chain-constructor differentiability atoms

The chain-telescope differentiability atoms for b-FrameM-2 (`item3-frameM-buildspec.md`): the chaining
row `chainQ` and lift column `chainA` are `DifferentiableAt` in their matrix arguments, the keystone
residual of `RouteMChartDiff.phiFlatLiveR1_differentiableAt_of_Agen` (`Agen s = chainA(N_s, W_s,
Cgen(s+1))`).

**The cast-avoiding route (validated this tide).** `chainQ`/`chainA` are `reindex`/`Sum.elim`/`of`
assemblies over a `Fin t ⊕ Fin (M'−t)` SUM-indexed intermediate matrix space — which carries NO norm
instance (the banked `instNormedAddCommGroupMatrix` is for `Fin l`/`Fin m` indices only). So the
`reindex`-as-CLE route stalls at the Sum-indexed space. The fix: differentiate **PER-ENTRY** — each
entry lands in `ℝ` (always normed), dodging the Sum-matrix wall. Decompose the row/column index `r :
Fin M'` via `finSplit` (the kept/lift split), then the banked entry laws `chainA_apply_castAdd`/`_natAdd`
/ `chainQ_apply_castAdd`/`_natAdd` reduce each entry to `(C − N·W) i j` / `W a j` / `1 i j` / `N i a`,
each differentiable by the matrix-op atoms (`DifferentiableAt.matMul` + `.sub` + the read entries).

* `DifferentiableAt.matMul` — the `DifferentiableAt` form of the banked `HasFDerivAt.matMul` (product
  rule for matrix-valued maps).
* `diffAt_chainQ` — `x ↦ chainQ h (N x)` differentiable (the `[I | N]` chaining row).
* `diffAt_chainA` — `x ↦ chainA h (N x) (W x) (C x)` differentiable (the `[C − N·W ; W]` lift column).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus + the banked matrix fderiv).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The `DifferentiableAt` matrix product rule.** If `f`, `g` (composable matrix-valued) are
differentiable at `x`, so is `fun y => f y * g y` — the `DifferentiableAt` shadow of the banked
`HasFDerivAt.matMul`. -/
theorem DifferentiableAt.matMul {l m n : ℕ} {f : G → Matrix (Fin l) (Fin m) ℝ}
    {g : G → Matrix (Fin m) (Fin n) ℝ} {x : G}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => f y * g y) x :=
  (HasFDerivAt.matMul hf.hasFDerivAt hg.hasFDerivAt).differentiableAt

/-- **`chainQ` is differentiable in its `N` argument.** `chainQ h N = [I_t | N]`; per-column
(`finSplit`): the kept block is the constant `I` (`differentiableAt_const`), the lift block is `N`
(differentiable). The chaining-row residual of the `Agen`/`Cgen` differentiability. -/
theorem diffAt_chainQ {N' M' t c : ℕ} (h : t + c = M')
    (Nf : (Fin N' → ℝ) → Matrix (Fin t) (Fin c) ℝ) (u : Fin N' → ℝ) (hNf : DifferentiableAt ℝ Nf u) :
    DifferentiableAt ℝ (fun x => chainQ h (Nf x)) u := by
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro col
  rw [show col = (finSplit (show t ≤ M' by omega)).symm ((finSplit (show t ≤ M' by omega)) col) from
    (Equiv.symm_apply_apply _ _).symm]
  set s := (finSplit (show t ≤ M' by omega)) col with hs
  clear_value s
  cases s with
  | inl jj =>
    have hidx : (finSplit (show t ≤ M' by omega)).symm (Sum.inl jj)
        = Fin.cast h (Fin.castAdd c jj) := by
      simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
        finSumFinEquiv_apply_left, finCongr_apply]; apply Fin.ext; simp
    rw [hidx, show (fun x => chainQ h (Nf x) i (Fin.cast h (Fin.castAdd c jj)))
        = fun _ => (1 : Matrix (Fin t) (Fin t) ℝ) i jj from by funext x; rw [chainQ_apply_castAdd]]
    exact differentiableAt_const _
  | inr a =>
    have hidx : (finSplit (show t ≤ M' by omega)).symm (Sum.inr a)
        = Fin.cast h (Fin.natAdd t (Fin.cast (by omega : M' - t = c) a)) := by
      simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
        finSumFinEquiv_apply_right, finCongr_apply]; apply Fin.ext; simp
    rw [hidx, show (fun x => chainQ h (Nf x) i
          (Fin.cast h (Fin.natAdd t (Fin.cast (by omega : M' - t = c) a))))
        = fun x => Nf x i (Fin.cast (by omega : M' - t = c) a) from by
      funext x; rw [chainQ_apply_natAdd]]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hNf i) _

/-- **`chainA` is differentiable in its `(N, W, C)` arguments.** `chainA h N W C = [C − N·W ; W]`;
per-row (`finSplit`): the kept rows are `C − N·W` (`DifferentiableAt.matMul` + `.sub`), the lift rows
are `W` (differentiable). The lift-column residual of the `Agen` differentiability. -/
theorem diffAt_chainA {N' M' t c m' : ℕ} (h : t + c = M')
    (Nf : (Fin N' → ℝ) → Matrix (Fin t) (Fin c) ℝ) (Wf : (Fin N' → ℝ) → Matrix (Fin c) (Fin m') ℝ)
    (Cf : (Fin N' → ℝ) → Matrix (Fin t) (Fin m') ℝ) (u : Fin N' → ℝ)
    (hNf : DifferentiableAt ℝ Nf u) (hWf : DifferentiableAt ℝ Wf u) (hCf : DifferentiableAt ℝ Cf u) :
    DifferentiableAt ℝ (fun x => chainA h (Nf x) (Wf x) (Cf x)) u := by
  apply differentiableAt_pi.mpr; intro r
  apply differentiableAt_pi.mpr; intro j
  rw [show r = (finSplit (show t ≤ M' by omega)).symm ((finSplit (show t ≤ M' by omega)) r) from
    (Equiv.symm_apply_apply _ _).symm]
  set s := (finSplit (show t ≤ M' by omega)) r with hs
  clear_value s
  cases s with
  | inl i =>
    have hidx : (finSplit (show t ≤ M' by omega)).symm (Sum.inl i)
        = Fin.cast h (Fin.castAdd c i) := by
      simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
        finSumFinEquiv_apply_left, finCongr_apply]; apply Fin.ext; simp
    rw [hidx, show (fun x => chainA h (Nf x) (Wf x) (Cf x) (Fin.cast h (Fin.castAdd c i)) j)
        = fun x => (Cf x - Nf x * Wf x) i j from by funext x; rw [chainA_apply_castAdd]]
    exact differentiableAt_pi.mp
      (differentiableAt_pi.mp (hCf.sub (DifferentiableAt.matMul hNf hWf)) i) j
  | inr a =>
    have hidx : (finSplit (show t ≤ M' by omega)).symm (Sum.inr a)
        = Fin.cast h (Fin.natAdd t (Fin.cast (by omega : M' - t = c) a)) := by
      simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm,
        finSumFinEquiv_apply_right, finCongr_apply]; apply Fin.ext; simp
    rw [hidx, show (fun x => chainA h (Nf x) (Wf x) (Cf x)
          (Fin.cast h (Fin.natAdd t (Fin.cast (by omega : M' - t = c) a))) j)
        = fun x => Wf x (Fin.cast (by omega : M' - t = c) a) j from by
      funext x; rw [chainA_apply_natAdd]]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp hWf _) j

end DLNFibre.DLN.RLCT
