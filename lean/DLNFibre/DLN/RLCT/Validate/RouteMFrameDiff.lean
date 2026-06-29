import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# `RouteMFrameDiff` — b-FrameM-2 toolkit: differentiability atoms over opaque-width matrix maps (Pi form)

The foundational differentiability toolkit for the Route (b) det_comp ladder's b-FrameM-2 step
(`item3-frameM-buildspec.md`): establishing `DifferentiableAt phiFlatLiveR1 u` over OPAQUE width
tuples — the existence of the chart Jacobian `DFrame_M` that the b-FrameM-3 keystone
(`toMatrix_blockTriangular_of_locality`, `RouteMFrameLocality`) consumes to discharge the headline's
`hbt`. (Only the EXISTENCE of a derivative is needed — the keystone reads off any `D` from
`DifferentiableAt.hasFDerivAt`; the matrix VALUES come from the engine separately.)

**The cast-avoiding design move (validated this tide).** The naive `fun_prop` route FAILS over opaque
widths (`Matrix.of` unregistered; abstract `Matrix.mul` whnf-times-out — and `Matrix m n ℝ` carries NO
norm instance). The fix: work entirely in the **Pi function form** `Fin a → Fin b → ℝ` (which IS
normed, the product norm), NOT the abstract `Matrix` type. This is exactly the codebase's `Params`
shape (`Params H = ∀ s, Fin _ → Fin _ → ℝ` with the sup-norm `instNormedAddCommGroupParams`), so the
atoms compose directly into `chartParamsGen`. Each chart output coordinate is a polynomial in the input
reads — a `Finset.sum` of products — differentiated by `differentiableAt_pi` + `DifferentiableAt.fun_sum`
+ `.mul`, NO `fin_cases` on the opaque row index.

* `diffAt_entry` — an entry of a differentiable matrix-map is differentiable.
* `diffAt_matmul` — the matrix product (explicit-sum form `= Matrix.mul_apply`) of two differentiable
  matrix-maps is differentiable (the chain's `B·chainQ`, `N·W`, `C·suffix` products).
* `diffAt_matadd` / `diffAt_smul` — matrix sum / radial-scalar scaling (the chain's `+ u·R`).
* `diffAt_read` — a decoder-block read `x ↦ (fun i j => x (rd i j))` is differentiable (the
  `readK/X/N/E/W` single-coordinate reads through the `chartIdxEquiv` reindex).
* `diffAt_constBlock` — a constant block (identity boundary, fixed pivot) is differentiable.

These are network-free (Mathlib calculus over Pi types). The remaining b-FrameM-2 work is the ASSEMBLY:
thread these through the chain constructors (`chainQ`/`chainA`/`Cgen`/`Agen` telescope → `chartParamsGen`
→ `paramsEquivFlat`), each a sub-piece. Once assembled, `DifferentiableAt phiFlatLiveR1 u` +
`toMatrix_blockTriangular_of_locality` discharge `hbt`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus; no S2).
-/

open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-- **An entry of a differentiable matrix-map is differentiable.** For `g : (Fin N → ℝ) → (Fin a →
Fin b → ℝ)` differentiable at `u`, the scalar entry `x ↦ g x i j` is differentiable at `u`
(`differentiableAt_pi` twice). The per-coordinate read of any differentiable matrix-valued chart map. -/
theorem diffAt_entry {N a b : ℕ} (g : (Fin N → ℝ) → (Fin a → Fin b → ℝ)) (u : Fin N → ℝ)
    (hg : DifferentiableAt ℝ g u) (i : Fin a) (j : Fin b) :
    DifferentiableAt ℝ (fun x => g x i j) u :=
  differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j

/-- **The matrix product of two differentiable matrix-maps is differentiable** (explicit-sum form,
`= Matrix.mul_apply`). Each output entry `∑ k, g x i k · h x k j` is a finite sum of products of
differentiable entries (`DifferentiableAt.fun_sum` + `.mul`). The chain's matrix products (`B·chainQ`,
`N·W`, the suffix telescope) over opaque inner widths. -/
theorem diffAt_matmul {N a b c : ℕ}
    (g : (Fin N → ℝ) → (Fin a → Fin b → ℝ)) (h : (Fin N → ℝ) → (Fin b → Fin c → ℝ))
    (u : Fin N → ℝ) (hg : DifferentiableAt ℝ g u) (hh : DifferentiableAt ℝ h u) :
    DifferentiableAt ℝ (fun x => (fun i j => ∑ k, g x i k * h x k j)) u := by
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  apply DifferentiableAt.fun_sum; intro k _
  exact (diffAt_entry g u hg i k).mul (diffAt_entry h u hh k j)

/-- **The matrix sum of two differentiable matrix-maps is differentiable** (the chain's `B·chainQ +
u·R`). Pi-pointwise `.add`. -/
theorem diffAt_matadd {N a b : ℕ}
    (g h : (Fin N → ℝ) → (Fin a → Fin b → ℝ)) (u : Fin N → ℝ)
    (hg : DifferentiableAt ℝ g u) (hh : DifferentiableAt ℝ h u) :
    DifferentiableAt ℝ (fun x => g x + h x) u := hg.add hh

/-- **The radial-scalar scaling of a differentiable matrix-map is differentiable** (the chain's `u·R`,
with the radial `u = x p` itself a differentiable read). `DifferentiableAt.smul`. -/
theorem diffAt_smul {N a b : ℕ} (s : (Fin N → ℝ) → ℝ) (g : (Fin N → ℝ) → (Fin a → Fin b → ℝ))
    (u : Fin N → ℝ) (hs : DifferentiableAt ℝ s u) (hg : DifferentiableAt ℝ g u) :
    DifferentiableAt ℝ (fun x => s x • g x) u := hs.smul hg

/-- **A decoder-block read is differentiable.** Each entry is a single coordinate `x (rd i j)` (the
`readK/X/N/E/W` reads through the `chartIdxEquiv.symm` reindex `rd`), so the assembled block is
differentiable (`differentiableAt_apply` per entry). -/
theorem diffAt_read {N a b : ℕ} (rd : Fin a → Fin b → Fin N) (u : Fin N → ℝ) :
    DifferentiableAt ℝ (fun x : Fin N → ℝ => (fun i j => x (rd i j))) u := by
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  exact differentiableAt_apply (rd i j) u

/-- **A constant block is differentiable** (the identity boundary `Bmat 0 = 1`, the fixed `1`-pivot,
the dead leaf `0`). `differentiableAt_const`. -/
theorem diffAt_constBlock {N a b : ℕ} (c : Fin a → Fin b → ℝ) (u : Fin N → ℝ) :
    DifferentiableAt ℝ (fun _ : Fin N → ℝ => c) u := differentiableAt_const c

/-! ## Non-vacuity: a one-layer chart fragment (read · read + radial·read) is differentiable -/

/-- **Non-vacuity.** A one-layer chart fragment — a matrix-product of two reads, plus a radial-scaled
read (`(read₁ · read₂) + (x p)·read₃`, the `B·chainQ + u·R` shape) — is differentiable over opaque
widths. Confirms the atoms compose into the chain's per-layer building block. -/
example {N a b c : ℕ} (rd1 : Fin a → Fin b → Fin N) (rd2 : Fin b → Fin c → Fin N)
    (rd3 : Fin a → Fin c → Fin N) (p : Fin N) (u : Fin N → ℝ) :
    DifferentiableAt ℝ
      (fun x : Fin N → ℝ =>
        (fun i j => ∑ k, x (rd1 i k) * x (rd2 k j)) + (x p) • (fun i j => x (rd3 i j))) u :=
  (diffAt_matmul _ _ u (diffAt_read rd1 u) (diffAt_read rd2 u)).add
    (diffAt_smul _ _ u (differentiableAt_apply p u) (diffAt_read rd3 u))

end DLNFibre.DLN.RLCT
