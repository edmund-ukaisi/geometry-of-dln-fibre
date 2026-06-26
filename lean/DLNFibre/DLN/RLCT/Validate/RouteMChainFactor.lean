import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# `RouteMChainFactor` — the per-level local-identity factorization engine (general-`M` achiever)

The reusable, M-agnostic algebra that turns the cert's per-boundary block data (the LDU-core
compressed transition `C_s = B_s · Q_s + u·R_s`, the unit-triangular chaining `Q_s · A_s = C_{s+1}`,
the radial-error `E_s = R_s · A_s`) into the abstract telescope's per-level local identity
`C_s · A_s = B_s · C_{s+1} + u • E_s` — exactly `RouteMAchieverTelescope.Chain.step`.

This DECOUPLES the telescope step from the block construction (the decorrelated-Codex design read, the
"`step_of_factor`" factorization): the only block-specific content is the chaining identity
`Q_s · A_s = C_{s+1}`, proved once on sum-blocks via `chain_block` (the cert's `[I | N]·[C−N·W ; W] = C`).
Everything else — the scalar telescope step — is generic matrix algebra over arbitrary index types.

* `step_of_factor` — the generic telescope step (any matrix shapes): from `Ck = Bk · Qk + u • Rk`,
  `Qk · Ak = Cnext`, `Ek = Rk · Ak`, derive `Ck · Ak = Bk · Cnext + u • Ek`.
* `chain_block` — the cert's chaining crux on sum-blocks: `[I | N]·[C − N·W ; W] = C`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-! ## The generic telescope step (the `step_of_factor` factorization) -/

/-- **The generic telescope step.** From the compressed-transition shape `Ck = Bk · Qk + u • Rk`, the
chaining identity `Qk · Ak = Cnext`, and the radial-error shape `Ek = Rk · Ak`, the abstract telescope's
per-level local identity `Ck · Ak = Bk · Cnext + u • Ek` follows by pure scalar matrix algebra
(`add_mul`, `smul_mul`, `mul_assoc Bk Qk Ak`, the chaining rewrite). Index types arbitrary —
this is M-agnostic, the seam between the block construction and `Chain.step`. -/
theorem step_of_factor {tk tk1 wk wk1 : Type*}
    [Fintype tk1] [Fintype wk]
    (u : ℝ)
    (Ck : Matrix tk wk ℝ) (Ak : Matrix wk wk1 ℝ) (Bk : Matrix tk tk1 ℝ)
    (Qk : Matrix tk1 wk ℝ) (Rk : Matrix tk wk ℝ) (Cnext : Matrix tk1 wk1 ℝ)
    (Ek : Matrix tk wk1 ℝ)
    (hC : Ck = Bk * Qk + u • Rk) (hQA : Qk * Ak = Cnext) (hE : Ek = Rk * Ak) :
    Ck * Ak = Bk * Cnext + u • Ek := by
  subst hC; subst hE
  rw [Matrix.add_mul, Matrix.smul_mul]
  rw [Matrix.mul_assoc Bk Qk Ak, hQA]

/-! ## The chaining crux (the cert's `[I | N]·[C − N·W ; W] = C`)

The unit-triangular chaining `A^(s) = G_s⁻¹ [C_{s+1} ; W_{s+1}] = [[C_{s+1} − N_s W_{s+1}],[W_{s+1}]]`
satisfies `Q_s A^(s) = C_{s+1}` with `Q_s = [I_{t_s} | N_s]`. On sum-blocks this is
`[I | N]·[C − N·W ; W] = I·(C − N·W) + N·W = C` — proved once here, the block-multiply `+ sub_add_cancel`.
`Q_s` is the horizontal block `of (Sum.elim 1 N)`; `A^(s)` the vertical block `of (Sum.elim (C−N·W) W)`. -/

/-- **The chaining crux** (`[I | N]·[C − N·W ; W] = C`, on sum-blocks). The chaining factor `A^(s)`,
written as the vertical block-column `of (fun (i : t ⊕ c) ↦ Sum.elim (C − N·W) W i)`, when
premultiplied by `Q = [I | N]` (the horizontal block-row `of (fun i ↦ Sum.elim (1 i) (N i))`), returns
`C`: the block product is `1·(C − N·W) + N·W = C`. The cert's uniform `B/C`-chaining identity. -/
theorem chain_block {t c m' : Type*} [Fintype t] [Fintype c] [DecidableEq t]
    (N : Matrix t c ℝ) (W : Matrix c m' ℝ) (C : Matrix t m' ℝ) :
    (Matrix.of (fun (i : t) (j : t ⊕ c) => Sum.elim ((1 : Matrix t t ℝ) i) (N i) j))
        * (Matrix.of (fun (i : t ⊕ c) (j : m') => Sum.elim (C - N * W) W i j))
      = C := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  -- `∑_k (1 i k)·(C−N·W) k j + ∑_k (N i k)·(W k j) = (C−N·W) i j + (N·W) i j = C i j`
  rw [← Matrix.mul_apply (M := (1 : Matrix t t ℝ)) (N := C - N * W),
      ← Matrix.mul_apply (M := N) (N := W)]
  rw [Matrix.one_mul, Matrix.sub_apply]
  ring

end DLNFibre.DLN.RLCT
