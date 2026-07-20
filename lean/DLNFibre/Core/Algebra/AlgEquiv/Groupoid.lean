/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.Algebra.Algebra.Equiv

/-!
# `AlgEquiv` groupoid laws — `trans_assoc`, `trans_refl`, `refl_trans`

The category/groupoid identities for `AlgEquiv.trans` and `AlgEquiv.refl`: composition is
associative and `refl` is a two-sided identity. Mathlib v4.29
(`Mathlib.Algebra.Algebra.Equiv`) carries the inverse laws `AlgEquiv.self_trans_symm` /
`symm_trans_self` and `trans_apply`, but **not** these three identity/associativity laws — they
exist only at the bare `Equiv` level (`Equiv.trans_assoc`). Each holds by `ext x; rfl`, since
`AlgEquiv.trans` composes the underlying functions and `refl` is the identity function.

These are stated at the abstract `AlgEquiv` level (not on any concrete localized chart type), so a
downstream cocycle round-trip — `(e.symm.trans e').trans …` rearrangements — discharges by rewriting
with these laws rather than by extensionality on a heavy double-localized presentation.

The declarations live in the bare Mathlib-mirror namespace `AlgEquiv` (mirroring
`Mathlib.Algebra.Algebra.Equiv`), not a `DLNFibre.Core.`-prefixed one.
-/

namespace AlgEquiv

variable {R : Type*} {A₁ : Type*} {A₂ : Type*} {A₃ : Type*} {A₄ : Type*}
variable [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃] [Semiring A₄]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃] [Algebra R A₄]

/-- `AlgEquiv.trans` is associative. -/
theorem trans_assoc (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (e₃ : A₃ ≃ₐ[R] A₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) := by
  ext x; rfl

/-- `AlgEquiv.refl` is a right identity for `AlgEquiv.trans`. -/
theorem trans_refl (e : A₁ ≃ₐ[R] A₂) : e.trans (AlgEquiv.refl) = e := by
  ext x; rfl

/-- `AlgEquiv.refl` is a left identity for `AlgEquiv.trans`. -/
theorem refl_trans (e : A₁ ≃ₐ[R] A₂) : (AlgEquiv.refl).trans e = e := by
  ext x; rfl

end AlgEquiv
