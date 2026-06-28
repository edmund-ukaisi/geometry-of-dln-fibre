/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `DLNFibre.Core.SchurFibreVanishing` — a Schur polynomial over `O(F)` vanishing on all fibre points is zero

The coefficientwise zero-test at the heart of the `Ψ`-direction vanishingIdeal descent (thread 31,
the route-3 wall): a polynomial `h : MvPolynomial σ O(F)` over the fibre coordinate ring
`O(F) = MvPolynomial τ k ⧸ vanishingIdeal F` is **zero** as soon as, for every choice of `σ`-variable
values `s : σ → k` and every fibre point `y ∈ F`, the double evaluation (`O(F)`-coefficients at `y`,
then `σ`-variables at `s`) vanishes.

The proof is the two-stage decomposition Codex named:
1. fix `y ∈ F`; `evalFibrePt y : O(F) →ₐ[k] k` evaluates a coordinate class at `y` (well-defined: the
   point lies on `F`, so `vanishingIdeal F` is killed). `MvPolynomial.map (evalFibrePt y) h :
   MvPolynomial σ k` vanishes at every `s` (the hypothesis), so it is `0` by `MvPolynomial.funext`
   (`k` infinite);
2. hence each coefficient `evalFibrePt y (coeff m h) = 0` for all `y ∈ F` (`MvPolynomial.coeff_map`),
   i.e. the representative of `coeff m h` lies in `vanishingIdeal F`, so `coeff m h = 0` in `O(F)`;
3. all coefficients zero ⟹ `h = 0` (`MvPolynomial.ext`).

## Main results
- `evalFibrePt` — the point evaluation `O(F) →ₐ[k] k` at a point `y ∈ F`.
- `mvpoly_eq_zero_of_forall_eval_fibre` — the coefficientwise zero-test.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- **Point evaluation of the fibre coordinate ring.** For a point `y : τ → k` lying on `F` (so it
kills every `p ∈ vanishingIdeal F`), the `k`-algebra hom `O(F) →ₐ[k] k` evaluating a coordinate class
`mk(vanishingIdeal F) p` at `y`. Well-defined by `Ideal.Quotient.liftₐ` (the kernel condition is
exactly `y ∈ F`). -/
noncomputable def evalFibrePt {τ : Type*} {F : Set (τ → k)} {y : τ → k} (hy : y ∈ F) :
    (MvPolynomial τ k ⧸ vanishingIdeal k F) →ₐ[k] k :=
  Ideal.Quotient.liftₐ (vanishingIdeal k F) (MvPolynomial.aeval y)
    (fun p hp ↦ by simpa using hp y hy)

@[simp] theorem evalFibrePt_mk {τ : Type*} {F : Set (τ → k)} {y : τ → k} (hy : y ∈ F)
    (p : MvPolynomial τ k) :
    evalFibrePt hy (Ideal.Quotient.mk (vanishingIdeal k F) p) = MvPolynomial.aeval y p :=
  rfl

/-- **The coefficientwise zero-test (the route-3 wall).** A polynomial `h : MvPolynomial σ O(F)` over
the fibre coordinate ring is `0` if its double evaluation vanishes on all `(s, y)` with `y ∈ F`:

> `(∀ s : σ → k, ∀ y ∈ F, eval s (map (evalFibrePt …) h) = 0) → h = 0`.

For fixed `y ∈ F`, `map (evalFibrePt y) h : MvPolynomial σ k` vanishes at every `s`, hence is `0`
(`MvPolynomial.funext`, `k` infinite); so every coefficient `evalFibrePt y (coeff m h) = 0`
(`coeff_map`) for all `y ∈ F`, putting the representative of `coeff m h` in `vanishingIdeal F`, so
`coeff m h = 0` in `O(F)`; `MvPolynomial.ext` finishes. -/
theorem mvpoly_eq_zero_of_forall_eval_fibre [Infinite k] {σ τ : Type*} {F : Set (τ → k)}
    (h : MvPolynomial σ (MvPolynomial τ k ⧸ vanishingIdeal k F))
    (hvanish : ∀ (s : σ → k) (y : τ → k) (hy : y ∈ F),
      MvPolynomial.eval s (MvPolynomial.map (evalFibrePt hy).toRingHom h) = 0) :
    h = 0 := by
  -- each coefficient of `h`, evaluated at every fibre point `y`, is `0`.
  have hcoeff : ∀ (m : σ →₀ ℕ) (y : τ → k) (hy : y ∈ F),
      evalFibrePt hy (MvPolynomial.coeff m h) = 0 := by
    intro m y hy
    -- `map (evalFibrePt y) h` vanishes at every `s`, so it is `0` (funext over the infinite field).
    have hzero : MvPolynomial.map (evalFibrePt hy).toRingHom h = 0 := by
      apply MvPolynomial.funext
      intro s
      rw [map_zero]
      exact hvanish s y hy
    -- the `m`-coefficient of the zero polynomial is `0`; `coeff_map` reads it off `coeff m h`.
    have := MvPolynomial.coeff_map (evalFibrePt hy).toRingHom h m
    rw [hzero, MvPolynomial.coeff_zero] at this
    exact this.symm
  -- so each coefficient `coeff m h ∈ O(F)` vanishes at all `y ∈ F`, hence is `0`.
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  -- `coeff m h` is `mk(vanishingIdeal F)(rep)`; vanishing at all `y ∈ F` puts `rep ∈ vanishingIdeal F`.
  obtain ⟨rep, hrep⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.coeff m h)
  rw [← hrep, Ideal.Quotient.eq_zero_iff_mem]
  intro y hy
  have := hcoeff m y hy
  rw [← hrep, evalFibrePt_mk] at this
  simpa using this

end DLNFibre.Core
