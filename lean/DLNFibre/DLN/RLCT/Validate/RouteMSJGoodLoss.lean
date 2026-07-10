import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGoodLoss` — good-chart cross-coupled loss positivity

**Thread `genm-l2prod`, Stage 2 (S,J) production.** The §8 unit-boundedness gate needs the resolved
good-chart corner loss `g_cc` to be strictly positive on the unit sphere. After the depth reduction
(vslice cert §4a) the cross-coupled Schur loss is, exactly,

    g_cc(Γ, v) = frobSq (P · v · A₂) + frobSq ((C · v + Γ · W) · A₂),

a SUM of two squared-linear terms in the joint block `(Γ, v)` (`P` the invertible pivot block, `Γ`
the corank block, `v` the boundary rows, `C, W` resolved layer maps, `A₂` the shared deep factor).
This is a positive-SEMIdefinite quadratic form; it is positive-DEFINITE — hence `> 0` off the
origin, hence on the sphere — exactly when the map `sjGoodMap` is injective (jbassembly §1b/§3a).

This module isolates that injectivity, network-free (pure matrix algebra):

* **`sjGoodMap`** — the linear map `(Γ, v) ↦ (P·v·A₂, (C·v + Γ·W)·A₂)` underlying `g_cc`.
* **`sjGoodMap_injective`** — it is injective as soon as the pivot `P` has a LEFT inverse and the
  resolved maps `W`, `A₂` have RIGHT inverses (i.e. full row rank — the good-chart hypotheses: pivot
  bounded below, deep factor generic). The kernel argument: the first component + `P, A₂` invertible
  force `v = 0`; then the second + `W, A₂` invertible force `Γ = 0`.
* **`sjGoodMap_loss_pos`** — the §8 payoff: on the good chart `g_cc(Γ, v) > 0` for `(Γ, v) ≠ 0`.
  This is the strict positivity that (via the compactness gate `exists_pos_lower_bound_on_sphere`)
  supplies the corner endpoint's uniform sphere lower bound.

S2-FREE; axiom-clean `[propext, Classical.choice, Quot.sound]`. The joint block `(Γ, v)` has
`dim = (M₀−t)(M₁−t) + t·(width) = Mval(branch)`; flattening to `Fin n → ℝ` and firing the endpoint
`corner_block_cube_lintegral_lt_top_of_injective` (both this and the flatten deferred to the CoV
assembly) is the good-chart leaf of `sjJointResolution`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {t p q h o : ℕ}

/-- **The good-chart cross-coupled linear map** `(Γ, v) ↦ (P·v·A₂, (C·v + Γ·W)·A₂)` — the map
underlying the resolved loss `g_cc(Γ, v) = frobSq (P·v·A₂) + frobSq ((C·v + Γ·W)·A₂)` (vslice cert
§4a). `Γ : (M₀−t)×(M₁−t)` corank block, `v : t×· ` boundary rows; `P` pivot, `C, W` resolved layer
maps, `A₂` the shared deep factor. -/
def sjGoodMap (P : Matrix (Fin t) (Fin t) ℝ) (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) :
    (Matrix (Fin p) (Fin q) ℝ × Matrix (Fin t) (Fin h) ℝ) →
      (Matrix (Fin t) (Fin o) ℝ × Matrix (Fin p) (Fin o) ℝ) :=
  fun x => (P * x.2 * A2, (C * x.2 + x.1 * W) * A2)

@[simp] theorem sjGoodMap_apply (P : Matrix (Fin t) (Fin t) ℝ) (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ)
    (Γ : Matrix (Fin p) (Fin q) ℝ) (v : Matrix (Fin t) (Fin h) ℝ) :
    sjGoodMap P C W A2 (Γ, v) = (P * v * A2, (C * v + Γ * W) * A2) := rfl

/-- `sjGoodMap … 0 = 0` (both blocks vanish at the origin). -/
theorem sjGoodMap_apply_zero (P : Matrix (Fin t) (Fin t) ℝ) (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) :
    sjGoodMap P C W A2 0 = 0 := by
  simp [sjGoodMap]

/-- **The good-chart map is injective** given the good-chart invertibility: the pivot `P` has a LEFT
inverse `LP` and the resolved maps `W`, `A₂` have RIGHT inverses `RW`, `RA` (full row rank). Kernel
argument: the first block `P·v·A₂` + `LP·(·)·RA` forces `v = 0`; the second block `(C·v + Γ·W)·A₂`
with `v = 0` + `(·)·RA·RW` forces `Γ = 0`. Compass-clean: every inverse is a bounded-below unit
coefficient, never a Jacobian determinant. -/
theorem sjGoodMap_injective
    (P : Matrix (Fin t) (Fin t) ℝ) (LP : Matrix (Fin t) (Fin t) ℝ) (hP : LP * P = 1)
    (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (RW : Matrix (Fin h) (Fin q) ℝ) (hW : W * RW = 1)
    (A2 : Matrix (Fin h) (Fin o) ℝ) (RA : Matrix (Fin o) (Fin h) ℝ) (hA2 : A2 * RA = 1) :
    Function.Injective (sjGoodMap P C W A2) := by
  -- `LP·(P·w·A₂)·RA = w` for any `w` (pivot + deep-factor invertibility).
  have keyv : ∀ w : Matrix (Fin t) (Fin h) ℝ, LP * (P * w * A2) * RA = w := by
    intro w
    rw [← Matrix.mul_assoc LP (P * w) A2, ← Matrix.mul_assoc LP P w, hP, Matrix.one_mul,
      Matrix.mul_assoc w A2 RA, hA2, Matrix.mul_one]
  -- `Z·W·A₂·RA·RW = Z` for any `Z` (deep-factor + `W` invertibility).
  have keyG : ∀ Z : Matrix (Fin p) (Fin q) ℝ, Z * W * A2 * RA * RW = Z := by
    intro Z
    rw [Matrix.mul_assoc (Z * W) A2 RA, hA2, Matrix.mul_one, Matrix.mul_assoc Z W RW, hW,
      Matrix.mul_one]
  rintro ⟨Γ, v⟩ ⟨Γ', v'⟩ hxy
  simp only [sjGoodMap_apply, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  -- `v = v'` from the first block.
  have hv : v = v' := by
    have e : LP * (P * v * A2) * RA = LP * (P * v' * A2) * RA :=
      congrArg (fun M : Matrix (Fin t) (Fin o) ℝ => LP * M * RA) h1
    rw [keyv, keyv] at e; exact e
  -- `Γ = Γ'` from the second block, using `v = v'`.
  rw [← hv, Matrix.add_mul, Matrix.add_mul] at h2
  have hcancel : Γ * W * A2 = Γ' * W * A2 := add_left_cancel h2
  have hΓ : Γ = Γ' := by
    have e : Γ * W * A2 * RA * RW = Γ' * W * A2 * RA * RW :=
      congrArg (fun M : Matrix (Fin p) (Fin o) ℝ => M * RA * RW) hcancel
    rw [keyG, keyG] at e; exact e
  exact Prod.ext hΓ hv

/-- **A nonzero real matrix has strictly positive Frobenius energy.** `M ≠ 0 → 0 < frobSq M`
(some entry is nonzero, its square is positive, the sum of squares dominates it). -/
theorem frobSq_pos_of_ne_zero {a b : Type*} [Fintype a] [Fintype b] (M : a → b → ℝ) (hM : M ≠ 0) :
    0 < frobSq M := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hM
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  have hj' : M i j ≠ 0 := by simpa using hj
  refine Finset.sum_pos' (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg _)) ?_
  exact ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j' _ => sq_nonneg _)
    ⟨j, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj'))⟩⟩

/-- **§8 positivity — the good-chart cross-coupled loss is positive off the origin.** For
`(Γ, v) ≠ 0` the resolved loss `g_cc(Γ, v) = frobSq (P·v·A₂) + frobSq ((C·v + Γ·W)·A₂)` is strictly
positive, given the good-chart invertibility (pivot left inverse, deep factor + `W` right inverses).
Since `sjGoodMap`
is injective and sends `0 ↦ 0`, `sjGoodMap (Γ,v) ≠ 0`, so at least one block is nonzero and its
Frobenius energy is positive (`frobSq_pos_of_ne_zero`), the other being nonnegative. This is the
sphere-positivity the compactness gate `exists_pos_lower_bound_on_sphere` upgrades to the corner
endpoint's uniform lower bound. -/
theorem sjGoodMap_loss_pos
    (P : Matrix (Fin t) (Fin t) ℝ) (LP : Matrix (Fin t) (Fin t) ℝ) (hP : LP * P = 1)
    (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (RW : Matrix (Fin h) (Fin q) ℝ) (hW : W * RW = 1)
    (A2 : Matrix (Fin h) (Fin o) ℝ) (RA : Matrix (Fin o) (Fin h) ℝ) (hA2 : A2 * RA = 1)
    (x : Matrix (Fin p) (Fin q) ℝ × Matrix (Fin t) (Fin h) ℝ) (hx : x ≠ 0) :
    0 < frobSq (sjGoodMap P C W A2 x).1 + frobSq (sjGoodMap P C W A2 x).2 := by
  have hne : sjGoodMap P C W A2 x ≠ 0 := fun h =>
    hx ((sjGoodMap_injective P LP hP C W RW hW A2 RA hA2)
      (h.trans (sjGoodMap_apply_zero P C W A2).symm))
  rw [Ne, Prod.ext_iff, not_and_or] at hne
  rcases hne with h1 | h2
  · exact add_pos_of_pos_of_nonneg (frobSq_pos_of_ne_zero _ h1) (frobSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (frobSq_nonneg _) (frobSq_pos_of_ne_zero _ h2)

end DLNFibre.DLN.RLCT
