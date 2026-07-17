import DLNFibre.DLN.RLCT.Validate.RouteMSJChargeFactor

set_option linter.style.longLine false

/-!
# `RouteMSJInteriorR1` — the R1 Frobenius-orthogonal split (couplerad §w3-boundary), reusable atoms

The interior composition's R1 step: the front loss `E_top + E_tr` decouples into a `Y`-loss through the
stacked front `E = [P;C]` plus a FREE `B̃·Q_b` block,

    E_top + E_tr = frobSq(E·Y) + frobSq(B̃·Q_b),
    Y = Q_inl·Π_⊥,  Π_⊥ = 1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b,  B̃ = B₁₂ + P·Q_inl·Q_bᵀ(Q_bQ_bᵀ)⁻¹,  E = [P;C],

where the cross term vanishes via `Q_b·Π_⊥ = 0` / `Π_⊥·Q_bᵀ = 0` (couplerad's firmed chain F1–F3 + steps 1–6).
This file banks the REUSABLE ATOMS (network-free, `frobSq`-level): the Frobenius inner product, the
cross-term-zero additivity `frobSq(A+B) = frobSq A + frobSq B`, and the two transverse-projector facts.
Stated abstractly (generic matrices) — the `hsQ` instantiation is downstream, keeping the heavy terms out of
these proofs (the abstract-`Aux` discipline, lean/CLAUDE.md).

S2-FREE, no measure theory; axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-! ## The Frobenius inner product and the cross-term additivity -/

/-- **The Frobenius inner product** `⟨A,B⟩_F = ∑ᵢⱼ Aᵢⱼ·Bᵢⱼ` (the polarisation of `frobSq`). -/
noncomputable def frobInner {a b : Type*} [Fintype a] [Fintype b] (A B : a → b → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- **The Frobenius expansion** `frobSq(A+B) = frobSq A + 2·⟨A,B⟩_F + frobSq B`. -/
theorem frobSq_add {a b : Type*} [Fintype a] [Fintype b] (A B : a → b → ℝ) :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  simp only [frobSq, frobInner, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **Cross-term-zero additivity.** If `⟨A,B⟩_F = 0` then `frobSq(A+B) = frobSq A + frobSq B`. -/
theorem frobSq_add_of_frobInner_zero {a b : Type*} [Fintype a] [Fintype b] (A B : a → b → ℝ)
    (h : frobInner A B = 0) :
    frobSq (A + B) = frobSq A + frobSq B := by
  rw [frobSq_add, h]; ring

/-! ## The transverse projector `Π_⊥ = 1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b` -/

/-- **(F1) `Q_b·Π_⊥ = 0`.** The corank rows are killed by the transverse projector: `Q_b·(1 −
Q_bᵀG⁻¹Q_b) = Q_b − (Q_bQ_bᵀ)G⁻¹Q_b = Q_b − Q_b = 0`, using `G·G⁻¹ = 1` (`Q_bQ_bᵀ` invertible). -/
theorem Qb_mul_projPerp {b n : ℕ} (Qb : Matrix (Fin b) (Fin n) ℝ)
    (hG : IsUnit (Qb * Qbᵀ).det) :
    Qb * (1 - Qbᵀ * (Qb * Qbᵀ)⁻¹ * Qb) = 0 := by
  have hGG : (Qb * Qbᵀ) * (Qb * Qbᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGG,
    Matrix.one_mul, sub_self]

/-- **(F2) `Π_⊥·Q_bᵀ = 0`.** Dual of (F1): `(1 − Q_bᵀG⁻¹Q_b)·Q_bᵀ = Q_bᵀ − Q_bᵀG⁻¹(Q_bQ_bᵀ) =
Q_bᵀ − Q_bᵀ = 0`, using `G⁻¹·G = 1`. -/
theorem projPerp_mul_QbT {b n : ℕ} (Qb : Matrix (Fin b) (Fin n) ℝ)
    (hG : IsUnit (Qb * Qbᵀ).det) :
    (1 - Qbᵀ * (Qb * Qbᵀ)⁻¹ * Qb) * Qbᵀ = 0 := by
  have hGG : (Qb * Qbᵀ)⁻¹ * (Qb * Qbᵀ) = 1 := Matrix.nonsing_inv_mul _ hG
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc (Qbᵀ * (Qb * Qbᵀ)⁻¹) Qb Qbᵀ,
    Matrix.mul_assoc Qbᵀ (Qb * Qbᵀ)⁻¹ (Qb * Qbᵀ), hGG, Matrix.mul_one, sub_self]

end DLNFibre.DLN.RLCT
