import DLNFibre.DLN.RLCT.Validate.RouteMSJChargeFactor
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra

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

/-- **The Frobenius inner product as a trace** `⟨A,B⟩_F = trace(A·Bᵀ)`. -/
theorem frobInner_eq_trace {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) :
    frobInner A B = Matrix.trace (A * Bᵀ) := by
  simp only [frobInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

/-! ## (F3) the pivot-row split and the R1 identity -/

/-- **(F3) `Q_inl = Y + Ã_z·Q_b`.** The pivot rows split into the transverse part `Y = Q_inl·Π_⊥` and
the `Q_b`-range part `Ã_z·Q_b` (`Ã_z = Q_inl·Q_bᵀ(Q_bQ_bᵀ)⁻¹`): `Q_inl·Π_⊥ + Q_inl·Q_bᵀG⁻¹·Q_b =
Q_inl·(Π_⊥ + Q_bᵀG⁻¹Q_b) = Q_inl·1 = Q_inl`. No invertibility needed (identical in `Π_⊥`'s definition). -/
theorem Q_inl_split {u b n : ℕ} (Q_inl : Matrix (Fin u) (Fin n) ℝ) (Q_b : Matrix (Fin b) (Fin n) ℝ) :
    Q_inl * (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b)
        + Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b
      = Q_inl := by
  rw [Matrix.mul_assoc Q_inl Q_bᵀ ((Q_b * Q_bᵀ)⁻¹),
    Matrix.mul_assoc Q_inl (Q_bᵀ * (Q_b * Q_bᵀ)⁻¹) Q_b, ← Matrix.mul_add,
    sub_add_cancel, Matrix.mul_one]

/-- **The R1 Frobenius-orthogonal split (couplerad §w3-boundary, abstract form).** The front loss
`E_top + E_tr` decouples into a `Y`-loss through the stacked front `E = [P;C]` plus a FREE `B̃·Q_b` block:

    frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ·Π_⊥) = frobSq([P;C]·Y) + frobSq(B̃·Q_b),

`Q̃ₚ = Q_inl + P⁻¹B₁₂Q_b`, `Π_⊥ = 1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`, `Y = Q_inl·Π_⊥`, `B̃ = B₁₂ + P·Q_inl·Q_bᵀ(Q_bQ_bᵀ)⁻¹`.
Hypotheses: `P` invertible (Q̃ₚ's `P·P⁻¹`) and `Q_bQ_bᵀ` invertible (`Π_⊥`). The cross term vanishes via
`Y·Q_bᵀ = 0` (F2). Abstract over generic matrices — instantiated at the `hsQ` objects downstream. -/
theorem R1_frobenius_split {u a b n : ℕ}
    (P : Matrix (Fin u) (Fin u) ℝ) (hP : IsUnit P.det)
    (B12 : Matrix (Fin u) (Fin b) ℝ) (C : Matrix (Fin a) (Fin u) ℝ)
    (Q_inl : Matrix (Fin u) (Fin n) ℝ) (Q_b : Matrix (Fin b) (Fin n) ℝ)
    (hG : IsUnit (Q_b * Q_bᵀ).det) :
    frobSq (P * (Q_inl + P⁻¹ * B12 * Q_b))
        + frobSq (C * (Q_inl + P⁻¹ * B12 * Q_b) * (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b))
      = frobSq (Matrix.fromRows P C * (Q_inl * (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b)))
        + frobSq ((B12 + P * (Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹)) * Q_b) := by
  -- transverse-projector facts + pivot-row split (explicit `Π_⊥`), then GENERALISE `Π_⊥` to a fresh
  -- variable `Pp` across the goal + these facts, so every occurrence is ONE atomic term (this defeats
  -- the `1`/`⁻¹` instance-diamond that otherwise blocks `rw`/`linarith` matching on composed terms).
  have hF1 : Q_b * (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b) = 0 := Qb_mul_projPerp Q_b hG
  have hF2 : (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b) * Q_bᵀ = 0 := projPerp_mul_QbT Q_b hG
  have hQsplit : Q_inl * (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b)
      + Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b = Q_inl := Q_inl_split Q_inl Q_b
  generalize hPp : (1 - Q_bᵀ * (Q_b * Q_bᵀ)⁻¹ * Q_b) = Pp at hF1 hF2 hQsplit ⊢
  -- STEP 1+2 (matrix): `P·Q̃ₚ = P·Y + B̃·Q_b`
  have hEtop_mat : P * (Q_inl + P⁻¹ * B12 * Q_b)
      = P * (Q_inl * Pp) + (B12 + P * (Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹)) * Q_b := by
    have h1 : P * (Q_inl + P⁻¹ * B12 * Q_b) = P * Q_inl + B12 * Q_b := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc P (P⁻¹ * B12) Q_b,
        ← Matrix.mul_assoc P P⁻¹ B12, Matrix.mul_nonsing_inv P hP, Matrix.one_mul]
    rw [h1]; nth_rewrite 1 [← hQsplit]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc P (Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹) Q_b]
    abel
  -- STEP 4 (matrix): `C·Q̃ₚ·Π_⊥ = C·Y`
  have hEtr_mat : C * (Q_inl + P⁻¹ * B12 * Q_b) * Pp = C * (Q_inl * Pp) := by
    rw [Matrix.mul_assoc C (Q_inl + P⁻¹ * B12 * Q_b) Pp, Matrix.add_mul,
      Matrix.mul_assoc (P⁻¹ * B12) Q_b Pp, hF1, Matrix.mul_zero, add_zero]
  -- STEP 3: cross term zero (via `Y·Q_bᵀ = 0`)
  have hYQbT : Q_inl * Pp * Q_bᵀ = 0 := by
    rw [Matrix.mul_assoc Q_inl Pp Q_bᵀ, hF2, Matrix.mul_zero]
  have hPYQ : P * (Q_inl * Pp) * Q_bᵀ = 0 := by
    rw [Matrix.mul_assoc P (Q_inl * Pp) Q_bᵀ, hYQbT, Matrix.mul_zero]
  have hcross : frobInner (P * (Q_inl * Pp))
      ((B12 + P * (Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹)) * Q_b) = 0 := by
    rw [frobInner_eq_trace, Matrix.transpose_mul,
      ← Matrix.mul_assoc (P * (Q_inl * Pp)) Q_bᵀ _, hPYQ, Matrix.zero_mul, Matrix.trace_zero]
  -- the three real-valued equalities (all atoms in terms of `Pp`, so `linarith` matches them)
  have e1 : frobSq (P * (Q_inl + P⁻¹ * B12 * Q_b))
      = frobSq (P * (Q_inl * Pp)) + frobSq ((B12 + P * (Q_inl * Q_bᵀ * (Q_b * Q_bᵀ)⁻¹)) * Q_b) := by
    rw [hEtop_mat]; exact frobSq_add_of_frobInner_zero _ _ hcross
  have e2 : frobSq (C * (Q_inl + P⁻¹ * B12 * Q_b) * Pp)
      = frobSq (C * (Q_inl * Pp)) := congrArg frobSq hEtr_mat
  have hl : (Matrix.fromRows (P * (Q_inl * Pp)) (C * (Q_inl * Pp))).submatrix Sum.inl id
      = P * (Q_inl * Pp) := by ext i j; simp [Matrix.fromRows, Matrix.submatrix_apply]
  have hr : (Matrix.fromRows (P * (Q_inl * Pp)) (C * (Q_inl * Pp))).submatrix Sum.inr id
      = C * (Q_inl * Pp) := by ext i j; simp [Matrix.fromRows, Matrix.submatrix_apply]
  have e3 : frobSq (Matrix.fromRows P C * (Q_inl * Pp))
      = frobSq (P * (Q_inl * Pp)) + frobSq (C * (Q_inl * Pp)) := by
    rw [show Matrix.fromRows P C * (Q_inl * Pp)
          = Matrix.fromRows (P * (Q_inl * Pp)) (C * (Q_inl * Pp)) from Matrix.fromRows_mul P C _,
      frobSq_row_split _, hl, hr]
  linear_combination e1 + e2 - e3

end DLNFibre.DLN.RLCT
