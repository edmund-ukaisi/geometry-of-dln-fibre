import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `Core.Aoyagi.WeightedCofactor` — the Q̂ cofactor machinery (thread-34, SEAT-L4)

The δ-agnostic row-recombination atom of the coupled Case-1 step. Aoyagi's left row-operation `Q₁`
(det-`0` as a source map, so NOT absorbable into the chart map `σ`) is reincorporated as the
conjugated cofactor `Q̂ = diag(b)·Q₁⁻¹·diag(b)⁻¹`, which "regenerates the row quotients". This
module builds `Q̂` at the right generality, avoiding the diagonal inverse (`b` vanishes at the
deepest point, so `diag(b)⁻¹` is junk there): `Q̂` is defined ENTRYWISE from `R := Q₁⁻¹` and an
explicit **divisibility ratio** `c` (`Q̂ a d = c a d · R a d`), and the conjugation is stated as
the inverse-free **commutation relation** `diag(b)·R = Q̂·diag(b)` (which holds wherever the ratio
witnesses `b_a = c a d · b_d` on the support of `R` — the divisibility chain `b₁|b₂|…`).

Properties (Codex-corroborated decomposition; NO matrix inverse / determinant needed):
`diagonal_mul_eq_weightedCofactor_mul_diagonal` (commutation), `continuousOn_weightedCofactor`
(entrywise continuity), `weightedCofactor_transport` (the residual transport `diag b·Hpre =
Q̂·(diag b·Hnext)` from a Schur identity `Hpre = R·Hnext` — the row-quotient regeneration),
`weightedCofactor_unitLower` (unipotent-preserved) and `weightedCofactor_eq_one` (`Q̂ = I` at the
deepest point). Abstract over the base space `X` and the row index `ι`.
-/

open Matrix Set Topology

namespace DLNFibre.Core.Aoyagi

/-- **The weighted cofactor** `Q̂` (thread-34): entrywise `Q̂ a d = c a d · R a d`, the conjugate
of a row operation `R` (`= Q₁⁻¹`) by the weights `b` via the ratio `c` — no diagonal inverse.
Over an arbitrary commutative ring `𝕜` (the DLN fold instantiates `𝕜 = (Fin D → ℝ) → ℝ` pointwise,
or `ℝ` per-point). -/
def weightedCofactor {ι X 𝕜 : Type*} [Fintype ι] [CommRing 𝕜] (c : X → ι → ι → 𝕜)
    (R : X → Matrix ι ι 𝕜) : X → Matrix ι ι 𝕜 :=
  fun x ↦ Matrix.of (fun a d ↦ c x a d * R x a d)

@[simp] theorem weightedCofactor_apply {ι X 𝕜 : Type*} [Fintype ι] [CommRing 𝕜] (c : X → ι → ι → 𝕜)
    (R : X → Matrix ι ι 𝕜) (x : X) (a d : ι) :
    weightedCofactor c R x a d = c x a d * R x a d := rfl

/-- **The commutation relation** `diag(b)·R = Q̂·diag(b)` — the inverse-free conjugation.
Holds on `V` wherever the divisibility ratio witnesses `b_a = c a d · b_d` on the support of `R`
(the chain `b₁|b₂|…`, encoded pointwise so no localization / diagonal inverse is needed). -/
theorem diagonal_mul_eq_weightedCofactor_mul_diagonal {ι X 𝕜 : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing 𝕜] (b : X → ι → 𝕜) (c : X → ι → ι → 𝕜) (R : X → Matrix ι ι 𝕜) {V : Set X}
    (hratio : ∀ x ∈ V, ∀ a d, R x a d ≠ 0 → b x a = c x a d * b x d) :
    Set.EqOn (fun x ↦ Matrix.diagonal (b x) * R x)
      (fun x ↦ weightedCofactor c R x * Matrix.diagonal (b x)) V := by
  intro x hx
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, weightedCofactor_apply]
  by_cases h : R x i j = 0
  · rw [h]; ring
  · rw [hratio x hx i j h]; ring

/-- **Entrywise continuity of `Q̂`** — `c`, `R` continuous ⟹ `Q̂` continuous (`StepInv`'s need). -/
theorem continuousOn_weightedCofactor {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (c : X → ι → ι → ℝ) (R : X → Matrix ι ι ℝ) {V : Set X}
    (hc : ∀ a d, ContinuousOn (fun x ↦ c x a d) V)
    (hR : ∀ a d, ContinuousOn (fun x ↦ R x a d) V) (a d : ι) :
    ContinuousOn (fun x ↦ weightedCofactor c R x a d) V := by
  simp only [weightedCofactor_apply]
  exact (hc a d).mul (hR a d)

/-- **The residual transport** (the row-quotient regeneration): from a Schur identity
`Hpre = R·Hnext`, the weighted residual `diag(b)·Hpre` re-expresses as `Q̂·(diag(b)·Hnext)` — the
child residual `diag(b)·Hnext` is recovered up to the left cofactor `Q̂`. -/
theorem weightedCofactor_transport {ι κ X 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [CommRing 𝕜]
    (b : X → ι → 𝕜) (c : X → ι → ι → 𝕜) (R : X → Matrix ι ι 𝕜) (Hpre Hnext : X → Matrix ι κ 𝕜)
    {V : Set X} (hratio : ∀ x ∈ V, ∀ a d, R x a d ≠ 0 → b x a = c x a d * b x d)
    (hSchur : Set.EqOn Hpre (fun x ↦ R x * Hnext x) V) :
    Set.EqOn (fun x ↦ Matrix.diagonal (b x) * Hpre x)
      (fun x ↦ weightedCofactor c R x * (Matrix.diagonal (b x) * Hnext x)) V := by
  intro x hx
  have hcomm := diagonal_mul_eq_weightedCofactor_mul_diagonal b c R hratio hx
  simp only at hcomm ⊢
  rw [hSchur hx, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]

/-- Unit-lower-triangular over a linear order: `1` on the diagonal, `0` strictly above. -/
def UnitLower {ι 𝕜 : Type*} [LinearOrder ι] [CommRing 𝕜] (A : Matrix ι ι 𝕜) : Prop :=
  (∀ a, A a a = 1) ∧ (∀ a d, a < d → A a d = 0)

/-- **`Q̂` is unipotent** (unit-lower) when `R` is and the ratio is `1` on the diagonal. -/
theorem weightedCofactor_unitLower {ι X 𝕜 : Type*} [Fintype ι] [LinearOrder ι] [CommRing 𝕜]
    (c : X → ι → ι → 𝕜) (R : X → Matrix ι ι 𝕜) (x : X)
    (hc1 : ∀ a, c x a a = 1) (hR : UnitLower (R x)) :
    UnitLower (weightedCofactor c R x) := by
  refine ⟨fun a ↦ ?_, fun a d had ↦ ?_⟩
  · simp [weightedCofactor_apply, hc1 a, hR.1 a]
  · simp [weightedCofactor_apply, hR.2 a d had]

/-- **`Q̂ = I` at the deepest point** — `R = I` there (the row op is trivial at `0`) and the ratio
`1` on the diagonal ⟹ `Q̂ = I`. (Off-diagonal `R = 0`, diagonal `c·1 = 1`.) -/
theorem weightedCofactor_eq_one {ι X 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [CommRing 𝕜]
    (c : X → ι → ι → 𝕜) (R : X → Matrix ι ι 𝕜) (x₀ : X)
    (hR0 : R x₀ = 1) (hc0 : ∀ a, c x₀ a a = 1) :
    weightedCofactor c R x₀ = 1 := by
  ext i j
  rw [weightedCofactor_apply, hR0]
  by_cases h : i = j
  · subst h; simp [hc0 i]
  · rw [Matrix.one_apply_ne h, mul_zero]

end DLNFibre.Core.Aoyagi
