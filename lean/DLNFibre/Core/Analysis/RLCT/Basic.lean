import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `RLCT.Basic` — the loss germ and its negative-power integrability

The **cite-free analytic substrate** of the real log-canonical threshold (RLCT). We fix a
nonnegative *loss germ* `K : (Fin n → ℝ) → ℝ` with `K ≥ 0`, a base point `x₀` (typically a zero,
`K x₀ = 0`), and a neighbourhood `U` on which we study the local integrability of the negative power
`K^(-c)` for a real exponent `c ≥ 0`.

The object of study is `admissibleExponents K U := {c ≥ 0 | IntegrableOn (K^(-c)) U}` — the set of
exponents at which `∫_U K^{-c}` is finite. As `c` grows the pole `K^{-c}` at `{K = 0}` sharpens, so
this set is a down-set; the exponent at which it turns finite → infinite is the RLCT
**integrability threshold** (`RLCT.Integrability`). This is the value the eventual zeta-pole `λ`
must match; here it is defined by *integrability alone*, with **no** cited analytic monument.

**Scope note (name = content).** `admissibleExponents` reads the ℝ-valued Bochner integrability of
`K^{-c}`. Over `ℝ`, `Real.rpow` sends `(0:ℝ)^(neg) = 0` (`Real.zero_rpow`), so the pole is invisible
*at* the zero set `{K = 0}`; the integrability still sees the blow-up on `{K > 0}` (an open, full-
measure set for a germ that does not vanish on an open set), so on such germs the ℝ formulation is
faithful. The 1-D witness `K = |·|` (`RLCT.Integrability`) confirms the formulation gives the
classical value `1`.

Bare Mathlib-mirror namespace `RLCT` (network-free; does not shadow any `DLNFibre.Core.X`).
-/

open MeasureTheory Set Real

namespace RLCT

variable {n : ℕ}

/-- The negative power `K^{-c}` of a loss germ, as an ℝ-valued function of the parameter. The object
whose local integrability defines the RLCT integrability threshold. -/
noncomputable def negPow (K : (Fin n → ℝ) → ℝ) (c : ℝ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ (K x) ^ (-c)

@[simp] lemma negPow_apply (K : (Fin n → ℝ) → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    negPow K c x = (K x) ^ (-c) := rfl

/-- `K^0 = 1` everywhere: the zero exponent gives the constant germ `1`. -/
@[simp] lemma negPow_zero (K : (Fin n → ℝ) → ℝ) : negPow K 0 = fun _ ↦ (1 : ℝ) := by
  funext x; simp [negPow]

/-- `K^{-c} ≥ 0` at any point where `K ≥ 0` (`Real.rpow` of a nonnegative base is nonnegative). -/
lemma negPow_nonneg {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hx : 0 ≤ K x) (c : ℝ) :
    0 ≤ negPow K c x :=
  Real.rpow_nonneg hx _

/-- `negPow K c` is measurable whenever `K` is (via `fun_prop`: composition of the measurable `K`
with the measurable `· ^ (-c)`). -/
lemma measurable_negPow {K : (Fin n → ℝ) → ℝ} (hK : Measurable K) (c : ℝ) :
    Measurable (negPow K c) := by
  unfold negPow; fun_prop

/-- An exponent `c` is **admissible** for the germ `K` on the neighbourhood `U` when `c ≥ 0` and the
negative power `K^{-c}` is integrable on `U`. The RLCT threshold is the supremum of the admissible
exponents. -/
def admissibleExponents (K : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ IntegrableOn (negPow K c) U}

lemma mem_admissibleExponents {K : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} {c : ℝ} :
    c ∈ admissibleExponents K U ↔ 0 ≤ c ∧ IntegrableOn (negPow K c) U := Iff.rfl

/-- Every admissible exponent is nonnegative. -/
lemma nonneg_of_mem_admissibleExponents {K : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} {c : ℝ}
    (hc : c ∈ admissibleExponents K U) : 0 ≤ c := hc.1

/-- `0` is admissible whenever the constant germ `1` is integrable on `U` (e.g. `U` of finite
measure): `K^0 = 1`. So the admissible set is nonempty on any finite-measure neighbourhood. -/
lemma zero_mem_admissibleExponents {K : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hU : IntegrableOn (fun _ ↦ (1 : ℝ)) U) : (0 : ℝ) ∈ admissibleExponents K U := by
  refine ⟨le_rfl, ?_⟩
  simpa [negPow_zero] using hU

end RLCT
