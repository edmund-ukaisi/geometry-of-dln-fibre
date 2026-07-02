import DLNFibre.Core.Analysis.RLCT.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# `RLCT.Integrability` — the integrability threshold and the 1-D witness

The RLCT **integrability threshold** of a loss germ `K` on a neighbourhood `U`:

`integrabilityThreshold K U := sSup (admissibleExponents K U)`

— the supremum of the exponents `c ≥ 0` at which `∫_U K^{-c}` is finite (`RLCT.Basic`). This is the
real log-canonical threshold **value**, defined by integrability alone, **cite-free**. It is *named*
a threshold, not `rlct`: the RLCT is classically this value, but pinning "the RLCT" to the zeta-pole
`(λ, m)` pair (with its multiplicity `m`) needs the cited meromorphic continuation and is deferred;
this module builds the agnostic substrate the chosen definition connects to.

**Contents.**
* `integrabilityThreshold` — the value; `admissibleExponents_downward` — the admissible set is a
  down-set (domination) when `0 ≤ K ≤ 1` on `U`;
* `integrabilityThreshold_mono` — monotone in the germ (`K ≤ K'` on `U`, `K` strictly positive
  there, `K'` in the pole regime ⟹ ordered — a milder singularity gives the larger threshold);
* **the 1-D witness** `integrabilityThreshold_abs = 1`: the power germ `K(t) = |t|` on `Ioo 0 t` has
  threshold exactly `1` (`∫₀ t^{-c}` finite iff `c < 1`). This *validates the formulation* — the
  classical value comes out right.

**Boundedness scope (name = content).** `sSup` in `ℝ` is the honest threshold precisely when the
admissible set is bounded above — the *pole* case, which is what the RLCT is about. A germ with no
pole at `x₀` (every `c` admissible) has an unbounded admissible set; `sSup` is then the `ℝ`-junk
`0`, and the value is out of scope (not claimed). The witness and every property below stay inside
the bounded/pole regime.
-/

open MeasureTheory Set Real

namespace RLCT

variable {n : ℕ}

/-- The **RLCT integrability threshold** of the loss germ `K` on the neighbourhood `U`: the supremum
of the admissible exponents (the `c ≥ 0` with `K^{-c}` integrable on `U`). The cite-free real
log-canonical threshold value. -/
noncomputable def integrabilityThreshold (K : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) : ℝ :=
  sSup (admissibleExponents K U)

lemma integrabilityThreshold_def (K : (Fin n → ℝ) → ℝ) (U : Set (Fin n → ℝ)) :
    integrabilityThreshold K U = sSup (admissibleExponents K U) := rfl

/-- **Down-set (domination) property.** If `c` is admissible and `0 ≤ c' ≤ c`, then `c'` is
admissible, provided `0 ≤ K ≤ 1` on `U`: then `K^{-c'} ≤ K^{-c}` pointwise (a less-negative exponent
on a base in `[0,1]`), so `K^{-c'}` is dominated by the integrable `K^{-c}`. At the zeros `{K = 0}`
both sides collapse to `0` (for `c' > 0`); the `c' = 0` case is `zero_mem_admissibleExponents`. -/
lemma admissibleExponents_downward {K : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hKmeas : Measurable K) (hUmeas : MeasurableSet U) (hK0 : ∀ x ∈ U, 0 ≤ K x)
    (hK1 : ∀ x ∈ U, K x ≤ 1) (hU1 : IntegrableOn (fun _ ↦ (1 : ℝ)) U)
    {c c' : ℝ} (hc : c ∈ admissibleExponents K U) (hc'0 : 0 ≤ c') (hcc' : c' ≤ c) :
    c' ∈ admissibleExponents K U := by
  rcases eq_or_lt_of_le hc'0 with hc'eq | hc'pos
  · -- `c' = 0`: use the constant-`1` route.
    rw [← hc'eq]; exact zero_mem_admissibleExponents hU1
  refine ⟨hc'0, ?_⟩
  have hdom : IntegrableOn (negPow K c) U := hc.2
  refine Integrable.mono' hdom (measurable_negPow hKmeas c').aestronglyMeasurable ?_
  -- `‖K^{-c'}‖ ≤ K^{-c}` everywhere on `U`, hence a.e. on `volume.restrict U`.
  refine ae_restrict_of_forall_mem hUmeas (fun x hx ↦ ?_)
  have hKx0 : 0 ≤ K x := hK0 x hx
  have hKx1 : K x ≤ 1 := hK1 x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (negPow_nonneg hKx0 c')]
  simp only [negPow_apply]
  rcases eq_or_lt_of_le hKx0 with hKxeq | hKxpos
  · -- `K x = 0`: both sides `0^(neg) = 0` (`c', c > 0`).
    rw [← hKxeq, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · -- `0 < K x ≤ 1`: less-negative exponent gives the smaller value.
    exact Real.rpow_le_rpow_of_exponent_ge hKxpos hKx1 (by linarith)

/-- **Germ monotonicity (strict-positive form).** If `K ≤ K'` on `U` with `K` strictly positive
there, then every exponent admissible for `K` is admissible for `K'`: pointwise `K'^{-c} ≤ K^{-c}`
(a larger base with a nonpositive exponent gives a smaller value), so `K'^{-c}` is dominated by the
integrable `K^{-c}`. A larger germ has (weakly) smaller negative powers, hence integrates at least
as well — its admissible set is at least as large. -/
lemma admissibleExponents_subset_of_le {K K' : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hK'meas : Measurable K') (hUmeas : MeasurableSet U) (hKpos : ∀ x ∈ U, 0 < K x)
    (hle : ∀ x ∈ U, K x ≤ K' x) :
    admissibleExponents K U ⊆ admissibleExponents K' U := by
  rintro c ⟨hc0, hint⟩
  refine ⟨hc0, ?_⟩
  refine Integrable.mono' hint (measurable_negPow hK'meas c).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem hUmeas (fun x hx ↦ ?_)
  have hKx : 0 < K x := hKpos x hx
  have hKx' : K x ≤ K' x := hle x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (negPow_nonneg (le_of_lt (hKx.trans_le hKx')) c)]
  simp only [negPow_apply]
  -- `(K' x)^(-c) ≤ (K x)^(-c)` : larger base, exponent `-c ≤ 0`.
  exact Real.rpow_le_rpow_of_nonpos hKx hKx' (by linarith)

/-- **Threshold monotonicity in the germ.** With the hypotheses of
`admissibleExponents_subset_of_le` plus `BddAbove (admissibleExponents K' U)` (the pole regime:
`K'` still has a finite threshold), the integrability threshold is monotone:
`integrabilityThreshold K U ≤ integrabilityThreshold K' U`. A larger germ (a milder singularity)
has the larger threshold. The `BddAbove` hypothesis is the `name = content` guard: `sSup` in `ℝ`
is the honest value only in the bounded/pole regime. -/
lemma integrabilityThreshold_mono {K K' : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
    (hK'meas : Measurable K') (hUmeas : MeasurableSet U) (hKpos : ∀ x ∈ U, 0 < K x)
    (hle : ∀ x ∈ U, K x ≤ K' x) (hne : (admissibleExponents K U).Nonempty)
    (hbdd : BddAbove (admissibleExponents K' U)) :
    integrabilityThreshold K U ≤ integrabilityThreshold K' U :=
  csSup_le_csSup hbdd hne
    (admissibleExponents_subset_of_le hK'meas hUmeas hKpos hle)

/-! ## The 1-D witness — the power germ `K(t) = |t|` has threshold `1`

The formulation is *validated* here: the germ `K = |·|` at `0`, integrated over `Ioo 0 t`, has
`∫ K^{-c}` finite iff `c < 1`, so the admissible set is `[0, 1)` and the threshold is exactly `1` —
the classical real log-canonical threshold of the power germ `|t|`. This is the non-vacuity witness
(bedrock): the definition gives the expected value. -/

/-- The 1-D witness germ `K(x) = |x 0|` on `Fin 1 → ℝ` (a genuine element of the framework's
`(Fin n → ℝ) → ℝ`). -/
noncomputable def absGerm : (Fin 1 → ℝ) → ℝ := fun x ↦ |x 0|

@[simp] lemma absGerm_apply (x : Fin 1 → ℝ) : absGerm x = |x 0| := rfl

/-- The witness neighbourhood `{x | x 0 ∈ Ioo 0 t}` — the preimage of `Ioo 0 t` under the coordinate
`x ↦ x 0`, a one-sided neighbourhood of `0` in the single coordinate. -/
def witnessNbhd (t : ℝ) : Set (Fin 1 → ℝ) :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' (Ioo (0 : ℝ) t)

/-- The witness admissible set is `[0, 1)`: `|x 0|^{-c}` is integrable on `{x 0 ∈ Ioo 0 t}` iff
`c < 1` (transported to the 1-D `∫₀ x^{-c}` dichotomy `integrableOn_Ioo_rpow_iff`, then `|x| = x` on
`Ioo 0 t`). -/
lemma admissibleExponents_absGerm (t : ℝ) (ht : 0 < t) :
    admissibleExponents absGerm (witnessNbhd t) = Ico 0 1 := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.funUnique (Fin 1) ℝ : (Fin 1 → ℝ) → ℝ) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  ext c
  simp only [admissibleExponents, mem_setOf_eq, mem_Ico]
  -- Transport the integrability to the 1-D `Ioo 0 t` via the measure-preserving `funUnique`.
  have hcomp : negPow absGerm c
      = (fun y : ℝ ↦ |y| ^ (-c)) ∘ (MeasurableEquiv.funUnique (Fin 1) ℝ : (Fin 1 → ℝ) → ℝ) := rfl
  have hbridge : IntegrableOn (negPow absGerm c) (witnessNbhd t) volume ↔
      IntegrableOn (fun y : ℝ ↦ |y| ^ (-c)) (Ioo (0 : ℝ) t) volume := by
    rw [hcomp, witnessNbhd]
    exact hmp.integrableOn_comp_preimage (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
  have hEq : EqOn (fun y : ℝ ↦ |y| ^ (-c)) (fun y : ℝ ↦ y ^ (-c)) (Ioo (0 : ℝ) t) :=
    fun y hy ↦ by simp only [abs_of_pos hy.1]
  rw [hbridge, integrableOn_congr_fun hEq measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff ht]
  constructor
  · rintro ⟨hc0, h⟩; exact ⟨hc0, by linarith⟩
  · rintro ⟨hc0, h⟩; exact ⟨hc0, by linarith⟩

/-- **The 1-D witness: `integrabilityThreshold |·| (Ioo 0 t) = 1`.** The power germ `K(t) = |t|` has
RLCT integrability threshold exactly `1` — the classical value. The definition is validated:
`sSup [0, 1) = 1`. Non-vacuity witness, shown in-file (bedrock). -/
theorem integrabilityThreshold_absGerm (t : ℝ) (ht : 0 < t) :
    integrabilityThreshold absGerm (witnessNbhd t) = 1 := by
  rw [integrabilityThreshold_def, admissibleExponents_absGerm t ht, csSup_Ico (by norm_num)]

end RLCT
