import DLNFibre.Core.Analysis.RLCT.Local
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `RLCT.RegularPoint` — the regular-point lemma (A1): `rlctAt K x = +∞` at a nonzero point

**A regular point carries no pole.** For a continuous nonnegative germ `K` and a point `x` with
`K x ≠ 0`, **every** exponent `c ≥ 0` is locally admissible: `K^(-c)` is continuous near `x`
(the base `K` is continuous and stays away from `0` on the open set `{K ≠ 0} ∋ x`, so the germ
`y ↦ (K y)^(-c)` is continuous there), hence locally integrable at `x`. So

`localAdmissibleExponents K x = Set.Ici 0`,

and the admissible set is **unbounded** (`¬ BddAbove …`) — the honest local value is `+∞`
(paper Prop 8.3(i): `rlct_x(F) < ∞ ⟺ F x = 0`). The ℝ-valued `rlctAt K x = sSup (Ici 0)` is the
documented junk-`0`, *not* claimed as a value; the content is the *shape* of the admissible set.

This is the cite-free analytic input to the global validation witness
(`RLCT.Global.rlctGlobal (sumSq C) = C/2`, `RLCT.GlobalWitness`): off the origin the sum-of-squares
germ is regular, so it contributes no constraint to the global admissible set, which is thus
governed entirely by the pole at `0`.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology

namespace RLCT

variable {n : ℕ}

/-- **`negPow K c` is continuous on `{K ≠ 0}`.** Where the base `K` (continuous) is nonzero, the
germ `y ↦ (K y)^(-c)` is continuous: `Real.continuousAt_rpow_const` fires on the `K y ≠ 0` branch,
so no sign condition on `c` is needed. -/
lemma continuousOn_negPow_ne_zero {K : (Fin n → ℝ) → ℝ} (hK : Continuous K) (c : ℝ) :
    ContinuousOn (negPow K c) {y | K y ≠ 0} := by
  intro y hy
  refine ((hK.continuousAt).rpow_const (Or.inl hy)).continuousWithinAt

/-- **A regular point is locally admissible at every exponent.** For a continuous nonnegative germ
`K` with `K x ≠ 0`, every `c ≥ 0` lies in `localAdmissibleExponents K x`: `negPow K c` is continuous
on the open set `{K ≠ 0} ∋ x` (`continuousOn_negPow_ne_zero`), hence locally integrable there, so
integrable on some neighbourhood of `x`. -/
lemma mem_localAdmissibleExponents_of_ne_zero {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK : Continuous K) (hx : K x ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    c ∈ localAdmissibleExponents K x := by
  refine ⟨hc, ?_⟩
  -- `{K ≠ 0}` is open and contains `x`; `negPow K c` is continuous on it, hence loc-integrable.
  have hVopen : IsOpen {y : Fin n → ℝ | K y ≠ 0} := hK.isOpen_preimage {0}ᶜ isOpen_compl_singleton
  have hxV : x ∈ {y : Fin n → ℝ | K y ≠ 0} := hx
  have hloc : LocallyIntegrableOn (negPow K c) {y : Fin n → ℝ | K y ≠ 0} :=
    (continuousOn_negPow_ne_zero hK c).locallyIntegrableOn hVopen.measurableSet
  -- `LocallyIntegrableOn` gives `IntegrableAtFilter (𝓝[V] x)`; on the open `V ∋ x`, `𝓝[V] x = 𝓝 x`.
  have := hloc x hxV
  rwa [hVopen.nhdsWithin_eq hxV] at this

/-- **The regular-point lemma (A1): `localAdmissibleExponents K x = Set.Ici 0`.** For a continuous
nonnegative germ `K` with `K x ≠ 0` (a *regular* point), the locally-admissible exponents are
*exactly* `[0, ∞)`: membership is `0 ≤ c` (always, `mem_localAdmissibleExponents_of_ne_zero`), and
conversely every admissible exponent is `≥ 0` by definition. No pole at `x`. -/
theorem localAdmissibleExponents_of_ne_zero {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK : Continuous K) (hx : K x ≠ 0) :
    localAdmissibleExponents K x = Set.Ici 0 := by
  ext c
  constructor
  · rintro ⟨hc, _⟩; exact hc
  · intro hc; exact mem_localAdmissibleExponents_of_ne_zero hK hx (Set.mem_Ici.1 hc)

/-- **The regular-point admissible set is unbounded** — no finite RLCT at a nonzero point.
`Set.Ici 0` has no upper bound in ℝ, so the honest local value is `+∞` (out of the ℝ `sSup`'s
scope); the ℝ-valued `rlctAt K x = sSup (Ici 0)` is the documented junk. -/
theorem not_bddAbove_localAdmissibleExponents_of_ne_zero {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK : Continuous K) (hx : K x ≠ 0) :
    ¬ BddAbove (localAdmissibleExponents K x) := by
  rw [localAdmissibleExponents_of_ne_zero hK hx]
  exact not_bddAbove_Ici (a := (0 : ℝ))

end RLCT
