import DLNFibre.Core.Analysis.RLCT.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# `RLCT.Local` — the cite-free **local** RLCT `rlctAt K x` (germ threshold at a point)

The **local** integrability threshold of a loss germ `K` at a single point `x`:

`rlctAt K x := sSup { c ≥ 0 | K^(-c) is locally integrable at x }`,

where "locally integrable at `x`" is `IntegrableAtFilter (negPow K c) (𝓝 x)` — integrable on *some*
neighbourhood of `x`. This is the paper's local `rlct_x(F)` (Def 8.1(ii), `main.tex` L1787/L1796), a
**cite-free, local** notion, distinct from R2a's **regional** `integrabilityThreshold K U` (a
threshold on a fixed region `U`, `RLCT.Integrability`):

* `rlctAt K x` reads the *germ* at `x` — quantifies over all neighbourhoods (`∃ s ∈ 𝓝 x`);
* `integrabilityThreshold K U` reads a *fixed region* `U`.

The two are connected by **Bridge B** (`integrabilityThreshold_eq_localRlct_of_worst`) under a
boundary-regular `U` and a worst-point hypothesis — a separate, buildable regional lemma, **not** a
cite. Their split is the fix for the altitude confusion that made the *regional* zeta-pole cite
inconsistent (certificate §7): the zeta-pole cite (`RLCT.Cited`) is now stated **locally**
(`s₀ = −rlctAt K x₀`), and is DLN-admissible — a local identity cannot be broken by a far-away zero,
and it is defined even when the zero set `{K = 0}` is non-isolated (the connected DLN fibre).

Where `K x ≠ 0` the germ has no pole and `rlctAt K x = 0` is not claimed (the admissible set is
unbounded / the honest value is `+∞`, out of the `ℝ` `sSup`'s bounded scope, as for
`integrabilityThreshold`); the pole regime (`K x = 0`, `BddAbove`) is where the value is
meaningful — the same `name = content` scope note as R2a.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology

namespace RLCT

variable {n : ℕ}

/-- An exponent `c` is **locally admissible** for the germ `K` at the point `x` when `c ≥ 0` and the
negative power `K^(-c)` is integrable on *some* neighbourhood of `x` (`IntegrableAtFilter … (𝓝 x)`).
The **local** analogue of `admissibleExponents` (`RLCT.Basic`), reading the germ at a point rather
than a fixed region. -/
def localAdmissibleExponents (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}

lemma mem_localAdmissibleExponents {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {c : ℝ} :
    c ∈ localAdmissibleExponents K x ↔ 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x) := Iff.rfl

/-- The **local RLCT** `rlctAt K x`: the supremum of the locally-admissible exponents at `x` — the
paper's `rlct_x(K)` (Def 8.1(ii)). Cite-free, local; the value the zeta-pole cite identifies with
the largest pole (`s₀ = −rlctAt K x₀`, `RLCT.Cited`). Honest in the pole regime (bounded admissible
set); `sSup ∅ = 0` / unbounded is the documented out-of-scope, as for `integrabilityThreshold`. -/
noncomputable def rlctAt (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (localAdmissibleExponents K x)

lemma rlctAt_def (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    rlctAt K x = sSup (localAdmissibleExponents K x) := rfl

/-- `0` is locally admissible at `x`: `K^0 = 1` is integrable on any neighbourhood of finite measure
(a small ball around `x`), so the local admissible set is nonempty. Witness that the local threshold
is `≥ 0` in the pole regime. -/
lemma zero_mem_localAdmissibleExponents {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : IntegrableAtFilter (fun _ ↦ (1 : ℝ)) (𝓝 x)) :
    (0 : ℝ) ∈ localAdmissibleExponents K x := by
  refine ⟨le_rfl, ?_⟩
  simpa [negPow_zero] using h

end RLCT
