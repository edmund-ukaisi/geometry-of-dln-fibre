import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Analysis.RLCT.Integrability

/-!
# `RLCT.Bridge` — Bridge B: regional `integrabilityThreshold` = local `rlctAt` at a worst point

**Bridge B** (certificate §7.2/§7.5) connects the two RLCT notions in the foundation:

* the **regional** threshold `integrabilityThreshold K U` (R2a, `RLCT.Integrability`) — a `sSup`
  over a fixed region `U`;
* the **local** RLCT `rlctAt K x₀` (`RLCT.Local`) — the germ threshold at one point.

**Claim (Bridge B).** If `x₀` is a *worst singularity* on `closure U` (`∀ x ∈ closure U,
rlctAt K x₀ ≤ rlctAt K x` — no point has a *sharper* local threshold), then the regional threshold
equals the local one at `x₀`: `integrabilityThreshold K U = rlctAt K x₀`.

This is **buildable analysis, NOT a cite** — it is the honest regional↔local tie the earlier
(inconsistent) *regional* zeta-pole cite tried to bundle. The correct architecture (certificate §7)
keeps the zeta-pole cite **local** (`RLCT.Cited`, `s₀ = −rlctAt K x₀`) and factors this regional
statement out here. The worst-point hypothesis **admits a connected fibre** (equal-threshold zeros
are fine) and forbids only a *strictly worse-threshold* zero — unlike the discarded sole-zero
condition, which excluded the DLN fibre.

**Status of the analytic core (certificate §7.1, (F1)+(F2)).** The equality rests on two
integrability facts about a **boundary-regular** `U` (a ball/box), taken here as explicit hypotheses
and **not** `sorry`-ed:

* **(F1-easy), `hSubThreshold`** — *sub-threshold everywhere ⟹ regionally integrable*: if `c` is
  below the local threshold at every point of `closure U`, then `K^(-c)` is integrable on `U` (a
  finite-subcover / compactness argument — always true, no regularity needed).
* **(F1-converse), `hIntegrableCap`** — *regionally integrable ⟹ capped by the worst local
  threshold*: if `K^(-c)` is integrable on `U`, then `c ≤ rlctAt K x₀` (needs `U` **thick** near
  `∂U`: for a cusped `U` the integral can converge while a boundary point has a smaller local
  threshold — certificate §7.1 counterexample `K = x²+y²`, `U = {0<x<1, 0<y<e^{−1/x²}}`; a ball/box
  avoids the pathology).

Given these two facts (the roadmapped lift), Bridge B is a clean order-theoretic assembly
(`csSup` antisymmetry), proved below **sorry-free**. Discharging `hSubThreshold` / `hIntegrableCap`
for a concrete ball/box `U` (from local integrability + compactness of `closure U` + boundary
regularity) is the remaining analysis — **roadmapped**, tractable, not attempted here (a focused
real-analysis rung). The 1-D `|t|` witness (`RLCT.Integrability.integrabilityThreshold_absGerm`)
already validates the *value* the bridge lands on.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set

namespace RLCT

variable {n : ℕ}

/-- **Bridge B — `integrabilityThreshold_eq_localRlct_of_worst` (buildable analysis, NOT a cite).**
If `x₀` is a worst singularity on `closure U` (`hworst`: no point has a strictly sharper local
threshold), then the regional threshold on `U` equals the local RLCT at `x₀`. The two integrability
facts `hSubThreshold` (F1-easy) and `hIntegrableCap` (F1-converse, needs boundary-regular `U`) are
the roadmapped analytic core (see the module docstring); given them, the equality is `csSup`
antisymmetry.

* `hworst` — `∀ x ∈ closure U, K x = 0 → rlctAt K x₀ ≤ rlctAt K x` (worst-point among the **zeros**;
  admits a connected fibre). Guarded to `K x = 0` for the same reason as Axiom A's `hWorst`: regular
  points have `rlctAt = 0` junk, so an unguarded `≤` is unsatisfiable at a real zero (`RLCT.Cited`).
* `hSubThreshold` — sub-threshold at every zero of `closure U` makes `c ≥ 0` regionally admissible.
  Its premise is likewise guarded to zeros (regular points carry no obstruction to integrability).
* `hIntegrableCap` — `∀ c ∈ admissibleExponents K U, c ≤ rlctAt K x₀`.
* `hbdd` — `BddAbove (admissibleExponents K U)` (pole regime; the regional `sSup` is honest).
* `h0mem` — `(0 : ℝ) ∈ admissibleExponents K U` (`0` regionally admissible: `K^0 = 1` integrable on
  finite-measure `U`, `RLCT.zero_mem_admissibleExponents`) — pins `0 ≤ sSup`, handling `c < 0`. -/
theorem integrabilityThreshold_eq_localRlct_of_worst {K : (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (hworst : ∀ x ∈ closure U, K x = 0 → rlctAt K x₀ ≤ rlctAt K x)
    (hSubThreshold : ∀ c : ℝ, 0 ≤ c → (∀ x ∈ closure U, K x = 0 → c < rlctAt K x) →
      c ∈ admissibleExponents K U)
    (hIntegrableCap : ∀ c ∈ admissibleExponents K U, c ≤ rlctAt K x₀)
    (hbdd : BddAbove (admissibleExponents K U))
    (h0mem : (0 : ℝ) ∈ admissibleExponents K U) :
    integrabilityThreshold K U = rlctAt K x₀ := by
  rw [integrabilityThreshold_def]
  refine le_antisymm ?_ ?_
  · -- `sSup (admissibleExponents K U) ≤ rlctAt K x₀`: `rlctAt K x₀` bounds the regional admissible.
    exact csSup_le ⟨0, h0mem⟩ hIntegrableCap
  · -- `rlctAt K x₀ ≤ sSup (…)`: every `c < rlctAt K x₀` is `< sSup`; conclude by density.
    refine le_of_forall_lt (fun c hc ↦ ?_)
    rcases lt_or_ge c 0 with hcneg | hc0
    · -- `c < 0`: `0` is admissible, so `0 ≤ sSup`, hence `c < 0 ≤ sSup`.
      exact lt_of_lt_of_le hcneg (le_csSup hbdd h0mem)
    · -- `0 ≤ c < rlctAt K x₀`: pick `c'` strictly between; at each ZERO `x ∈ closure U`,
      -- `c' < rlctAt K x₀ ≤ rlctAt K x` (`hworst`), so the zero-guarded `hSubThreshold` makes `c'`
      -- admissible, giving `c < c' ≤ sSup`.
      obtain ⟨c', hcc', hc'r⟩ := exists_between hc
      have hc'0 : 0 ≤ c' := le_of_lt (lt_of_le_of_lt hc0 hcc')
      have hc'mem : c' ∈ admissibleExponents K U :=
        hSubThreshold c' hc'0 (fun x hx hKx ↦ lt_of_lt_of_le hc'r (hworst x hx hKx))
      exact lt_of_lt_of_le hcc' (le_csSup hbdd hc'mem)

end RLCT
