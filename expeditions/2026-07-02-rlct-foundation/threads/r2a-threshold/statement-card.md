# Statement cards — R2a RLCT integrability-threshold substrate

The cite-free analytic foothill of the RLCT foundation: the definition-agnostic integrability
**threshold value** and its 1-D validation witness. Bare Mathlib-mirror namespace `RLCT`
(network-free; does not shadow `DLNFibre.Core.X`).

---

## Card 1 — the threshold value (definition)

> **Claim.** For a loss germ `K : (Fin n → ℝ) → ℝ` and a neighbourhood `U`, the RLCT integrability
> threshold is the supremum of the exponents `c ≥ 0` at which `K^(-c)` is Lebesgue-integrable on `U`.
>
> - **Lean:** `RLCT.integrabilityThreshold` (def) + `RLCT.admissibleExponents`
>   (`lean/DLNFibre/Core/Analysis/RLCT/{Integrability,Basic}.lean` @ `c06a6f54`)
> - **Gloss.** `admissibleExponents K U = {c : ℝ | 0 ≤ c ∧ IntegrableOn (fun x ↦ (K x)^(-c)) U}`;
>   `integrabilityThreshold K U = sSup (admissibleExponents K U)`, an `ℝ` value.
> - **Proved.** The objects are defined; `negPow_nonneg`, `measurable_negPow`,
>   `zero_mem_admissibleExponents` (0 admissible when `1` integrable on `U`).
> - **Assumed.** none (it is a definition).
> - **Cited.** none — axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
> - **Deferred.** The zeta-pole `(λ, m)` *definition* of "the RLCT" (with multiplicity `m`) — needs the
>   cited meromorphic continuation, deferred by design; this is the agnostic substrate it connects to.
>   The name is `integrabilityThreshold`, **not** `rlct`, exactly to not claim it IS the RLCT.
>   Honest only in the bounded/pole regime (`sSup` in `ℝ` is junk `0` if no pole / unbounded set) — a
>   documented scope, not a claim.
> - **Faithfulness (scope of the RLCT reading).** `integrabilityThreshold K U` equals the *classical*
>   RLCT integrability threshold precisely when `{x ∈ U | K x = 0}` is **null**: the ℝ-`negPow` collapses
>   the pole at `{K=0}` to `0` (`Real.zero_rpow`), so if that set had positive measure the value reads too
>   large (counterexample: `K = x` on `(0,1]`, `0` on `(1,2)` → ℝ-threshold `1` vs classical `0`). For the
>   DLN germ `K^{DLN}_B = ‖mult−B‖²` this **holds** — `{K_B = 0} = mult⁻¹(B)` is a proper subvariety, hence
>   null — so the reading is faithful where the payoff needs it. (Co-located per rev-r2a; the definition is
>   correctly general — this scopes its RLCT *interpretation*.)
> - **Status.** sorry-free

---

## Card 2 — the 1-D witness (validation, bedrock)

> **Claim.** The power germ `K(t) = |t|` at `0`, integrated over the one-sided coordinate
> neighbourhood `{x | x 0 ∈ Ioo 0 t}` (`t > 0`), has RLCT integrability threshold exactly `1` — the
> classical real log-canonical threshold of `|t|` (`∫₀ x^(-c)` finite iff `c < 1`).
>
> - **Lean:** `RLCT.integrabilityThreshold_absGerm`
>   (`lean/DLNFibre/Core/Analysis/RLCT/Integrability.lean` @ `c06a6f54`)
> - **Gloss.** `integrabilityThreshold_absGerm (t) (ht : 0 < t) : integrabilityThreshold absGerm
>   (witnessNbhd t) = 1`, where `absGerm x = |x 0|` and `witnessNbhd t = funUnique⁻¹'(Ioo 0 t)`.
>   Supporting: `admissibleExponents_absGerm : admissibleExponents absGerm (witnessNbhd t) = Ico 0 1`.
> - **Proved.** Unconditional (given `0 < t`). Route: the measure-preserving `MeasurableEquiv.funUnique
>   (Fin 1) ℝ` transports integrability to the 1-D `∫ over Ioo 0 t`
>   (`MeasurePreserving.integrableOn_comp_preimage`); `|x| = x` on `Ioo 0 t`
>   (`integrableOn_congr_fun`); the near-0 dichotomy `intervalIntegral.integrableOn_Ioo_rpow_iff`
>   gives admissible ⟺ `c < 1`; `csSup_Ico` gives `sSup (Ico 0 1) = 1`.
> - **Assumed.** `0 < t` (a genuine neighbourhood).
> - **Cited.** none — axiom-clean.
> - **Deferred.** none.
> - **Status.** sorry-free
>
> **Why this card matters (bedrock non-vacuity).** If the definition gave anything other than `1`, the
> formulation would be wrong. It gives `1`, the classical value — so the ℝ-`IntegrableOn` formulation
> (which, via `Real.zero_rpow`, sees the pole on `{K > 0}` but collapses it at `{K = 0}`) is faithful
> on non-degenerate germs. This is the validation the brief asked for.

---

## Card 3 — down-set + germ monotonicity (properties)

> **Claim.** The admissible set is a down-set (in `c`) for germs valued in `[0,1]`; and the threshold
> is monotone in the germ — a pointwise-larger germ (a milder singularity) has the larger threshold.
>
> - **Lean:** `RLCT.admissibleExponents_downward`, `RLCT.admissibleExponents_subset_of_le`,
>   `RLCT.integrabilityThreshold_mono` (`.../Integrability.lean` @ `c06a6f54`)
> - **Gloss.** `_downward`: `Measurable K`, `MeasurableSet U`, `0 ≤ K ≤ 1` on `U`, `1` integrable on
>   `U`, `c` admissible, `0 ≤ c' ≤ c` ⟹ `c'` admissible (domination `K^(-c') ≤ K^(-c)`).
>   `_subset_of_le`: `Measurable K'`, `MeasurableSet U`, `0 < K ≤ K'` on `U` ⟹ `admissibleExponents K U
>   ⊆ admissibleExponents K' U`. `_mono`: same + `admissibleExponents K U` nonempty + `BddAbove
>   (admissibleExponents K' U)` ⟹ `integrabilityThreshold K U ≤ integrabilityThreshold K' U`.
> - **Proved.** All three, unconditionally under the stated hypotheses (via `Integrable.mono'` +
>   `Real.rpow_le_rpow_of_exponent_ge` / `Real.rpow_le_rpow_of_nonpos`, and `csSup_le_csSup`).
> - **Assumed.** The measurability + range hypotheses above; for `_mono`, `BddAbove` (the pole regime —
>   the `name = content` guard: `sSup` in `ℝ` is the honest value only when the admissible set is
>   bounded) and nonemptiness. `_subset_of_le`/`_mono` are stated in the **strict-positive** (`0 < K`)
>   form: domination is a.e.-clean away from `K`'s zero set (where the ℝ-rpow collapse would break it).
> - **Cited.** none — axiom-clean.
> - **Deferred.** The a.e.-zero-set generalization (`{K=0}` null instead of `0 < K`) — a reachable but
>   not-attempted extension; the strict-positive form is what is proved and named.
> - **Status.** sorry-free

---

## Reviewer note (fidelity focus)

The one non-mechanical design decision — the **ℝ-`IntegrableOn` formulation** vs an `ℝ≥0∞` lintegral
— is the load-bearing fidelity question. The Codex definition-consult **hung** (exit 143 at stdin, as
R0 warned); the decision was made on the merits and Card 2's witness *validates* it (gives the
classical `1`). A decorrelated reviewer should confirm: (a) `admissibleExponents` faithfully captures
the local integrability of the negative power for a non-degenerate germ (the `Real.zero_rpow`-collapse
is null and the witness confirms the value), and (b) the `integrabilityThreshold` name/scope honestly
does NOT claim to be "the RLCT" (the zeta-pole `(λ,m)` object).
