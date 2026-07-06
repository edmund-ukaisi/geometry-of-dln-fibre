# Statement card — R9 RLCT-foundation layer-completion (validation set)

The RLCT foundation, **validated not just defined**: the regular-point structure lemma, the global
witness value, the fork-closing bridge, the local monotonicity API, the power rule, and the
cite/cite-free coherence on the concrete witness germ. Six sorry-free modules; the two on-cite
corollaries carry exactly `cited_local_zeta_pole` (+ std-3), everything else is std-3 only.

All files at `lean/DLNFibre/Core/Analysis/RLCT/` @ `c4110342`.

## A1 — the regular-point lemma (cite-free)

> **Claim.** For `K : (Fin n → ℝ) → ℝ` continuous, `K x ≠ 0`, the locally-admissible exponents at
> `x` are exactly `[0, ∞)`: no pole at a regular point.
>
> - **Lean:** `RLCT.localAdmissibleExponents_of_ne_zero`  (`RegularPoint.lean`)
> - **Gloss.** `Continuous K → K x ≠ 0 → localAdmissibleExponents K x = Set.Ici 0`. Companion
>   `RLCT.not_bddAbove_localAdmissibleExponents_of_ne_zero`: same hypotheses ⟹
>   `¬ BddAbove (localAdmissibleExponents K x)` (honest local value `+∞`, ℝ-`sSup` junk).
> - **Proved.** Unconditional. `negPow K c` is continuous on the open `{K ≠ 0} ∋ x`
>   (`Real.continuousAt_rpow_const`, `K y ≠ 0` branch — no sign condition on `c`), hence
>   `LocallyIntegrableOn` there (`ContinuousOn.locallyIntegrableOn`), so `IntegrableAtFilter (𝓝 x)`
>   (open ⟹ `𝓝[V] x = 𝓝 x`) for every `c ≥ 0`. `0 ≤ K` is **not needed** (the `K y ≠ 0` branch of
>   rpow-continuity covers it). `#print axioms = [propext, Classical.choice, Quot.sound]`.
> - **Assumed.** `Continuous K`, `K x ≠ 0`. Both load-bearing, carried in the statement.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free (awaiting fidelity review).

## A — the `rlctGlobal` validation witness (cite-free)

> **Claim.** For `C ≥ 1`, the polymorphic global RLCT of the sum-of-squares kernel is `C/2`.
>
> - **Lean:** `RLCT.rlctGlobal_sumSq`  (`GlobalWitness.lean`)
> - **Gloss.** `1 ≤ C → RLCT.Global.rlctGlobal (sumSq C) = (C : ℝ) / 2`. Supporting
>   `RLCT.globalAdmissibleExponents_sumSq`: `RLCT.Global.globalAdmissibleExponents (sumSq C) =
>   Set.Ico 0 (C/2)`.
> - **Proved.** Unconditional (modulo `1 ≤ C`). The global admissible set is `Ico 0 (C/2)`: at `0`
>   the origin's pole caps it (`mem_localAdmissibleExponents_sumSq`, R7); at every `x ≠ 0` the germ
>   is regular (`sumSq C x ≠ 0`, `continuous_sumSq`) so A1 imposes no constraint. `csSup_Ico` reads
>   off `C/2`. Non-vacuously exercises `RLCT.Global` (the value matches the local `rlctAt_sumSq` — the
>   Prop 8.3(iii) inf-over-zeros shape, single zero at `0`). `#print axioms = std-3`.
> - **Assumed.** `1 ≤ C` (carried).
> - **Cited.** none (rides R7's `mem_localAdmissibleExponents_sumSq` + A1, both cite-free).
> - **Deferred.** none.
> - **Status.** sorry-free (awaiting fidelity review).

## B1 — the fork-closing bridge (cite-free)

> **Claim.** The polymorphic global-side `rlctAt`, specialised to `Fin n → ℝ`, IS the zeta-side
> `rlctAt`.
>
> - **Lean:** `RLCT.global_rlctAt_eq`  (`GlobalBridge.lean`)
> - **Gloss.** `RLCT.Global.rlctAt K x = RLCT.rlctAt K x` (`K : (Fin n → ℝ) → ℝ`). By `rfl` — the two
>   `negPow`/`localAdmissibleExponents`/`sSup` are term-identical (`global_negPow_eq`,
>   `global_localAdmissibleExponents_eq` also `rfl`).
> - **Proved.** Definitional. `#print axioms = std-3`. Closes the "two `rlctAt`s" fork; used by A to
>   apply the zeta-side `mem_localAdmissibleExponents_sumSq` under the global-side admissible set.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free (awaiting fidelity review).

## B2 — local API parity: down-set + germ-monotonicity (cite-free)

> **Claim.** `localAdmissibleExponents K x` is a down-set (under a germ bound `0 ≤ K ≤ 1` near `x`),
> and is monotone in the germ (under `K ≤ K'` near `x`, `K` positive there).
>
> - **Lean:** `RLCT.localAdmissibleExponents_downward`, `RLCT.localAdmissibleExponents_subset_of_le`
>   (`LocalMono.lean`)
> - **Gloss.** Down-set: `Measurable K → (∀ᶠ y in 𝓝 x, 0 ≤ K y ∧ K y ≤ 1) →
>   c ∈ localAdmissibleExponents K x → 0 ≤ c' → c' ≤ c → c' ∈ localAdmissibleExponents K x`.
>   Germ-mono: `Measurable K' → (∀ᶠ y in 𝓝 x, 0 < K y ∧ K y ≤ K' y) →
>   localAdmissibleExponents K x ⊆ localAdmissibleExponents K' x`.
> - **Proved.** The local analogues of the regional `admissibleExponents_downward` /
>   `_subset_of_le` (`Integrability.lean`), through `IntegrableAtFilter`: shrink a witnessing nbhd to
>   an **open** (measurable) one, intersect with the open germ-bound region, dominate by
>   `Integrable.mono'` (`ae_restrict_of_forall_mem` on the open intersection). `#print axioms = std-3`.
> - **Assumed.** The germ bounds are stated as **filter-eventual** hypotheses (`∀ᶠ y in 𝓝 x, …`) —
>   the honest minimal germ-level form of the regional pointwise bounds; disclosed, carried in each
>   statement. `Measurable K`/`K'` for the dominated function's strong measurability. This is a
>   *widening* of scope vs. the dispatch's "`{K ≤ 1}`/`{K > 1}` split": the eventual form is cleaner
>   and strictly more general (holds automatically for a continuous germ with a zero at `x`).
> - **Cited / Deferred.** none.
> - **Status.** sorry-free (awaiting fidelity review).

## B4 — the power rule (cite-free)

> **Claim.** Raising a nonnegative germ to a natural power `k ≥ 1` scales the local RLCT by `1/k`.
>
> - **Lean:** `RLCT.rlctAt_powGerm`  (`PowerRule.lean`)
> - **Gloss.** `(∀ x, 0 ≤ K x) → 1 ≤ k → rlctAt (powGerm K k) x₀ = rlctAt K x₀ / k`, where
>   `powGerm K k = fun x ↦ (K x)^k`. Supporting: `negPow_powGerm` (the germ identity
>   `negPow (K^k) c = negPow K (k·c)` on `0 ≤ K`), `mem_localAdmissibleExponents_powGerm` (transfer
>   `c ∈ … (K^k) ↔ k·c ∈ … K`), `localAdmissibleExponents_powGerm` (admissible set `= (1/k) •` base).
> - **Proved.** **General `k ≥ 1`** (not only `k = 2`). The germ identity is `Real.rpow_natCast` +
>   `Real.rpow_mul` (needs `0 ≤ K`); the admissible set scales by the bijection `c ↦ k·c`; the `sSup`
>   scales by `Real.sSup_smul_of_nonneg`. **No `BddAbove` hypothesis** — the `sSup` scaling holds for
>   any set (junk-`0` scales coherently, `(1/k)·0 = 0`), so the identity is exact in both the pole and
>   the regular/junk regime. DLN case `k = 2` is the specialisation. `#print axioms = std-3`.
> - **Assumed.** `0 ≤ K` pointwise, `1 ≤ k`. Both carried; `0 ≤ K` is load-bearing for the rpow
>   collapse.
> - **Cited / Deferred.** none. (General `k` landed; no scope hypothesis was needed beyond `0 ≤ K`.)
> - **Status.** sorry-free (awaiting fidelity review).

## B5 — on-cite positivity (CITED)

> **Claim.** From any `ZetaSetup S`, the local RLCT at the base point is strictly positive.
>
> - **Lean:** `RLCT.rlctAt_pos_of_zetaSetup`  (`CiteCoherence.lean`)
> - **Gloss.** `(S : ZetaSetup n) → 0 < rlctAt S.K S.x₀`. From `largestPole_neg` (`s₀ < 0`) +
>   `largestPole_eq_neg_rlctAt` (`s₀ = −rlctAt K x₀`).
> - **Proved.** Standalone corollary. `#print axioms = std-3 + RLCT.cited_local_zeta_pole` — carries
>   **exactly** the one located, `@[cited]` continuation axiom, nothing else. This is correct and
>   honest: it *is* a statement about the cited pole. **Off the DLN payoff's value path** (the payoff
>   rides the two DLN Watanabe/Aoyagi cites on `rlctGlobal`, never this local zeta axiom).
> - **Assumed.** none beyond `ZetaSetup`'s bundled hypotheses.
> - **Cited.** `cited_local_zeta_pole` (the local zeta-pole monument).
> - **Deferred.** none.
> - **Status.** sorry-free (awaiting fidelity review).

## Coherence check — cited pole = cite-free canonical value on the witness germ

> **Claim (i, cite-free).** The witness germ `K = (x 0)²` has canonical local RLCT `1/2` at `0`.
> **Claim (ii, CITED).** The cited zeta-pole location `λ` on that germ also equals `1/2` (Link 1).
>
> - **Lean:** `RLCT.rlctAt_zetaSetupSq` (i), `RLCT.rlctPair_lam_zetaSetupSq` (ii)  (`CiteCoherence.lean`)
> - **Gloss.** (i) `rlctAt zetaSetupSq.K zetaSetupSq.x₀ = 1/2`, via `zetaSetupSq_K_eq_sumSq`
>   (`zetaSetupSq.K = sumSq 1`, the `Fin 1` sum collapsing) + `zetaSetupSq_x₀_eq_zero` +
>   `rlctAt_sumSq` at `C = 1`. (ii) `(rlctPair zetaSetupSq).lam = 1/2`, via Link 1
>   `rlctPair_lam_eq_rlctAt` + (i).
> - **Proved.** (i) `#print axioms = std-3` (cite-free — rides R7 `SumSq`). (ii) `#print axioms =
>   std-3 + RLCT.cited_local_zeta_pole` (via Link 1). Together: the **cited** pole location and the
>   **cite-free** canonical value **agree** on the one concrete germ — Link 1 validated non-vacuously.
> - **Assumed.** none beyond the fixed witness `zetaSetupSq`.
> - **Cited.** (i) none; (ii) `cited_local_zeta_pole`.
> - **Deferred.** none.
> - **Status.** sorry-free (awaiting fidelity review).

## Gates

- `scripts/sorries`: 0 sorry / 0 #exit / 0 native_decide across the library (the 3 axioms are the
  pre-existing declared cites: `cited_local_zeta_pole`, `cited_watanabe_upper_ax`,
  `cited_aoyagi_lower_ax`).
- Each new module builds by name via `scripts/lb`; all six build together clean (no warnings).
- Cordon: authoritative per-theorem status by `#print axioms` above — cite-free items std-3; the two
  on-cite corollaries carry exactly `cited_local_zeta_pole`.

## Wiring note (for the controller — single-writer aggregator)

Add at the end of `DLNFibre.lean`'s RLCT block (dependency order):

    import DLNFibre.Core.Analysis.RLCT.RegularPoint
    import DLNFibre.Core.Analysis.RLCT.GlobalBridge
    import DLNFibre.Core.Analysis.RLCT.GlobalWitness   -- needs SumSq, RegularPoint, GlobalBridge
    import DLNFibre.Core.Analysis.RLCT.LocalMono
    import DLNFibre.Core.Analysis.RLCT.PowerRule
    import DLNFibre.Core.Analysis.RLCT.CiteCoherence   -- needs Pair, Witness, SumSq (CITED items)

`GlobalWitness` imports `SumSq` + `RegularPoint` + `GlobalBridge`; `CiteCoherence` imports `Pair` +
`Witness` + `SumSq`. All of `SumSq`, `Pair`, `Witness` are already in the aggregator.
