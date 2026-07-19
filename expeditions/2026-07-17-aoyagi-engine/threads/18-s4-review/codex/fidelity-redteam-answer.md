### 1. STATEMENT FIDELITY / VACUITY — PASS

Verified: `leafOfState.numDiv` is the length of `t0Indices`, the filtered list of full-ledger divisors with `divTilde = 0`; every emitted terminal leaf is such a `leafOfState`. Thus `k : Fin l.numDiv` selects an actual analytic divisor, not an ambient profile.

The claim is non-vacuous: when `numDiv = 0`, `Fin l.numDiv` is empty, so no witness exists. Nothing forces `divProfile` to contain every profile.

### 2. HYPOTHESIS TIGHTNESS — NATURALLY SHARP

`0 < widthMinUpto M L` is equivalent to `∀ i, 0 < M i`; it is a reformulation, not a weakening. The supplied `![2,2,0]` counterexample decisively refutes positivity of only `M 0,…,M (L−1)`: the output width is load-bearing.

Therefore all-width positivity is the sharp natural uniform running-min condition. Strict logical minimality among arbitrary predicates is not established—one could potentially add isolated zero-width cases where realization happens—but no strictly weaker prefix-positivity condition supports the stated uniform theorem.

### 3. LOWCOVER PULL-BRICK — PASS

Verified from the implemented branch: if `cleared < a^layer`, LowCover supplies a divisor at level `cleared+1`. Anchor liveness and

`cleared < a^layer < target < widthMinUpto M layer`

make that level eligible. Since `target` is the minimum eligible occupied level, `target ≤ cleared+1`; but the selected anchor has `target > a^layer > cleared`, giving the contradiction. Hence `cleared = a^layer`.

No componentwise domination lemma is needed for this numerical conclusion. `step1_dominates` may remain relevant upstream for chain invariants/chooser correctness, but not for the pull-brick itself.

### 4. HIDDEN OVERCLAIM / DOWNSTREAM — HIGH RISK

The theorem is minimizer-only and must not be paraphrased as `realizedProfiles ⊇ Adm`.

Verified mismatch in the checkout: `EngineObligations.o5_realization`, `monomialization_terminates`, and `resolutionOf` remain width-free and call the old width-free `o5_core`. They must acquire `hMpos`, or callers must derive it.

Moreover, the width-free `realizedProfiles_eq_clearableAdm` forecast is also contradicted by `![2,2,0]`: `(2,0)` is Clearable by its definition but is not realized. That statement likewise needs positivity or a revised predicate.