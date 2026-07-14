# Review — head-split u≥1 CRUX (fidelity + soundness)

- **Target:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJPivotFin.lean`, branch `genm-sj5-step2` @ `e395121c`.
- **Function:** fidelity + claim-soundness (report-only for fidelity/precision).
- **Reviewer:** independent audit thread `genm-cruxreview`; decorrelated with Codex (xhigh).
- **Date:** 2026-07-14.

## Verdict

**PASS on the u≥1 crux** — `pivotPeel_domination` is sound, non-vacuous, faithful, and clean-three
(`[propext, Classical.choice, Quot.sound]`, forced `#print axioms` after a forced recompile). **One
load-bearing caveat** about the wiring target (finding 1) + two minor simplification items + one stale
cross-reference note.

## Method

Worked from a scratch worktree at `e395121c` (source byte-identical to the target). Force-recompiled the
crux module in isolation via a hardlink build (removing only my own hardlink names; the same-commit locked
worktree's oleans were verified untouched). Ran forced `#print axioms` on every target theorem and its
dependency path. Verified each step of the full-block route by hand, plus the verbatim stub reproduction
(byte-identical signature + `@pivotDom_finiteness = @pivotDom_finiteness_impl` type-match by `rfl`).
Decorrelated the mathematics with Codex — see `codex/full-block-soundness-{prompt,answer}.md`; it
corroborated every substantive point.

## Findings (ranked, most severe first)

### 1. CAVEAT (load-bearing) — `pivotDom_finiteness_impl` is NOT axiom-clean; sorry is only the out-of-scope u=0 edge

Forced `#print axioms pivotDom_finiteness_impl` = `[propext, sorryAx, Classical.choice, Quot.sound]`.
The `sorryAx` enters **only** via the out-of-scope u=0 edge:
`pivotDom_uzero` (still a `sorry` stub in `RouteMSJPivotDom.lean:109`) →
`pivotDom_finiteness_uzero` (`RouteMSJPivotFin.lean:1301`) →
the u=0 branch of `pivotDom_finiteness_impl` (`RouteMSJPivotFin.lean:1329`).

The u≥1 crux and the **entire u≥1 path** are clean-three, re-verified on the forced recompile:
`pivotPeel_domination`, `forward_LHS_finiteness`, `pivotDomLHS_lt_top_of_pos`,
`pivotDomLHS_lt_top_of_zero`, `pivotDomRHS_ne_zero_aux` (E), `pivotDomRHS_eq_top_of_critical` (B),
`vfibre_top`, `shell_fullBlock_le`, `frobSq_mul_ge_of_gramFloor`, `minAdm_add_peel_le`,
`matBox_frobSq_neg_lintegral_lt_top`.

**Consequence.** The "sorry-free + axiom-clean, clean-three" milestone headline is true of
`pivotPeel_domination`; it is **not yet** true of `pivotDom_finiteness_impl`. That theorem clears to
clean-three only after the u=0 edge is mooted (controller plan: u≥1 head-split `t★ ≥ 1`). Do not wire
`pivotDom_finiteness_impl` into (□) as axiom-clean before the moot lands. (Confirmed with the controller;
consistent with the stated scope.)

### 2. PASS — `pivotPeel_domination` faithfully encodes the head-split domination; the full-block route is sound

- **Fidelity.** Conclusion `∃ C < ⊤, pivotDomLHS ≤ C · pivotDomRHS` is defeq to `headSplit_pivotDom`'s
  conclusion; the crux uses the **imported** `pivotDomLHS` / `pivotDomRHS` / `pivotShell` / `hsQ` (no
  shadowing in the file). `pivotDom_finiteness_impl` reproduces the stub `pivotDom_finiteness` verbatim
  (byte-identical signature; `rfl` type-match).
- **`pivotShell` = `{A_cor | (hsQ·hsQᵀ − ε²·1).PosSemidef}`** (`RouteMSJHeadSplitDom.lean:63`), so
  `hA.2` supplies the Loewner floor directly to `shell_fullBlock_le`.
- **Loewner floor** (`frobSq_mul_ge_of_gramFloor`): `ε²·frobSq(B) ≤ frobSq(B·Q)` on `{Q·Qᵀ ⪰ ε²·1}` —
  correct linear algebra (per row `v` of `B`, `‖v·Q‖² = v·(Q·Qᵀ)·v ≥ ε²‖v‖²`; sum over rows; `Q·Qᵀ` is
  the correct Gram for right multiplication — Codex Q1).
- **Shell bound** (`shell_fullBlock_le`): the inner `(x, D)` block integral `≤ ε^{−2c'}·(pure block-box
  integral)`, finite for `c' < N/2`, `N = (u+a)(u+b)`, via `matBox_frobSq_neg_lintegral_lt_top`
  (banked `lintegral_box_sq_neg_lt_top`, `c' < r/2`). The outer `z` and `A_cor` **finite volumes are
  retained** in `pivotDomLHS_lt_top_of_pos` (multiplies `K` by `hmatvol · hparamsvol`,
  `RouteMSJPivotFin.lean:1165–1166`). (Codex Q2 flagged a missing-volume worry — an artifact of the
  prompt's compression, not the code; the code retains the factors.)
- **Threshold chain:** `RHS < ⊤` ⟹ (contrapositive of B) `2c' < minAdm + ab` ⟹ (`minAdm_add_peel_le`
  via `hpiv`) `minAdm + ab ≤ N` ⟹ `c' < N/2` ⟹ (full-block) `LHS < ⊤`; `c' = 0` via
  `pivotDomLHS_lt_top_of_zero`. Nat chain verified by hand (`tailMinWidth ≤ M 1 ≤ u+(M1−u)`).
- **Non-vacuity:** `RHS ≠ 0` (E, a genuine denominator for the ratio trick); hypotheses jointly
  satisfiable (e.g. `M = ![3,3,3]`, `u = 2`: `hpiv` holds tight `6 ≤ 6`, operative region `c' < 3.5`
  non-empty); `C` finite via the ratio trick; `ε > 0` load-bearing (Codex Q4); shell ⟹ `Q·Qᵀ` PD ⟹
  `rank Q = u+b`, `n ≥ u+b` automatic (no separate rank hypothesis; empty shell ⟹ `LHS = 0`, harmless —
  Codex Q5). `a = 0` / `b = 0` edges harmless.
- The "domination" is a **finiteness comparison** (ratio trick), honestly documented as such — the name
  mildly oversells but the docstring clarifies. No overclaim.

### 3. PASS — E (`pivotDomRHS_ne_zero_aux`), `hZfMeas` load-bearing-but-sound

Statement (`pivotDomRHS ≠ 0`) matches intent. `hZfMeas` is genuinely required for
`measurable_pivotRHS_integrand` (the `Zf`-dependent corank `frobSq`), feeding Tonelli `hFmeas` →
`setLIntegral_eq_zero_iff'`. It is not a vacuity dodge (measurability is a mild, satisfiable condition,
met by the downstream SVD frame). The call site (`RouteMSJPivotFin.lean:1254`) supplies it.
**Minor (simplification):** `hc0` is unused in E — drop.

### 4. PASS — B (`pivotDomRHS_eq_top_of_critical`), exponent arithmetic correct + critical regime reachable

`s = (m0−1) + ab − 2c' ≤ −1 ⟺ m0 + ab ≤ 2c'` (via `Nat.cast_sub` for `m0−1`; `m0 = minAdm ≥ 1` by
`one_le_minAdm_redChain`). Critical regime reachable/non-vacuous; divergence real (positive-measure
`{frobSq(prod z) > 0}` slab × `vfibre_top`; corner bound `corner_inner_ge` + `frobSq_corank_le` at
`ρ = v·√(P/Kp)`; the 1-D monomial diverges by `abs_rpow_lintegral_Ioo_eq_top`, `s ≤ −1`).
**Minor (simplification):** `hZfMeas` is unused in B (linter-flagged, `RouteMSJPivotFin.lean:1078`) — drop.

### 5. PRECISION cross-ref (not in the crux file) — stale "true threshold" note

`RouteMSJPivotDom.lean:22–31` calls the "true LHS threshold" `minAdm(M)/2` (`= 3.5` for `(3,3,3)`,
`u=2`) and warns that dropping the corank over-estimates. The shipped full-block route's finiteness
region `c' < N/2` (`= 4.5`) is a **valid, non-tight superset** covering the RHS-finite region `c' < 3.5`
— no contradiction, because on the **shell** the singularity is the N-dimensional full-block one
(threshold `N/2`), not `3.5` (Codex Q3). That note describes the old S3 / corank-peel analysis and is now
stale/misleading vs the shipped route; reconcile when folding in.

## Fold-in items logged with the controller (rendezvous pass)

1. Moot the u=0 edge (`pivotDom_uzero`) via u≥1 head-split `t★ ≥ 1` — clears finding 1.
2. Drop unused `hc0` from E and unused `hZfMeas` from B — findings 3, 4.
3. Reconcile the stale `RouteMSJPivotDom` header note — finding 5.
