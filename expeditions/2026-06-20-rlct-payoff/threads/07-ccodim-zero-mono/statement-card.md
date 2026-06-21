# Thread 07 — `cCodim·0` dimension-monotonicity (the θ-count discharge) — statement card

Module: `lean/DLNFibre/Core/CCodimZeroMono.lean` (~1560 LoC, sorry-free, axiom-clean).
Build: whole `DLNFibre` library green (`lake build`, 3017 jobs); `scripts/sorries` = 0.
Axioms (`#print axioms`): `[propext, Classical.choice, Quot.sound]` on `cCodim_zero_mono` and on the
discharged headline `numTop_eq_ncard_topComponents_of_strict`.
Pinned commit: `6bcd7da` (branch `expedition/rlct-payoff`).

## Goal

Prove the two combinatorial inequalities that discharge `hMono` / `hMonoStrict` of thread-06's reduced
headline `Core.CCodimCornerMono.numTop_eq_ncard_topComponents_of_dimMono`, making the θ-count headline
`θ = numTop d r = #{top-dim irreducible components of Σ̄^r}` UNCONDITIONAL:

> **`cCodim_zero_mono`** (weak): `(∀ v, e v ≤ e' v) ⟹ cCodim e 0 ≤ cCodim e' 0`.
> **`cCodim_zero_strict`** (strict, all-vertex): `(∀ v, e v < e' v) ⟹ cCodim e 0 < cCodim e' 0`.

Both are pure `CTheta`-level combinatorics over `ℤ` (no field, no geometry) — about the minimum of the
quadratic `codimForm` over the corner-`0` Kostant partitions. The module imports only
`Core.CThetaQIPConverse` (reusing its `codimBil` bilinear machinery) for the inequalities, and
`Core.CCodimCornerMono` for the final headline wiring.

## Status — LANDED: the weak inequality `cCodim_zero_mono`, and `hMono` discharged

### Construction (the shortest-interval split), fully formalised sorry-free

`codimForm` is the type-A `Ext`-pairing form; `codimBil` (from `CThetaQIPConverse`) is its bilinear
pairing. At an over-covered vertex `k`, the SHORTEST positive-multiplicity covering interval `[a,d']`
is split, omitting `k`. The split's `codimForm`-delta is `∑_Y m̄(Y) · coeff(Y)` over intervals `Y`,
and the crux **sign lemma** is that every `Y` with `coeff(Y) > 0` is a strictly-shorter covering
interval of `k` — absent when `[a,d']` is shortest, so the delta is `≤ 0`. Numerically certified
(813081/813081 weak; non-shortest splits increase in 513381 cases ⟹ "shortest" load-bearing).

LANDED Lean pieces (all sorry-free, axiom-clean):
- **Bilinear univ-sum collapse** (`codimBil_extendℤ_boxℤ_right`/`_left`, `rect_*_eq_univ`,
  `codimBil_boxℤ_boxℤ`): `codimBil` of `extendℤ m̄` against a single interval box, as a `univ`-sum over
  `Fin²` of `m̄(Y)` weighted by the rectangle indicators `rrInd`/`llInd` (clamped for reachability;
  valid for ALL box endpoints, including below-diagonal where the sum is `0`).
- **The four atomic moves**, each with `codimForm`-delta = `∑_Y m̄(Y)·coeff(Y)`, a sign lemma
  (`*Coeff_pos_imp`), a non-increase lemma (`codimForm_*_le`), a per-vertex coverage shift
  (`*_cover`), and a Kostant-validity lemma (`*_mem`, landing in the corner-`0` partitions of the
  vector decremented at the omitted vertex, corner preserved):
  - **`redMove`** — interior split `[a,d'] → [a,b] + [c,d']` (`c = b+2`, omits `k = b+1`);
  - **`leftShrink`** — `[a,d'] → [a+1,d']` (omits the left endpoint `a`; covers `a = 0` / singleton);
  - **`rightShrink`** — `[a,d'] → [a,d'−1]` (omits the right endpoint `d'`; covers `d' = N`);
  - **`removeMove`** — singleton removal `[a,a] → ∅` (omits `a`; coefficient ALWAYS `≤ 0`).
  The interior delta uses the gap `c = b+2` to kill the self-term (`codimForm_splitDelta = 0`); the
  guards/`codimForm_congr_onbox` make `codimForm` blind to below-diagonal increments.
- **`reduceStep`** — one step: at an over-covered vertex `k`, pick the shortest covering interval
  (`exists_shortest_covering`) and dispatch by `k`'s position in `[a,d']` (interior / left-endpoint /
  right-endpoint / singleton) to the matching move; lands a corner-`0` partition of `e'` decremented
  at `k` with `codimForm` no larger.
- **`exists_le_codimForm`** — the reduction recursion (strong induction on `∑ e'`): for `e ≤ e'` and
  any corner-`0` partition `m'` of `e'`, there is a corner-`0` partition `m` of `e` with
  `codimForm m ≤ codimForm m'`. Each step decrements `∑ e'` by `1` and does not increase `codimForm`.
- **`cCodim_zero_mono`** — assembles against the minimiser: `cCodim e 0 ≤ codimForm m ≤ codimForm
  m'_min = cCodim e' 0`. ✅ LANDED.
- **`numTop_eq_ncard_topComponents_of_strict`** (`[IsAlgClosed k] [CharZero k]`) — the θ-count
  headline with `hMono` discharged by `cCodim_zero_mono`; it now carries ONLY `hMonoStrict`.
  `hLowerBound` is thereby fully unconditional.

### The single remaining gap — `cCodim_zero_strict` (the strict all-vertex version)

> **`cCodim_zero_strict`**: `(∀ v, e v < e' v) ⟹ cCodim e 0 < cCodim e' 0`.

NOT proved in Lean; NOT sorry-patched. Numerically certified true (800/800; gap always `≥ 1`).
Status: the weak reduction gives a chain `m' ⤳ m` with `codimForm m ≤ codimForm m'`; STRICT needs SOME
step to strictly decrease (delta `< 0`). The delta `∑_Y m̄(Y)·coeff(Y)` is `< 0` iff some `Y` with
`m̄(Y) ≥ 1` has `coeff(Y) < 0`. Verified (this thread): a *single* shortest-split can be FLAT (e.g.
splitting the full interval `[0,N]` has no negative-coefficient `Y` at all); the strict drop is
configuration-dependent and does not localise to one obviously-identifiable step. A clean Lean route
(identify-the-strict-step, or a global counting invariant `cCodim e' ≥ cCodim e + 1`) was NOT found in
the time-box. Recommended next: a pen-and-paper certificate for the exact strict-step selection (or
the `+1`-step invariant `cCodim e 0 < cCodim (e+1) 0`, which combines with weak mono to give the
all-vertex strict via `e ≤ e+1 ≤ e'`).

NOTE (from thread 06, confirmed): strict *single-vertex* dimension-mono is FALSE (e.g. `cCodim [1,1,0]
0 = cCodim [1,2,0] 0 = 0`); only the strict ALL-vertex version holds.

## Non-vacuity (combinatorial, on `dev`)

`(2,2,2)`: `r=0 → cCodim=3, numTop=1`; `r=1 → cCodim=1, numTop=2` (`Core.CTheta`, decide-checked).
`(2,3,2)`: `r=0 → cCodim=4, numTop=2`; `r=1 → cCodim=1, numTop=1` (the `θ=2` (2,3,2) instance is at
`r=0`, matching synthesis line 76 — confirmed against thread-06's note).

## Decorrelation / verification

The construction was independently re-derived and certified by exhaustive numerical enumeration in
this thread (the codimForm = Ext-pairing form identity 2000/2000; the shortest-split delta-sign
813081/813081; the per-interval coefficient sign over all four move types 8645/8645; the end-to-end
`TotalDelta = ∑ m̄(Y)coeff(Y)` 40000/40000). The decorrelated pen-and-paper seat (`delta-cert`) was
dispatched but did not return within the thread; the numerics + the sorry-free Lean proof of the weak
inequality are the verification. A reviewer fidelity audit is requested (AUDIT gate).

## Summary

Weak `cCodim_zero_mono` LANDED sorry-free + axiom-clean; `hMono` discharged in the θ-count headline
(`numTop_eq_ncard_topComponents_of_strict`), making `hLowerBound` unconditional. The strict all-vertex
`cCodim_zero_strict` (⟹ `hMonoStrict`, ⟹ `hRecover`, ⟹ FULLY unconditional θ-count) is the precisely-
scoped remaining gap, characterised + numerically certified, NOT sorry-patched.
