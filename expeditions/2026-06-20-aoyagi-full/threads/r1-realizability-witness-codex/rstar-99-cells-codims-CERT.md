# #99 — non-leaf cells/codims: cap-class correctness CERT (pen-and-paper, decorrelated)

Adjudication of the redeploy truth-value: **does the #99 non-leaf cell/codim decomposition correctly
compute the rank-pattern read for general non-leaf `M` WITHOUT an endpoint-cap-class bug (an
intermediate-width pinch) in the per-cell `Mval`?**

All algebra exact (sympy `.rank()` over ℚ for the matrix reads; integer arithmetic for `Mval`/`Adm`; no
float). Adjudicated against the FROZEN #125 interface (`RouteMState.lean`/`RouteMValue.lean`,
`PivotWitness`/`codimsOf`/`routeM_value_eq`) + the route-(a) architecture
(`r1-realizability-feasibility-CERT.md`). Decorrelated codex consult under `codex/`.

## Verdict (one line)

**ACCEPT — the cap-class bug CANNOT land through the frozen #125 contract; the interface is
self-fencing.** Two independent reasons, both exact-verified: (1) the codim VALUE is `(Mval M₀ T_c).toNat`
and `Mval` is rank-free (no min/cap), so the pinch cannot enter the value once `T_c` is fixed; (2) the
codim is *certified* by `PivotWitness M₀ c = ⟨T_c, hAdm : T_c ∈ Adm M₀, hCodim : c = (Mval M₀ T_c).toNat⟩`,
and a pinch-corrupted `T_c` is ALWAYS non-admissible — so `hAdm` is unprovable and the bug cannot
typecheck. No kill-condition. One **producer-side guard** to record (below): rs-grind must read `T_c`
from the genuine all-widths rank (= the matrix rank), not the endpoint-only cap — but even if it slips,
Lean rejects it at `hAdm`.

## Frozen interface (decl-grounded, `RouteMState.lean` @ fm3)

- `PivotWitness M c` (`:287`): `⟨T : Fin L → ℕ, hAdm : T ∈ Adm M, hCodim : c = (Mval M T).toNat⟩` — the
  per-codim certificate **demands `T` admissible**.
- `minAdm_le_Mval_toNat` (`:295`): `minAdm M ≤ (Mval M T).toNat` for `T ∈ Adm M` — the (C≥) lower bound,
  driven entirely by admissibility.
- `routeM_value_eq` (`RouteMValue.lean:42`): the value `⨅ = ½·minAdm` from
  `hwit : ∀ i, ∀ c ∈ codimsOf i, PivotWitness M c` (C≥) + an achiever leaf `i₀` with `minAdm ∈ codimsOf i₀`
  (C=∃). `codimsOf : ι → List ℕ` is a bare codim-list; the witness carries the admissibility.
- `Mval M T = ∑_j (tPrev_j − T_j)(M_{j+1} − T_j)` (`Lambda.lean`), `tPrev_0 = M_0`, `tPrev_j = T_{j-1}`:
  a polynomial in `(M,T)` — **no `Matrix.rank`, no window-min, no cap**.

## The two candidate bug-sites (the decorrelated framing — codex isolated the same two)

- **Site 1 — the codim VALUE `Mval`.** Rank-free. The intermediate-width pinch is a property of a
  partial-identity PRODUCT rank; `Mval` takes no product and no rank. **Cannot pinch.** [FACT, structural;
  codex Q1-framing concurs: "isolate whether the suspect min/cap is inside `Mval` itself or only in the
  rank-profile→`T_c` read".]
- **Site 2 — the cell's `T_c` READ.** Route (a): `codim c := (Mval M₀ T_c).toNat` for a `T_c` the
  dispatcher reads off the cell's rank-drop profile (running ranks of a representative tuple). The pinch
  could enter IF `T_c` is computed via the WRONG endpoint-only cap. This is the only live site, and the
  finding below shows the frozen interface fences it.

## The exact facts (scripts `pp99_celldcodim.py`, `pp99_nonachiever_fast.py`)

The genuine running-rank read (the #121 result, re-confirmed): `t_j = rank` of the `(0,j)` prefix product
`= min( min_{0≤p<j} U_p , min_{0≤r≤j} M_r )` — window-min of the truncations `U`, capped by **all** widths
`M_0..M_j`. The buggy "pinched" read uses the endpoint-only cap `min( window-min U, min(M_0, M_j) )`.

1. **PART 2 (sympy exact, interior-pinch `M`):** the genuine prefix matrix ranks equal the all-widths
   formula on every interior-pinch `M` tested (903 cases, 0 mismatches). So the all-widths formula IS the
   true matrix read; the endpoint cap is the bug.

2. **The genuine read is ALWAYS monotone** (rank drops along products: `rank(AB) ≤ min(rank A, rank B)`).
   Verified: over all `(M,U)` (L=2..4, widths 1..4), 0 non-monotone genuine prefix-rank profiles.

3. **(C≥) integrity under the genuine read — never undershoots:** over 673600 `(M non-leaf, arbitrary
   cell profile U)`, the genuine all-widths `T_c` yields `Mval(M₀, T_c) < minAdm` in **0** cases. (When the
   genuine `T_c` fails admissibility it is ONLY by `t_L ≠ 0` — the deepest rank not reaching 0; that is the
   non-achiever / non-terminal cell, handled by the dispatcher picking the achiever-resolving cell, not a
   codim error.) Structural pin (`pp99_celldcodim.py` analysis): a genuine (monotone, width-capped,
   `t_0=M_0`) read is admissible **iff** `t_L = 0`; the only failure mode is the last-entry-nonzero
   (5136/15956), never a bound violation.

4. **The pinch is self-fencing (the decisive finding):** over all `(M,U)`,
   - **0 silent-wrong codims** — whenever the pinched `T_c` is admissible, it EQUALS the genuine `T_c`
     (375264 admissible-pinch cases, 0 divergences). The pinch can never emit a *valid-but-wrong* codim.
   - **every divergent pinched `T_c` is NON-admissible** — all 73189 cases where pinched ≠ genuine have
     `admPred(M, T_c_pinch) = False` (the pinch produces a NON-MONOTONE `T_c`, e.g. `M=(2,1,2,1), U=(2,2,0)`:
     genuine `T_c=(1,1,0)` admissible codim 1; pinched `T_c=(1,2,0)` non-monotone, NOT in `Adm`).

⟹ Since `PivotWitness M₀ c` requires `hAdm : T_c ∈ Adm M₀`, a pinch-corrupted `T_c` **cannot inhabit
`PivotWitness`**: `hAdm` is unprovable (the committed `decide`-instance for `admPred` returns `False`).
The frozen interface STRUCTURALLY REJECTS the cap-class bug — it can never reach a green build.

## Anchors reproduce (fidelity, `pp99_celldcodim.py` §D)

`(2,2,2)` achiever `T*=(1,0)`, exact prefix ranks `t=(2,1,0)`, `Mval=3=minAdm` (the `codimsOf222=[4,3]`
anchor, `Case222RouteStep.lean`); `(3,2,3)` `T*=(1,0)` `t=(3,1,0)` `Mval=5=minAdm` (matches the
`RouteMValue` docstring `codimsOf=[6,5]` for the chain, BOTH root `Mval(3,2,3) T`); `(4,3,2)` `T*=(2,0)`
`t=(4,2,0)` `Mval=6=minAdm`; `(3,3,3,3)` `T*=(2,1,0)` `t=(3,2,1,0)` `Mval=6=minAdm`. All exact.

## Where the genuine vs pinched read agree (the #121 link)

On the ACHIEVER (and any admissible `T`), genuine = pinched (admissibility kills the cap — the #121
result: `admPred ⟹ ρ weakly-decreasing ⟹` window-min = endpoint, AND `ρ_j ≤` every width). So the bug is
invisible on the achiever and on every admissible profile; it only shows on NON-admissible cell profiles,
which is exactly where `PivotWitness.hAdm` blocks it. The #99 and #121 cap-corrections are the same
bug-family, and the #99 codim layer inherits the fence from the admissibility requirement.

## Producer-side guard (for rs-grind — record, not a blocker)

The interface fences the bug at `hAdm`, but a cleaner producer avoids ever constructing a bad `T_c`:

- **Read `T_c` from the genuine all-widths rank** `t_j = min(min_{0≤p<j} U_p, min_{0≤r≤j} M_r)`, i.e. the
  actual `Matrix.rank` of the `(0,j)` prefix (Core's `rankPattern_cascade_prefix` already computes this:
  `survivors (d_j)(d_0)(cascadeCount 0 j)` with `cascadeCount` the running window-min capped at `d_0`).
  Do NOT hand-roll the endpoint-only `min(M_0, M_j)` cap.
- Equivalently, pick `T_c` admissible-by-construction (the achiever `T*` for the binding cell; a monotone
  width-capped profile with `t_L=0` for the others). Then `PivotWitness` is immediate and the pinch is
  structurally absent (route (a) self-certifying — codex Q3-framing: the codim is guaranteed correct by the
  definition `codim := Mval M₀ T_c`, the rank read only chooses WHICH admissible `T_c`).
- The Core decl to consume for the read is `rankPattern_cascade_prefix` (the `(0,j)` row) /
  `rankPattern_cascade` (#122, interior `i`), NOT a fresh endpoint-cap formula — these compute the genuine
  all-widths survivors count and are pinch-free by construction.

## Decorrelated codex (`codex/codex99_prompt.md`, `codex/codex99_answer.md`)

Hypothesis withheld (frame + facts + sub-question, no conclusion). Codex independently isolated the SAME
two sites ("whether the suspect min/cap operation is inside `Mval` itself or only in the rank-profile-to-
`T_c` read") and independently confirmed the ACHIEVER invariant ("admissibility makes the cap inactive on
every window, so the endpoint-only formula and the all-width formula agree there"). Its sandbox blocked
its own code run before it could print final verdicts, so the verdicts here ride my exact computation; the
decorrelation value is the independent two-site framing + the achiever invariant, both matching.

## Most likely thing to break this verdict / next step

The verdict is about the CODIM layer (Site 1+2), and is robust: the codim is rank-free and the witness
demands admissibility. What it does NOT cover — and what the #99 grind's real residual is — is the
GEOMETRIC fidelity that the emitted `codim = Mval M₀ T_c` is the ACTUAL exceptional-divisor codim of the
cell's blow-up (the per-cell `hnode` Schur presentation, `r1-realizability-feasibility-CERT.md` §5). That
is an analytic-chart obligation, NOT a cap-class combinatorial bug, and is out of this adjudication's
scope. The single highest-value next decorrelated step there remains the general-M `hnode` cert at a
C5/mixed node (the `t=(3,3,2,2,2,0)` witness) — flagged in the feasibility cert, not re-opened here.

## Scripts (this dir) — exact, re-runnable

- `pp99_celldcodim.py` — Site-1 rank-free check; achiever genuine-vs-pinch (0 divergence); anchors.
- `pp99_nonachiever_fast.py` — (C≥) integrity (0 undershoot); self-fencing (divergent pinch ⟹
  non-admissible, 73189/73189); PART-2 sympy exact (genuine read = all-widths, 903 cases).
- `codex/codex99_prompt.md`, `codex/codex99_answer.md` — decorrelated consult.
