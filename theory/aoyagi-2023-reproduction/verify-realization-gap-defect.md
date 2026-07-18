# Verify — the t̃=0 read-off does NOT enumerate all of Adm (FOURTH verified paper defect)

**Status: VERIFIED DEFECT (2026-07-19) — the recursion's t̃=0 leaf-profile set is a PROPER subset
of the admissible set at interior-bottleneck widths; the λ formula (min over Adm) SURVIVES because
every minimizer is realized. Never state "profile-set ⊇ Adm" or "== Adm" for the recursion.**

*Provenance: pen-and-paper thread 12 (pnp-o5), fork-13 o5-IN. Two-way: the ORIGINAL VALIDATED profile
simulator (`expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py`,
runmin/FIX-A) + a decorrelated Codex consult that found the same discrepancy and characterization
independently (`expeditions/2026-07-17-aoyagi-engine/threads/12-realization/codex/realization-answer.md`).
Exact integer algebra, 847-instance scan (`threads/12-realization/battery/realization-battery.py`,
exit-0). Companion to Def-3 (T-D, `verify-def3-underspec.md`), the p.20 raw-width reset (FIX-A,
`verify-case2-rawwidth-defect.md`), and the p.15 total-comparability defect (`verify-p15-fullchain-defect.md`).
This is the **leaf/read-off face** of the SAME width-drop mechanism as the p.15 defect.*

## The claim (Aoyagi p.22 read-off, as used by the reproduction)

> The exceptional divisors surviving to a t̃=0 leaf enumerate the admissible strata `Adm(M)` — the
> weakly-decreasing profiles `a=(a¹≥…≥a^L=0)` with `aⁱ ≤ M(i+1)` (running-min bound). The learning
> coefficient reads off the minimum of `Mval` over this set.

Used as: the built resolution tree's t̃=0 leaf divisors realize **every** `a ∈ Adm` (the "profile-set ⊇
Adm" / `IsFullMonomialization`-as-completeness half, o5-IN, elder-gate5).

## The defect: `P(M) ⊊ Adm(M)` at interior bottlenecks

Let `P(M)` = the set of t̃=0 leaf-divisor profiles of the recursion tree (any branch, any chooser).

**Witness** (minimal deep instance). `M = (3,3,4,2,3)`, `L=4`, running mins `(r_1,…,r_5)=(3,3,3,2,2)`.
`Adm` has 19 profiles; the recursion realizes only 17. Missing:

| missing `a ∈ Adm` | `Mval(a)` | where it actually appears | why unrealizable at t̃=0 |
|---|---|---|---|
| `(2,2,2,0)` | 7 | `(2,2,2,2)` at t̃=2 | level `2 = r_4`; layer 4 clears only `≤ r_4−1 = 1` |
| `(3,2,2,0)` | 8 | `(3,2,2,2)` at t̃=2 | same — stranded at level `r_4` |

Both missing profiles have `Mval > minAdm = 5`, so the **minimum is untouched** (see "what survives").

**Mechanism — running-min saturation freezing.** `occ_above` at layer `S` is `[J+1, r_S − 1]`. A divisor
at level `≥ r_S` is **never** in `occ_above` at layer `S`, for any pivot `J` and any Case-1 chooser pick;
rollover and Case 2 never lower existing divisors. So it survives layer `S` at level `≥ r_S`, and since
`r_S` is non-increasing it can never reach t̃=0. A t̃=0 divisor with profile `a` needs, at each strict
descent `a^S < a^{S-1}` after its birth layer, `a^{S-1} ≤ r_S − 1`. When `a^{S-1} = r_S` (the running-min
bound is TIGHT and `a` drops afterward) the descent is impossible — the divisor is stranded at t̃>0. This
is **chooser- and branch-independent** (verified by exhaustive pick×branch search on the witness). It is
the same width-drop strand as `verify-p15-fullchain-defect.md`: a divisor at the dropped running min is
stranded above the shrunken chain — there it breaks comparability, here it fails to clear.

**Exact scope** (scan, prediction matched at every instance):

| scan | instances | `P ⊊ Adm` (gap) | `P ⊆ Adm` | `min P = minAdm` | gap ⟺ interior bottleneck |
|---|---|---|---|---|---|
| widths {1,2,3}, L≤4 | 351 | 84 | 351/351 | 351/351 | 351/351 |
| widths {2,3}, L≤4 | 56 | 8 | 56/56 | 56/56 | 56/56 |
| widths {1,2,3,4}, L≤3 | 320 | 56 | 320/320 | 320/320 | 320/320 |
| widths {1,2}, L≤5 | 120 | 22 | 120/120 | 120/120 | 120/120 |

> the gap `P(M) ⊊ Adm(M)` occurs **iff there is an interior bottleneck** —
> `∃ 3 ≤ S ≤ L` with `min(M¹,…,M^S) < min(M¹,M²)` — EXACTLY (0 mismatches / 791 instances).

Failing witnesses: `(2,2,1,1)` (missing `(1,1,0)`), `(3,3,2,2)` (missing `(2,2,0)`), `(3,3,1,1)` (missing
`(1,1,0),(2,1,0)`), `(3,3,4,2,3)` (missing `(2,2,2,0),(3,2,2,0)`), … Non-failing: monotone widths and any
drop only at the last layer (`(3,2,4,2)`, `(2,2,3,3,2)`, all L≤2). Interior bottlenecks (a hidden layer
narrower than the first two) are a common DLN configuration — in scope, not a corner case.

## The corrected statement: `P(M) = Clearable-Adm(M)`

Define `b(a) = 1 + |maximal prefix of a equal to the running-min envelope (r_2,r_3,…)|` and
`Clearable(a) := ∀ S ∈ (b(a), clear(a)], a^S < a^{S-1} ⟹ a^{S-1} < r_S`. Then

> `P(M) = { a ∈ Adm(M) : Clearable(a) }` — EXACT (847 instances + Codex proof, both directions).

Equivalently (Codex form): `a ∈ P` iff every strict descent from a coordinate saturating its running-min
(`a^{s-1} = r_s > a^s`) has the complete running-min envelope as its prefix.

## What survives (the λ formula, via the min-bridge)

The learning coefficient needs only the **minimum**, and the minimum is untouched:

> `minAdm(M) ∈ terminalExponents` — PROVED. Every `Mval`-minimizer is `Clearable`, hence realized.

Proof (Codex's envelope-splice; verified 0 counterexamples / 356 non-clearable profiles). The running-min
envelope prefix contributes **exactly 0** to `Mval` (`(M¹−r_2)(M²−r_2)=0` and each
`(r_j−r_{j+1})(M^{j+1}−r_{j+1})=0`). For a non-clearable `a` with first bad descent at `s`
(`a^{s-1}=r_s`), replacing coords `1..s−1` by the envelope keeps the boundary + suffix terms fixed and
drops the prefix contribution from `>0` to `0`, so `Mval` strictly decreases and `a` cannot minimize.
Directly cross-checked: `min over P(M) = minAdm(M)` at all 847 instances.

**Consequence for the formalisation.** DROP o5-IN as "profile-set ⊇/== Adm" (false). PROVE
`minAdm ∈ terminalExponents` via the envelope-splice minimizer + the steering-rule realization of a
clearable minimizer (cert-o5-realization §3–§4). KEEP `terminalExponents` t̃=0-restricted — the stranded
strata at t̃>0 are real (`(2,2,2,2)` etc.) and an unrestricted `∀k` re-admits them and is false. The full
`⊇ Clearable-Adm` completeness (the strongest true statement) is certified and formalisable, sequenced
post-critical-path (expedition journal tick 150; elder-gate7).

## How it was missed, then found

The four pre-committed kill instances ((2,2,2), (3,3,4), (2,2,2,2), (2,2,3,2)) are ALL
bottleneck-free — `P = Adm` there — so the `== Adm` battery kill sat green while the general
claim was false (the shallow-instance confound, second occurrence in this expedition; lesson:
pre-committed battery sets for read-off/completeness claims must include the known failure
mechanism — interior bottleneck, e.g. `(3,3,4,2,3)`, `(2,2,1,1)`, `(3,3,2,2)`). Found by the
o5-∈ realization certificate's scoped scan, cross-validated against the original simulator.

## Evidence
- exact-recursion battery `threads/12-realization/battery/realization-battery.py` (exit-0, 847 instances):
  B1 `P⊆Adm`, B2 `P=Clearable-Adm`, B3 `min P=minAdm`, B4 minimizer-clearable, B5 chooser/branch-independent
  strand, B6 steering rule realizes exactly clearable.
- original validated simulator `threads/08-atlas-probe/battery/nonmono-2232-sim.py` (runmin/FIX-A) — the
  witness cross-checked on it independently of the pnp-o5 reimplementation.
- decorrelated Codex (hypothesis withheld): `threads/12-realization/codex/realization-{prompt,answer}.md`.
- cert: `threads/12-realization/cert-o5-realization.md`; scope counts: `threads/12-realization/scope-counts.md`.
