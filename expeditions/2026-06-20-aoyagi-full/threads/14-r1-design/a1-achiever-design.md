# A1 #46 achiever (upper bound): the explicit T* construction + feasibility (design for fm)

> **★ LESSON (banked here, next to the work) — verify a relation in its STATED generality, not on the
> structured instance the application feeds.** Across A1 the same trap recurred THREE times: a relation
> verified 0-fail ON THE ACHIEVER `Y` got written as a GENERAL theorem/bridge. (i) Route B's "Gale = #74"
> — a true equivalence on the achiever `Y`, but #74 is NOT sufficient for the assignment in general
> (`M=[0,1,1], Y=[0,2]`: Gale holds, no dominated assignment); the Rado–Gale biconditional is FALSE
> general + UNNECESSARY scoped (pivot-existence = realizability = green `Yvec_lowerfit`). (ii) "lower-fit
> = the #74-dual `largestK(Y)≥largestK(M[1:])`" — true on achiever `Y` but the wrong TARGET; the band
> needs `G2 = largestK over FULL M` (the widths-only bridge fails 1017/1360). (iii) the residual
> two-sided predicate "characterises existence" — only on the achiever `Y` (arbitrary-`Y` mismatch
> 1924/3239). COMMON ROOT: `0/1360`-on-the-achiever certifies the achiever, NOT the general theorem the
> route's PROOF invokes; the decorrelation (Codex) also only tested achiever instances, so it didn't
> catch the insufficiency — the catch came from RE-DERIVING the theorem's general form. FIX HABIT:
> before writing `⟺` / `= X` / `⟹` in a card, ask "in what generality is this the THEOREM vs. an
> achiever-coincidence?" and scope the written statement accordingly. Corollary: a route's "reusable
> general theorem" advantage EVAPORATES if the theorem is only achiever-true — a CONSTRUCTION (BG)
> carries no over-claim risk. (Also in `expeditions/.../lessons.md`.) Owned the B-recommendation twice;
> the front-load check caught each before the hand-off landed.

## ★ CANONICAL B-PIN (2026-06-21) — the consolidated deliverable for a114e07e ★

a114e07e independently confirmed NO closed-form Y-ordering (6 canonical orderings, best 212/1360) — so B
IS the forward greedy + a monotonicity invariant. Here it is, consolidated, all verified 1360/1360
(`/tmp/a1_B_consolidated.py`). (Supersedes the iterations below — DP framing, max=max, #74-reuse — which
record the path; THIS is the pin.)

**THE GREEDY (forward, deterministic — PRODUCES the feasible ordering q + T* in one pass).** Inputs:
the achiever `ℓ*` (= the #45 achiever), `Y = balancedSplit(P,ℓ*) ⊎ tail`, `P = ∑(ℓ*+1 smallest widths)`,
`tail = L−ℓ* largest widths`. State `(u : ℤ, rem : Multiset ℤ)`, `u₀ := M^1`, `rem₀ := Y`. For
`j = 0..L−1`:
- `lo_j := M^{j+1} + u − min(u, admBound_j)`,  `hi_j := M^{j+1} + u`  (`admBound_0=min(M^1,M^2)`, else `M^{j+1}`);
- `q_j :=` the SMALLEST element of `rem ∩ [lo_j, hi_j]` (= `(rem.filter (· ∈ Icc lo_j hi_j)).min`);
- `rem := rem.erase q_j`;  `T*_j := u_{j+1} := M^{j+1} + u − q_j`.

**THE MONOTONICITY INVARIANT (the loop invariant — INV(j), the Lean induction).** Before step `j`
(remaining `rem`, current `u`):
> `INV(j)`:  `u = ∑(rem) − ∑_{k=j}^{L−1} M^{k+1}`  (conservation)  ∧  `q is a permutation of (Y minus rem)`.

**WINDOW NON-EMPTINESS (`rem ∩ [lo_j,hi_j] ≠ ∅`, so the greedy never stalls) — the irreducible Hall
content, decomposed:**
- **Upper fit `min(rem) ≤ hi_j`:** from INV, `hi_j = ∑rem − ∑_{k≥j+1}M^{k+1}`; the smallest of `|rem|=L−j`
  positive elements `≤ ∑rem/(L−j) ≤ hi_j`.
- **Lower fit `max(rem) ≥ lo_j`** ⟸ the achiever-tied guard `smallestK_m(Y) ≤ Sprefix_{m+1}(M)` ∀m,
  which holds under `good ℓ*` (NOT generic — fails 991/16992 over arbitrary c, 0-fail under `good c`).
  a114e07e's count-argument (`count{a_i=b+1}≤r ⟹ complement bound`) closes both regimes; my derivation
  (case ii `S_m≥mb+(m+r−c)` via `good_c@c ⟹ a_c≤b+1` + tail-sum; case i `S_m≥mb`, form `c·S_m≥m(S_c−r)`,
  from `{good_c@i}` linarith) is the decorrelated confirmation/backup.

**ADMISSIBILITY DISCHARGE (`T*∈Adm`).** From `q_j ∈ [lo_j,hi_j]`, the update `u_{j+1}=M^{j+1}+u_j−q_j`
satisfies `0 ≤ u_{j+1} ≤ min(u_j, admBound_j)` ⟹ (i) `u_{j+1}≥0`, (ii) `u_{j+1}≤u_j` (weakly-dec),
(iii) `u_{j+1}≤admBound_j`; and `u_L=0` (rem exhausted, INV(L)). All three Adm clauses hold by the
window bounds — INDUCTION on `j` carrying INV. [verified: admissibility clauses 1360/1360.]

**VALUE DISCHARGE (`Mval(M,T*) = 2·cleanCore(ℓ*,smallest)`).** `edgeQ(M,T*) = q` IDENTICALLY (the
greedy's `u_{j+1}=M^{j+1}+u_j−q_j` ⟺ `edgeQ_j = q_j`, the telescope-inverse) ⟹ multiset `{edgeQ(T*)} =
{q} = Y` (q a permutation of Y by INV) ⟹ `∑edgeQ(T*)² = ∑Y²` ⟹ (the #74 factor-2 identity
`2·Mval = ∑(edgeQ++[0])² − ∑M²`) `2·Mval(T*) = ∑Y² − ∑M² = 4·cleanCore` ⟹ `Mval(T*) = 2·cleanCore`.
[the tail cancels in `∑Y²−∑M²`; verified.] ⟹ `lambdaCore = ½ min Mval ≤ ½ Mval(T*) = cleanCore`; with
#45 (≥) ⟹ `lambdaCore_eq_clean`.

**a114e07e fit:** the monotone-Y infra (srt_of_monotone, smallestK_of_monotone, …) it built handles the
sorted-prefix RHS; the greedy here is the q-PRODUCER (Multiset.erase + filter.min, strong-induction on
`|rem|`); INV is the one loop invariant; the lower-fit reuses its count-argument (= my good_c derivation,
decorrelated). NOTE: c = ℓ* (split-length), and the value closes as `¼(∑Y²−∑M²)` NOT `4·cleanCore` (the
two stale-brief watch-items fm flagged).

---

- **Seat:** `pp` (design). For the lean-formaliser (via fm). Task #46 — the UPPER-bound half of
  `lambdaCore_eq_clean`. The lower bound (#45: corridor-majorization #74 + Step B #73 + padding) is GREEN.
- **Verified** exact-algebra (1360/1360, /tmp/a1_*.py) + decorrelated Codex (xhigh,
  /tmp/codex-a1-achiever-answer.md). Codex's `numerics-don't-replace-Hall` flag is RIGHT — and the Hall
  content is irreducible (no sidestep), BUT it's exactly the #45 majorization (already green), so the
  achiever REUSES #45 for the value.

## What the achiever needs (the upper bound, precisely)

The statement is candidate (d): `∃ ℓ, lambdaCore M = cleanCore ℓ (ℓ+1 smallest widths)`. It splits:
- **LOWER (#45, GREEN):** `∀ T∈Adm, Mval(M,T) ≥ 2·cleanCore(ℓ*, ℓ*+1 smallest)` ⟹ `lambdaCore ≥ cleanCore`.
- **UPPER (#46):** `lambdaCore ≤ cleanCore(ℓ*, smallest)`, i.e. `min_T Mval ≤ 2·cleanCore`, i.e.
  **∃ T*∈Adm with `Mval(M,T*) = 2·cleanCore(ℓ*, smallest)`**. Then `lambdaCore = ½ min Mval ≤
  ½ Mval(T*) = cleanCore`, and with the LB ⟹ EQUALITY.

**KEY SIMPLIFICATION:** the upper bound needs ONE explicit `T*` hitting the value — NOT a minimisation
proof (the LB already gives ≥, so one T* at the value closes =). So #46 = a CONSTRUCTION + a VALUE
identity, not a min-argument.

## Why no naive sidestep (Codex Q3 + verified)

A naive direct `T*` formula does NOT work: "prefix-min, tail forced 0" hits `minMval` only 616/1360;
"largest-fitting-first greedy placement" of the achiever multiset fails 258/1360. The corridor/Hall
content is IRREDUCIBLE (Codex Q3: any closed-form T* must still certify every prefix-corridor
inequality). So the construction is the DP, and the value is the global majorization.

## The construction (Codex Q1: backward DP — Lean-cleanest)

`T*` is the cost-minimising admissible sequence, by a backward DP (primitive recursion on the position):
```
t_L := 0
for j = L−1 downto 0:   t_j := the maximiser of the suffix... (equivalently the DP below)
```
The clean recurrence form (Codex): with the achiever edge-values `q` (the balanced split on the ℓ*+1
smallest widths, placed), `u_j := max(0, min(admBound_j, u_{j+1} + M^{j+1} − q_j))`, `u_0 = M^1`,
`t_j := u_j`. (`admBound_0 = min(M^1,M^2)`, `admBound_j = M^{j+1}` for `j≥1`.)
VERIFIED: the DP `T*` is admissible + `Mval(M,T*) = minMval = 2·cleanCore(ℓ*, smallest)` for all
1360 cases.

## The three obligations (what fm proves)

1. **CONSTRUCTION:** `T*` via the backward DP (primitive recursion on `j`). Total, definable.
2. **ADMISSIBILITY (by induction — the monotonicity invariant):** the recurrence maintains
   `0 ≤ t_j ≤ admBound_j` and `t` weakly-decreasing (and `t_L = 0` by construction). One induction on
   `j` carrying the invariant `u_j ≥ u_{j+1} ∧ u_j ≤ admBound_j`. (This is the "Hall/feasibility" content,
   discharged constructively by the recurrence, NOT a separate Hall lemma — the DP builds feasibility in.)
3. **VALUE (Codex Q4: needs the global majorization, = the #45 machinery):** `Mval(M,T*) =
   2·cleanCore(ℓ*, smallest)`. Via the telescoping identity `2·Mval(M,T) = ∑(edgeQ++[0])² − ∑M²` (the
   #45/#74 identity, factor 2) — for `T*`, the `edgeQ` multiset IS the achiever `Y` (balanced split ++
   tail), so `∑edgeQ(T*)² = ∑Y²` and `2·Mval(T*) = ∑Y² − ∑M² = 4·cleanCore`. REUSES #45's edgeQ/
   majorization (already green); the achiever adds the *equality* case (edgeQ(T*) = Y exactly), which is
   the balanced-split-realises-the-corridor-with-equality fact.

## THE D-CRUX, PRE-HARDENED (the airtight `edgeQ(T*)=Y` argument — telescope-inverse, NOT the DP) — 2026-06-21

The lean-formaliser flagged D (`edgeQ(T*)=Y`) as the friction. The DP framing above makes `edgeQ(T*)=Y`
a property to PROVE of the DP output (hard). **Cleaner: make it hold BY CONSTRUCTION via the
edgeQ/telescope mutual inverse.** This DISSOLVES the crux. Two verified facts:

- **(D1) `edgeQ` and `telescope` are MUTUALLY INVERSE** (verified `edgeQ∘telescope = id`, 4080/4080):
  given any sequence `q = (q_0,…,q_{L-1})`, define `telescope(M,q)`: `u_0 := M^1`,
  `u_{j+1} := M^{j+1} + u_j − q_j`, `T := (u_1,…,u_L)`. Then **`edgeQ(M, telescope(M,q)) = q` identically**
  (pure algebra: `edgeQ_j = M^{j+1} + u_j − u_{j+1} = M^{j+1} + u_j − (M^{j+1}+u_j−q_j) = q_j`). This is
  an EASY algebraic lemma (one `simp`/`ring` per coordinate), NOT the DP.
- **(D2) the QFeasible characterization** (verified, `a1_corridor_greedy.py`): `T = telescope(M,q)` is
  admissible (`T∈Adm M`) ⟺ `q` satisfies the corridor (the telescoped `u` is weakly-decreasing, in-bounds,
  `u_L = 0`). [`{edgeQ(T):T∈Adm} = {q : QFeasible}` exactly.]

**The argument (no DP, no "prove edgeQ(T*)=Y of a DP"):**
1. (B-step, Lean-tactics, the formaliser's job) construct `q*` = a corridor-feasible ORDERING of the
   achiever multiset `Y` (= `balancedSplit(P,ℓ*) ⊎ tail`). [`∃` such ordering: verified `∃T∈Adm,
   edgeQ(T)=Y` 1360/1360 — equivalently `∃` feasible ordering of `Y` by D1.]
2. Set `T* := telescope(M, q*)`. By (D2), `q*` feasible ⟹ `T* ∈ Adm`. By (D1), `edgeQ(M,T*) = q*`
   IDENTICALLY ⟹ the multiset `{edgeQ(T*)_j} = {q*_j} = Y` (q* is a permutation of Y). **`edgeQ(T*)=Y`
   holds BY CONSTRUCTION** — no DP-output property to verify.
3. (Value) `∑ edgeQ(T*)² = ∑ q*² = ∑Y²` (sum-of-squares is multiset-symmetric). With the #74 identity
   `2·Mval(M,T) = ∑(edgeQ(T)++[0])² − ∑M²` (factor 2): `2·Mval(T*) = ∑Y² − ∑M² = 4·cleanCore(ℓ*,smallest)`
   [tail cancels] ⟹ `Mval(T*) = 2·cleanCore`. ∎

**So the D-crux is: (D1) telescope-is-edgeQ-inverse [easy algebra] + (D2) QFeasible-defn [the corridor =
admissibility, already in #45's machinery] + (B) the feasible ordering of Y exists [the formaliser's
Tuple.sort step].** The "why edgeQ(T*)=Y" worry vanishes — telescoping a feasible ordering of Y gives a
T* whose edgeQ IS that ordering, exactly, by the inverse. The DP recurrence above is one CONCRETE way to
produce a feasible ordering, but the formaliser does NOT need it: any feasible ordering (B) + telescope
+ the inverse (D1) closes D. (Replaces obligation 1 "DP construction" with the lighter "telescope a
feasible ordering"; obligation 2 admissibility = D2 QFeasible; obligation 3 value unchanged.)

## B IS THE IRREDUCIBLE CONTENT — NOT "Tuple.sort", but the DP/exchange (honest correction) — 2026-06-21

The controller sharpened correctly: the D-crux pre-hardening RELOCATED the Hall content into B (it did
NOT eliminate it). B = "exhibit a corridor-feasible ordering `q*` of `Y` + prove it feasible." I then
investigated which explicit ordering works — and the honest finding is **there is NO clean closed-form
ordering** (verified, `/tmp/a1_B_*.py`):
- `Y` ASCENDING feasible: 560/1360. DESCENDING: 778/1360. "by-M-position" (place large Y at large-M
  positions): 1218/1360. The cost-minimising backward-DP edges: 1360/1360. Codex (xhigh) independently
  found the feasible ordering is NON-UNIQUE (many per-M profiles) and hit per-(M,ℓ) infeasibility — i.e.
  no simple sort-key rule. (Codex's run timed out before a structured verdict; its probes corroborate
  "no closed form".)
- The prefix-corridor `∀k Σ_{j<k}q_j ≤ M^1+Σ_{j<k}M^{j+1}` is NECESSARY but NOT sufficient (the
  `u_j ≤ admBound_j` bound also bites: 3617/7935 corridor-satisfying orderings still fail). So B's
  feasibility is genuinely the corridor + the bound — the irreducible exchange/DP content.

**So B = the DP construction** (the only verified-general feasible ordering), with admissibility by the
clamp-invariant induction (`u_{j+1} := max(0, min(admBound_j, u_{j+1-recurrence}))` keeps `u`
weakly-dec/in-bounds/`u_L=0` BY the clamps — TRANSPARENT, verified 1360/1360). **No sort-reduction
shortcut:** reducing to sorted-M (via perm-invariance) does NOT help, because `Adm M` is POSITIONAL and
the achiever `T*` lives on the unsorted `M` — sorting needs the `Adm(M)≃Adm(sortM)` Mval-preserving cone
bijection, the ~250-line beast the route-reframe card said to avoid.

**The VALUE, given the DP (clean):** `Mval(T*) = min_T Mval` (`Finset.inf'_mem`, FREE since `T*` is the
DP argmin) `= 2·cleanCore` by `min_T ∑edgeQ² = ∑Y²` — whose `(≥)` is #45 (green) and whose `(≤)` is the
DP attaining the min. (I caught two CIRCULAR attempts to make the value free: "min=∑Y² gives it" is
circular — the `≤` IS the achiever. The honest content: the DP CONSTRUCTS a T attaining `∑edgeQ²=∑Y²`,
and edgeQ(T*)=Y holds by the inverse D1 once T*=telescope(its own feasible ordering).)

**HONEST NET for #46:** the irreducible piece is **the DP construction + its clamp-admissibility**
(NOT a closed-form sort — none exists; NOT a sort-reduction — cone bijection hard). Given the DP, the
value chain is clean (D1 inverse + #45 majorization + `inf'_mem`). The "Tuple.sort step" in the D-crux
section above is WRONG — replace with "the DP construction." The DP is genuinely needed; my D-crux moved
the Hall content from the value-step into the construction-step (where the clamp makes admissibility
transparent), which IS a real gain — but it did not remove the DP. The formaliser builds the DP.

## THE B-DELIVERABLE — EXPLICIT feasible ordering (smallest-in-range greedy) + airtight feasibility — 2026-06-21

**The single A1 blocker, RESOLVED.** Replaces the DP with an EXPLICIT, deterministic, Lean-formalisable
greedy (no cost-minimisation). All verified exact (`/tmp/a1_greedy_min_verify.py`, `a1_invariant.py`,
`a1_nonempty_clean.py`).

### The construction (smallest-in-range greedy — forward, deterministic)
State: `u` (current `u_j`, starts `M^1`), `rem` (remaining multiset of `Y`, starts `Y`). For `j=0..L-1`:
- **window** `W_j = [M^{j+1}+u−min(u,admBound_j),  M^{j+1}+u]`;
- `q_j :=` the **SMALLEST element of `rem ∩ W_j`**; remove it from `rem`; set `u := M^{j+1}+u−q_j`.
- (at `j=L−1` the window forces `q_{L-1}=M^L+u`, giving `u_L=0`.)
`T* := telescope(M,q)` (`T*_j = u_{j+1}`). VERIFIED: `q` perm of `Y`, `T*∈Adm`, `Mval(M,T*) =
½(∑Y²−∑M²) = 2·cleanCore(ℓ*,smallest)` — **1360/1360**. (Tie-break MUST be smallest-IN-RANGE: "pure
smallest remaining" ignoring the window FAILS 560/1360.)

### The feasibility invariant (conservation law — the Lean induction)
**`u_j = ∑(rem) − ∑_{k≥j} M^{k+1}`** (VERIFIED 5008/5008). One step: placing `q_j` (removed from `rem`)
with `u_{j+1}=M^{j+1}+u_j−q_j` preserves it exactly.

### Window-non-emptiness (the irreducible Hall content — DECOMPOSED, the green-but-wrong guard)
`W_j∩rem≠∅` needs `∃v∈rem, lo_j ≤ v ≤ hi_j`, `hi_j=M^{j+1}+u_j`, `lo_j=hi_j−min(u_j,admBound_j)`:
- **Upper fit `min(rem) ≤ hi_j`: ALWAYS** (3648/3648). From the invariant `hi_j=∑rem−∑_{k≥j+1}M^{k+1}`;
  smallest of `|rem|=L−j` positive elements `≤ ∑rem/(L−j) ≤ hi_j`.
- **Lower fit `max(rem) ≥ lo_j`: ALWAYS** (verified 1360/1360). **⚠️ CORRECTION (2026-06-21, the
  lean-formaliser caught a green-but-wrong in MY stated reason):** I'd claimed the reason is
  `max(Y)=max(M)` (Y's tail = the largest widths). That stated mechanism is **WRONG** — it FAILS
  190/1360 as a guard (`max(Y) < max(M^{2..L+1})` in those cases). The numerics passed (the greedy's
  actual lower-fit held 3648/3648) but my *stated mechanism diverged from the truth* — exactly the
  green-but-wrong the front-load discipline exists to surface. **The FAITHFUL guard is the static
  largestK-MAJORIZATION** `largestK_k(Y) ≥ largestK_k(M[:L]) ∀k` (VERIFIED 0/1360) — the DUAL of the
  corridor-majorization #74 (`smallestK_k(eq0) ≤ smallestK_k(M)`, already GREEN). The per-step
  `max(rem_j) ≥ lo_j` is a SUFFIX/prefix of this global majorization (the large Y-values survive in
  `rem` to cover the large widths ahead — the dominance, not `max=max`). So the lower-fit REUSES #74's
  dual, NOT a fresh lemma and NOT `max=max`.

### ⚠️ SECOND CORRECTION (2026-06-21, a114e07e building it found my "#74-dual reuse" INCOMPLETE)
The lean-formaliser reduced the lower-fit to ONE guard `smallestK_m(Y) ≤ Sprefix_{m+1}(M)` (`= a_0+..+a_m
=: S_m` on sorted-ascending `a`), ∀m≤L, and found it **achiever-tied, NOT the generic #74-dual**: it
FAILS **991/16992 over arbitrary c** but holds **0-fail over the achiever c / `good c`** (`good_nat(a,c):
∀i≤c, i·a_i ≤ S_i+i−1`). [I confirmed: 991/16992 arbitrary, 0/13736 achiever, 0/14200 good_c — matches
exactly.] So my "reuses #74" was INCOMPLETE: the `m≤c` half is irreducible **`good c`-tied** content, NOT
generic majorization. (My second incomplete claim on this lower-fit — both caught by the Lean build, not
by me; the front-load + kernel-as-decorrelation working.)

**The corrected guard + its derivation FROM `good c`** (verified exhaustively):
- `smallestK_m(Y) = m·b + max(0, m+r−c)` (corrected Step B), `b=⌊S_c/c⌋`, `r=S_c mod c`. Target:
  `m·b + max(0,m+r−c) ≤ S_m` ∀m≤c.
- **CASE ii (`m+r ≥ c`): `S_m ≥ mb+(m+r−c)`.** CLEAN: `good_c@c` ⟹ `c·a_c ≤ S_c+c−1 = cb+r+c−1` ⟹
  `a_c ≤ b+1` (since `r<c`); ascending ⟹ `a_i≤b+1 ∀i≤c` ⟹ tail `Σ_{i>m}a_i ≤ (c−m)(b+1)` ⟹
  `S_m = S_c−tail ≥ cb+r−(c−m)(b+1) = mb+(m+r−c)`. [linarith from `a_c≤b+1` + the tail sum.]
- **CASE i (`m+r < c`): `S_m ≥ mb`.** THE achiever-tied crux (verified 0-fail under good_c; fails
  680/8474 without). Naive m-induction FAILS (`a_m≥b` is false, 102927/166456). It's a GLOBAL average
  fact needing `good c`'s full running-average ceiling (`a_i ≤ S_{i−1}/(i−1)+1`, the "no jump"). **fm-
  targetable integer form: `c·S_m ≥ m·(S_c−r)`** (= `m·c·b`, verified 113519/113519) — provable from
  `{good_c@i : i≤c}` by `linarith`/`omega` with the ceilings in scope (a114e07e drives the final tactic;
  this is the irreducible `good c`-tied piece, NOT a hand-closed chain — I give the verified statement +
  the mechanism, the formaliser closes the linarith).

**NET for a114e07e:** lower-fit = `smallestK_m(Y) ≤ S_m` ∀m≤c, under `good c`. Case ii CLEAN (good_c@c ⟹
a_c≤b+1 ⟹ tail-sum ⟹ linarith). Case i = `S_m≥mb` (form `c·S_m ≥ m(S_c−r)`) from `{good_c@i}` by
linarith — the achiever-tied crux. Both verified; the m≤c half is `good c`-tied, NOT generic #74.

### What fm proves
1. Construction (forward primitive recursion carrying `(u,rem)`).
2. Invariant `u_j=∑rem−∑_{k≥j}M^{k+1}` (induction, trivial step).
3. Non-emptiness: upper-fit (smallest-≤-mean) + lower-fit (tail-dominance) ⟹ never stalls ⟹ `rem`
   exhausts ⟹ `q` perm of `Y`.
4. Admissibility: `q_j∈W_j ⟹ u_{j+1}∈[0,min(u_j,admBound_j)]` (window bounds) ⟹ `T*∈Adm`.
5. Value: `edgeQ(T*)=q` (D1) ⟹ multiset `=Y` ⟹ `∑edgeQ²=∑Y²` ⟹ (#74) `Mval(T*)=2·cleanCore` ⟹
   `lambdaCore ≤ cleanCore`; with #45 ⟹ `lambdaCore_eq_clean`.

NO DP (the greedy is cleaner — forward, deterministic, one invariant). Hall content = non-emptiness =
upper-fit (mean) + lower-fit (**the largestK-majorization** `largestK_k(Y) ≥ largestK_k(M[:L])`, the DUAL
of green #74 — NOT `max=max`, which was a green-but-wrong I stated and the lean-formaliser caught). All
verified 1360/1360.

### LEAN ENCODING ADVICE (a114e07e's request — the greedy-existence encoding) — 2026-06-21
Target: `∃ q* : Fin L → ℤ, (q* is a permutation of Y) ∧ (q* corridor-feasible)`.
- **The lower-fit guard = the largestK-majorization, proved as the DUAL of #74** (green). State it
  `∀ k, largestK_k(Y) ≥ largestK_k(M[:L])`. [`largestK_k(Y) = ∑Y − smallestK_{L−k}(Y)`; flip #74's
  `smallestK(eq0) ≤ smallestK(M)`.] Do NOT re-prove a Hall lemma — it's #74's dual.
- **Encoding (recommend E1, greedy via strong-induction on the remaining multiset):** carry
  `(u : ℤ, rem : Multiset ℤ)`; recurse on `|rem|` (well-founded, decreases by 1 per step via
  `Multiset.erase`). The per-step lower-fit `max(rem_j) ≥ lo_j` is a SUFFIX of the global
  largestK-majorization (the surviving large values cover the widths ahead) — derive it from the
  majorization-prefix, NOT from `max=max`. The INV `u_j = ∑rem − ∑_{k≥j}M^{k+1}` threads through the
  recursion. (Multiset, not sorted-List: the pick is "smallest element in `[lo,hi]`" =
  `(rem.filter (· ∈ Icc lo hi)).min`, and `Multiset.erase` is the clean state update.)
- **E2 (static dominance⟹arrangement, Gale-Ryser) — only if Mathlib has the theorem:** the
  largestK-majorization IS the dominance condition for `∃` a feasible arrangement; a library
  `majorization ⟹ ∃ ordering-under-prefix-caps` would give the existence non-constructively. But this
  likely is NOT in Mathlib — so E1 (greedy, self-contained given #74's dual) is the recommendation.

(Codex consult attempted twice on the invariant, both hit the env exit-144/timeout — the verification is
my independent exact-algebra; AND the lean-formaliser's Lean-build IS the decorrelation that caught the
`max=max` green-but-wrong, which a timed-out Codex would not have.)

## The feasibility invariant (Codex Q2 — the precise Hall content, positional)

The decisive invariant: `∀k, Σ_{j<k} q_j ≤ M^1 + Σ_{j<k} M^{j+1}` (the POSITIONAL prefix corridor), with
equality at `k=L` (saturation). Equivalent to `u_j` staying `≥ 0`, weakly-decreasing, in-bounds. It is
**POSITIONAL** (indexed by original positions) — NO global sorting of M is needed once ℓ* (hence the
multiset `q`) is fixed. The DP discharges this invariant by construction (the `max(0, min(admBound, ·))`
clamps keep `u` in the corridor at every step).

## Value-side arithmetic sub-lemmas (the named pieces, all verified exact)

The value `Mval(M,T*) = 2·cleanCore(ℓ*, smallest)` reduces to these (1360/1360, 210/210 —
`/tmp/a1_value_arith.py`):
- **`∑Y = ∑M`** (sum preserved): `Y = balancedSplit(P,ℓ*) ⊎ tail`, `M = smallest ⊎ tail`,
  `P = ∑smallest`; balanced split preserves the sum ⟹ `∑Y = ∑M`. ✓
- **`4·cleanCore(ℓ*, smallest) = ∑Y² − ∑M²`**: the `tail` (the `L−ℓ*` LARGEST widths) appears in BOTH
  `∑Y²` and `∑M²` and CANCELS ⟹ `∑Y²−∑M² = ∑balanced² − ∑smallest² = 4·cleanCore`. ✓
- **`cleanCore_perm` (the tail-cancellation)**: `∑Y²−∑M²` depends only on the `ℓ*+1` smallest (via the
  split); the tail multiset cancels symmetrically. (The perm/multiset-symmetry content.) ✓
- **`balancedSplit_sq_int` (closed form)**: `∑(balanced ℓ-split of P)² = ℓ·b² + r·(2b+1)`,
  `b=⌊P/ℓ⌋, r=P%ℓ` (= `r·(b+1)² + (ℓ−r)·b²`). ✓
Value chain: `Mval(M,T*) = ½(∑Y²−∑M²)` [the `2·Mval = ∑(edgeQ++[0])²−∑M²` identity, `edgeQ(T*)=Y`]
`= ½·4·cleanCore = 2·cleanCore`. All exact.

## Net (hand fm)

#46 = backward-DP `T*` + admissibility-by-induction (the monotonicity invariant) + value-via-#45-
majorization (edgeQ(T*) = Y, equality case). The Hall content is irreducible but built into the DP
recurrence (not a separate lemma) and the value reuses #45. The upper bound is then
`lambdaCore ≤ ½ Mval(T*) = cleanCore`; with the LB ⟹ `lambdaCore_eq_clean` (Skeleton sorry 5→4).
NO naive direct/greedy sidestep (verified: 616/1360, 258/1360 fail).

## ★★ THE ACHIEVER-EXISTENCE CERTIFICATE (task #85) — the closed answer, two routes ★★ — 2026-06-21

The controller's #85 diagnosis is CORRECT and now fully understood: the forward greedy's local
invariant (conservation + small-end caps) is NOT inductively closed because feasibility is a
**two-sided** matching (small-end corridor caps AND high-end positional lower bounds `q_j ≥ M^{j+1}`);
the abstract residual two-sided predicate is *also* not closed (verified: abstract-state window-fail
1186, closure-fail 100). There is **no clean local (rem,u,W) invariant**. The fix is a NON-greedy /
structure-aware certificate. Two are below, BOTH exact-verified (0-fail) and **decorrelated** (Route S
= my construction; Route B = independent Codex `xhigh`, every claim re-verified by me).

### ★ THE GREEDY-INVARIANT DICHOTOMY (red-teamed with Codex `xhigh`, restored) — 2026-06-21
The controller asked to push a windowed-greedy COUPLED invariant, then (Codex restored) to red-team it
for ABSTRACT inductive closure. Decorrelated result (mine + Codex, every counterexample re-verified):

**(1) On UNSORTED widths `W` (general positional `M`): no INDEPENDENT checkable closed invariant.**
Once a forward greedy commits `q_0..q_{j-1}`, the residual `rem` must be realised *exactly* in the
residual corridor. The residual base polytope IS a polymatroid (submodular `ρ_resid`, 0/378), BUT
**"is THIS `rem` a base-permutation of the residual polymatroid" is STRICTLY STRONGER than the residual
Gale condition `smallestK_k(rem) ≤ ρ_resid(A)`**. Counterexample (controller's failure mode, now
explained): `rem=(0,2), u=1, W=[0,1]` — Gale holds (`0≤1, 0≤1, 2≤2`), base nonempty (`{(1,1)}`), yet
`(0,2)` is not a permutation of any base point. **Codex confirmed it is parametric, not a zero-width
artefact**: `u=a, W=[a,b], rem={0,2a+b}` for any `a,b>0` (window₀=`[a,2a]`, no `rem` elt fits; residual
Gale still holds) — verified 0,3 / a=1..3. The gap "residual-Gale holds but `rem` not realisable"
occurs 1708/3820 over arbitrary residual states (`/tmp/a1_gap_generalizes.py`); no poly-size corridor-
majorization conjunction closes it (302–576 left). And **exact feasibility itself is NOT greedy-closed
on unsorted W** (Codex CX, re-verified): `u=2, W=[3,1,3], rem={1,3,5}` is feasible (`(5,1,3)`) but
smallest-in-window picks 3 and dead-ends. Smallest-in-window FAILS on 1264 feasible unsorted-W states.

**⚠️ SCOPING CORRECTION (Codex caught my over-claim).** A checkable abstractly-closed invariant
*technically* DOES exist — `GreedyOK(rem,u,slots)` := "the deterministic greedy suffix succeeds" — it
is closed by definition. But it is **tautological**: proving it initially = proving greedy success, so
it is not an *independent* certificate. The honest claim is: **no independent (Gale-style / corridor-
majorization) checkable invariant closes on unsorted W** — not the absolute "no closed invariant".

**(2) On SORTED widths `W` (ascending): the greedy IS clean — an EXCHANGE-lemma closed invariant.**
This is the new positive finding (mine). On ascending `W`, the smallest-in-window greedy step
**preserves exact feasibility abstractly** (0/2130 step-checks; greedy never fails on a feasible state
0/33614). The proof is a clean **exchange**: in any feasible completion, the smallest-in-window element
can be swapped to the front and the completion stays feasible (verified 0/42481,
`/tmp/a1_exchange_lemma.py`). So on sorted widths the closed invariant = "∃ feasible completion", and
the greedy step preserves it via the exchange — terminating by induction on `|rem|`, NON-tautological
(the exchange is the content). **This dovetails with the perm-invariance reduction**: `minMval M =
minMval(sort M)` (0/3000), so sort `M`, run the smallest-in-window greedy (clean on sorted widths),
producing the QFeasible achiever directly — verified end-to-end **0/19525**
(`/tmp/a1_sortedM_greedy_full.py`). NO Rado theorem, NO bubble-transport composition: the greedy
itself is the construction. ⟹ this is **ROUTE T** below (the cleanest of the three).

**Route B (Rado–Gale) escapes the unsorted residual gap** because it never commits a residual — its
sufficiency is for the existence of SOME base-permutation of the achiever `Y` from the TOP, not the
realisability of
an arbitrary committed `rem`. Conclusion: the certificate must be non-residual (Route B top-level, or
Route S global sorted-reduction); the forward-greedy angle is closed.

### The exact QFeasible corridor (the target, in edge-prefix form — re-derived, on the trunk's Adm)
`T ∈ Adm M` ⟺ its edge vector `q = edgeQ(M,T)` (length L) satisfies, with `S_n := M⁰+⋯+Mⁿ`,
`P_n := ∑_{j<n} q_j`:
- **(L)**  `q_j ≥ M⁽ʲ⁺¹⁾`  ∀j                  [positional lower bounds; = u weakly-decreasing]
- **(U)**  `P_n ≤ S_n`  ∀n                       [upper corridor; = u_n ≥ 0]
- **(Ladm)** `P_n ≥ S_n − admBound_{n−1}`  ∀n     [lower corridor; = u_n ≤ admBound_{n−1}]
- **(T)**  `P_L = S_L`                            [total; = u_L = 0]

(`admBound_0 = min(M⁰,M¹)`, `admBound_j = M⁽ʲ⁺¹⁾` for j≥1.) The target: ∃ q a permutation of `Y`
satisfying (L)(U)(Ladm)(T). Then `T* := telescope(M,q) ∈ Adm M`, `edgeQ(M,T*)=q` (D1 inverse),
`∑edgeQ²=∑Y²` ⟹ `2·Mval(T*)=∑Y²−∑M²=4·cleanCore` ⟹ upper bound. Existence verified **0-fail**
(1360 cases widths 0..3 L≤4); existence is **permutation-invariant in M** (`minMval M = minMval(sortM)`,
0/3000) — this is WHY both routes route through sorted M.

### ROUTE B (RECOMMENDED — the deepest/cleanest; Codex `xhigh`, every claim re-verified) — RADO-GALE
Model the placement as an **integer-polymatroid base assignment**. Slots `E = Fin L`, slot-`j` width
`w_j = M⁽ʲ⁺¹⁾`; for `i` put `C_i := min{M⁰,…,Mⁱ}` (so `C_0=M⁰`, monotone non-increasing, `C_L`-style
`= 0` past L). For nonempty `A ⊆ E` define the **rank**
> `ρ(A) := (∑_{j∈A} M⁽ʲ⁺¹⁾) + C_{min A}`,   `ρ(∅) := 0`.

**`ρ` is a monotone submodular (polymatroid) rank** [verified 0/1360]: the width term is modular,
`A ↦ C_{min A}` is submodular (it `= ∑_i (C_i−C_{i+1})·1[A∩{0..i}≠∅]`, a sum of rank-1 "covers").

**Rado–Gale — the CORRECTED, ACHIEVER-Y-SCOPED statement (precision fix, 2026-06-21).**
⛔ **The biconditional as previously written here was an OVER-CLAIM** — confirmed by pp-hall's 3rd
decorrelated check and Codex, and re-verified by me. The FALSE form was:
> ~~`(∃ bijection q : E→Y, ∀A ∑_{j∈A} q_j ≤ ρ(A))  ⟺  (∀A, sumSmallest(|A|,Y) ≤ ρ(A))`~~  ❌ `⟸` FALSE.

The `⟸` fails for general `Y`: `M=[0,1,1]`, `Y=[2,0]` has all hyps + `sumSmallest≤ρ`, but NO feasible
bijection (the value `2` won't fit a cap-1 singleton slot). The map is into a **polymatroid ∩
partition-matroid** (a Rado TRANSVERSAL), so a `sumSmallest≤ρ` (lower/`#74`) family ALONE is NOT
sufficient — it also needs the **per-value UPPER / `largestK` condition** (the partition-matroid side,
flagged at the m≤c lower-fit lines 203–207). `sumSmallest≤ρ` matches existence ONLY on the structured
achiever `Y` (an equivalence there, NOT a theorem in general; arbitrary-`Y` mismatch 1209/2018,
`/tmp/a1_gale_direction.py`).

**The HONEST statement = ACHIEVER-Y-SCOPED** (what is actually true and Lean-provable):
> For the achiever `Y := Yvec M (cAch M)` (every `M`, `hL:1≤L`): `∃ q ~ Y` with `q` QFeasible
> (equivalently `T* := telescope(M,q) ∈ Adm M`).
This is **UNCONDITIONAL in `M`** (verified 0/1360, `/tmp/a1_achiever_unconditional.py`): `cAch M` is
the *largest* good `c`, so `good_c (cAch M)` holds BY DEFINITION — no separate hypothesis (my first fix
wrote "under good_c (cAch M)", which is REDUNDANT; dropped). The internal ingredients the proof uses are
the good-c / `Yvec_lowerfit` (`#74`-side, GREEN) **AND** the `largestK`/`G2` upper-side (the
partition-matroid condition) — but neither `#74 ∧ P1` nor `#74` alone characterises existence for
*general* `Y` (`#74∧P1` mismatch 285/2018, `M=[1,0,1] Y=[0,2]`; `#74` alone 1209/2018) — so the result
is genuinely the achiever-`Y` realizability, **witnessed by the BG construction**, NOT a general
polymatroid biconditional and NOT a clean two-condition predicate.

The math WHERE APPLIED is sound: the achiever-Y descent (0/1360) + existence (0/203k) were re-verified
by pp-hall. This was a **statement-scope over-claim (name≠content), not a math error** — fixed here per
the precision policy. **Route decision:** with B's general-theorem reusability gone (it is achiever-Y-
scoped), the choice defers to a114e07e's lift judgment; controller + pp + pp-hall LEAN BG (a
construction — no over-claim risk, no not-in-Mathlib polymatroid theorem). IF a114e07e nonetheless picks
B, the skeleton to hand is the **achiever-Y-scoped Rado pivot-existence** (good-c hypothesis), below —
NOT the general biconditional. Provable standalone by **induction on |E|**: remove
the largest `Y`-value `y*`, choose a slot `e*`, contract to `ρ'(A) := min(ρ(A), ρ(A∪{e*})−y*)` (again
monotone-submodular-integral), and the residual instance still satisfies Gale + `∑(Y∖y*)=ρ'(E∖e*)`.
The construction with a *searched* `e*` (any pivot keeping the residual Gale-valid) is verified
0/1360, AND **a valid pivot always exists** (0/1360 instances with no valid pivot). ⚠️ But there is
**no clean deterministic pivot rule**: "largest-`y*` → largest-width slot, ties smallest index" FAILS
206/1360; "largest-`y*` → min-index of the minimal tight set" FAILS 1170/1360. So the inductive step
is the genuine **existence-of-a-valid-pivot** lemma, proven by the standard **uncrossing / tight-set
exchange** argument (a valid `e*` exists for any monotone-submodular `ρ` satisfying Gale — the
polymatroid-transversal theorem; `Finset.all_card_le_biUnion_card_iff_exists_injective` is the Hall
atom underneath). NOT a closed pivot formula — the formaliser proves existence, then the construction
follows by induction. This pivot-existence IS the substantial irreducible piece; it is **reusable** and
self-contained. (No free deterministic shortcut on either route — Route B's pivot-existence and Route
S's per-swap witness are both existence/case-analysis, not closed formulas.)

**Discharging the Gale condition for the achiever `Y`** [verified 0/1360]: for `|A|=k`, `i=min A`,
`ρ(A)=C_i+∑_{j∈A}M⁽ʲ⁺¹⁾` is a sum of `k+1` DISTINCT entries of the full width vector `M` (the `k`
slot-widths in `A` plus one of `M⁰..Mⁱ` realising `C_i`), hence `≥ a_0+⋯+a_k` (`a` = sort `M` asc, the
`k+1` smallest). So `sumSmallest(k,Y) ≤ a_0+⋯+a_k ≤ ρ(A)` — the LHS is **exactly the green #74 small-end
lemma in its sorted form** (`smallestK_k(Y) ≤ S_k`). The whole high-end/corridor content is *absorbed*
into `ρ`'s submodularity; the only majorization fed in is green #74.

**Assignment ⟹ QFeasible** [verified 0/1360, clause algebra 0/1360]: from `∑_A q ≤ ρ(A) ∀A` and
`∑q=ρ(E)`:
- (U) prefix `A={0..n−1}`: `ρ(A)=M⁰+⋯+Mⁿ=S_n` (since `min A=0`, `C_0=M⁰`), so `P_n ≤ S_n`. ✓
- (L) complement `q_j = ρ(E)−∑_{A≠j}` … `≥ ρ(E)−ρ(E∖{j}) = M⁽ʲ⁺¹⁾` (for j≥1; `min(E∖{j})=0`). ✓
  (j=0 gives the stronger `q_0 ≥ M⁰+M¹−min(M⁰,M¹)=max(M⁰,M¹)`.)
- (Ladm) suffix `A={n..L−1}`: `∑_{j≥n} q_j ≤ ∑_{j≥n}M⁽ʲ⁺¹⁾ + C_n` ⟹ `P_n ≥ S_n − C_n`; `C_1=min(M⁰,M¹)`,
  `C_n ≤ Mⁿ = admBound_{n−1}` for n≥2 ⟹ (Ladm). ✓

So Route B = **[build Rado–Gale once]** + **[green #74 sorted-form]** + **[ρ clause-algebra, all `omega`/
`Finset` lemmas]**. The two-sided majorizations the design chased are *shadows* of the single Gale
family `sumSmallest(|A|,Y) ≤ ρ(A)`; prefix sets give the small end, complements the high end. This is
why the local greedy invariant could never close — it tracked only the prefix shadows.

### ROUTE S (concrete fallback — no abstract theorem, but L²-fiddly) — SORTED ACHIEVER + BUBBLE TRANSPORT
1. **On sort M** (`a = sort M` ascending), the placement **`q = sort(Y)` (Y ascending) is QFeasible**
   [verified 0/19525, ALL FOUR clauses, each with a clean reason]: (U) `= P_n = smallestK_n(Y) ≤ S_n`
   is green #74; (L) `sort(Y)_j ≥ a_{j+1}`; (Ladm) `smallestK_n(Y) ≥ S_{n−1}` (admBound telescopes
   `S_n − Mⁿ = S_{n−1}`); (T) `∑Y=∑M`. This is the trivial achiever — sorted widths are the most
   constrained corridor.
2. **Transport sort M → M by bubble-sort** [full chain verified 0/19525]: un-sort the widths by
   adjacent swaps; at each swap of an ascending pair at `p`, a feasible `q` maps to a feasible `q'`
   on the swapped widths via a **local exchange** — one of `{id, swap q at (p,p+1), swap q at
   (p−1,p)}`. Mval is preserved FREE by the edge identity (`∑edgeQ²=∑q²` invariant under perm,
   `∑M²` invariant under width-swap). The cone map is `telescope ∘ local-witness ∘ edgeQ`
   [verified 0/747 per step: adm-preserving + Mval-preserving].
   ⚠️ The witness is NOT a single deterministic rule — it needs a 3-way case-split (`swap_p` alone
   never suffices; it's `id`, `swap_pm1`, or a combination). This + the L(L−1)/2 bubble passes is the
   fiddle. `feasible_ms(sort M) ⊆ feasible_ms(M)` [0/360] is the underlying monotonicity: sorting is
   the most-constrained corridor, so the sorted achiever transports OUT to every M.

### ROUTE T (NEW — RECOMMENDED; the cleanest) — SORT M + SMALLEST-IN-WINDOW GREEDY (exchange invariant)
The greedy-invariant dichotomy above gives a third route that is cleaner than both B and S: it is the
forward greedy the controller asked for, made to close by **running it on sorted widths**.
1. **Perm-invariance** `minMval M = minMval(sort M)` [0/3000] reduces the trunk's general-`M` upper
   bound to sorted `M`. (Shared with Route S; the one bridge lemma. NOTE: this is the SAME
   perm-invariance both other routes implicitly need — it is not extra cost.)
2. **On sorted `M`, the smallest-in-window greedy is a CLOSED construction.** State
   `(rem : Multiset ℤ, u : ℤ)`; at slot `j` (ascending widths) pick the smallest `rem` element in the
   window `[max(M⁽ʲ⁺¹⁾, u+M⁽ʲ⁺¹⁾−admBound_j), u+M⁽ʲ⁺¹⁾]`, erase, update `u`. The **invariant** is
   "`∃ feasible completion from `(rem,u)``", and the **step lemma** (the content) is the EXCHANGE:
   *the smallest-in-window element can be swapped to the front of any feasible completion and it stays
   feasible* — proven by a one-swap argument, verified 0/42481. Terminating by well-founded recursion
   on `|rem|`. NON-tautological (the exchange is real work), and abstractly closed BECAUSE the widths
   are monotone (the non-monotone case fails, 1264 states — that is exactly why sorting is needed).
   End-to-end: sorted-`M` greedy ⟹ QFeasible perm of `Y`, verified **0/19525**.
3. The output `q` telescopes to `T* ∈ Adm(sort M)`; value via `edgeQ(T*)=q ⟹ ∑edgeQ²=∑Y²` (#74
   factor-2 identity). With perm-invariance ⟹ the trunk upper bound on general `M`.
**Why T beats B and S.** No Rado theorem to build (B's cost), no L² bubble-transport with a 3-way
per-swap case-split (S's cost). The only substantial pieces are the **exchange step-lemma** (one swap,
clean) and **perm-invariance** (shared). The greedy is exactly the construction the controller wanted —
it just had to run on sorted widths, where the coupled invariant genuinely closes.

### ★ ROUTE BG (a114e07e's CHOICE, #84) — BACKWARD MIN-SUFFIX GREEDY on M, NO TRANSPORT — 2026-06-21
**Honest re-adjudication (correcting my T>S>B):** Routes T and S both still need the `sort M → M`
transport (T's greedy produces `T*∈Adm(sortM)`, the trunk needs `T∈Adm(M)`). a114e07e chose a route
that **avoids the transport entirely** — and it works: the **backward min-suffix greedy runs directly
on the unsorted positional `M`** (verified 0/19525, widths 0..4 L≤5). Mechanism: process `j=L−1…0`; the
suffix `T_j=∑_{k≥j}q_k` must lie in `[Stot−S_j, Stot−S_j+admBound_{j−1}]`; pick the smallest `rem`
value with `q_j≥M⁽ʲ⁺¹⁾` and `T_j` in-window; the achiever-`Y` structure makes the window always
non-empty. KEY (the reachable-vs-abstract point the controller flagged): smallest-in-window on
UNSORTED `M` FAILS on arbitrary abstract states but SUCCEEDS on the achiever-`Y`-reachable states
(0/1360 forward, 0/19525 backward) — the failing abstract states are not reachable from `Y`. So the
proof is **scoped to the achiever `Y`** (not an abstract closed invariant) — which is sound, since we
only need the one achiever witness.
**Window non-emptiness decomposes** into two per-step guards, each 0-fail over all 5008 steps:
- **upper-fit** `min(rem) ≤ hi_q`, and **lower-fit** `max(rem) ≥ lo_q`.
⚠️⚠️ **THE NEXT SENTENCE IS STALE — see §RESOLVED BG SKELETON below for the CORRECT window/band split.**
The stale form said both guards reduce to `#74 + its dual largestK_k(Y) ≥ largestK_k(M[1:])`. CORRECTION
(controller + a114e07e + pp, banked in §RESOLVED): there are TWO DIFFERENT objects — the **WINDOW guard
(the per-position pick / P1=Dom)** uses the widths `M[1:]` (sorted-pointwise dominance over `M⁽ʲ⁺¹⁾`);
the **BAND (P2, `u_j ≤ M⁽ʲ⁾`)** is over **FULL M** (`G2 = largestK_j(Y) ≥ largestK_j(full M)`, `= Yvec_lowerfit`
at `m=L−j`) — the `M[1:]`-for-the-band form FAILS 1017/1360 because `S_{j−1}` includes `M⁰`. Do NOT use
`M[1:]` for the band. (The stale per-step-reduction below is also superseded by the P1/P2 split.)
~~These reduce to #74 + the dual `largestK_k(Y) ≥ largestK_k(M[1:])`; per-step reduction is not a clean
order-statistic (non-descending 1126/1360), the same Hall content as #85 on `M`.~~ → see §RESOLVED.
**REVISED PREFERENCE (Lean cost): BG ≈ T > S > B.** BG and T share the "smallest-in-window greedy +
window-non-emptiness-from-(#74 + dual)" content; BG does it on `M` (skips transport) at the cost of
scoping the invariant to `Y`-reachable states; T does it on sorted `M` (clean abstract closure via the
exchange lemma) but then needs the transport. a114e07e's BG-on-`M` is a sound, transport-free choice;
the irreducible piece is the same Hall window-non-emptiness either way.

#### ★★ RESOLVED BG SKELETON (pp-hall, 2026-06-21) — supersedes the "same irreducible Hall as #85 / Y-scoped invariant" framing above ★★

The §ROUTE-BG framing above (lines: "same irreducible window-non-emptiness Hall content as #85",
"scoping the invariant to `Y`-reachable states") is STALE. The resolution below splits BG's two
obligations and shows **one half IS an abstractly-closed invariant** (cleaner than "all Y-scoped").
This is the spec a114e07e builds against. All statements re-verified 0-fail (numbers inline).

**Construction (backward greedy on the UNSORTED M — ORIGINAL-M-positional output).** `b_j := M⁽ʲ⁺¹⁾`
at the ACTUAL positions. For `j = L−1 … 0`: `q_j := min{v ∈ rem : v ≥ b_j}`; `rem := rem.erase q_j`.
No window upper-bound during the pick (the band is proved separately, NOT folded into the pick).
`telescope`: `u_0 := M⁰`, `u_{j+1} := u_j + M⁽ʲ⁺¹⁾ − q_j`, `T*_j := u_{j+1}`. **`edgeQ M T* = q*`
identically** (one `ring`/coord, the telescope-inverse). Output `q* : Fin L → ℤ` is **original-M-positional**;
`T* ∈ Adm(actual M)` directly — NO perm-invariance, NO sort→unsort transport (verified 0/1360, of which
1239 unsorted; descending-M hammer 0/1360).

**The two obligations split (the reconciliation — both framings right, different obligations):**

- **P1 — per-position lower / stall-freedom** (`q*_j ≥ M⁽ʲ⁺¹⁾`; the greedy always finds a pick):
  **ABSTRACTLY CLOSED**, Y-free. Invariant `Dom(b, R) := (R.card = |b|) ∧ (∀i, sortAsc(R)[i] ≥ sortAsc(b)[i])`
  (sorted-pointwise dominance). The one-backward-step closure: if `Dom(b,R)` and `n≥1`, then
  `v := min{w∈R : w ≥ b_{n−1}}` exists (`sortAsc(R)[n−1] ≥ sortAsc(b)[n−1] ≥ b_{n−1}`) and
  `Dom(b∘castSucc, R.erase v)`. **Verified on ARBITRARY (not reachable) states: 0 stalls, 0 closure-fail / 64805.**
  This is the abstractly-closed invariant prior forward-greedy attempts lacked — `Dom` is the Hall-LOWER
  condition alone, one-sided, genuinely closed.

- **P2 — the band `u_j ≤ M⁽ʲ⁾`** (= the admBound clause = lower-prefix `prefix_j(q*) ≥ S_{j−1}`):
  **Y-SCOPED, NOT abstractly closed** (Dom-states fail the band 38421/62196 BY DESIGN). Proved GLOBALLY
  (post-hoc, not a carried invariant) via `ENGINE-1` (min-suffix-optimality, abstract) + `G2` (Y-scoped).
  ⚠️ NOT provable by naive pairwise exchange (fails 16847/50000) — use the right-to-left induction.

**Why the two framings looked to conflict:** the forward-greedy `§ROUTE-T/§ROUTE-S` window is TWO-sided
(`W_j=[lo_j,hi_j]`), so the upper `hi_j` FOLDS THE BAND INTO the per-step guard ⟹ that guard is Y-scoped
(correctly — it carries the band). BG-backward is ONE-sided in the pick (band stripped out, proved
separately) ⟹ BG's P1 is abstractly closed. So the forward "Y-scoped guard" = BG's `P1 + P2` fused; the
backward split separates the abstractly-closed half (P1) from the Y-scoped half (P2). The forward
`largestK`-guard = BG's `G2` (equivalent, 0/3900).

**THE GATE (prevents a114e07e's abstract-closure check misfiring):**
- Run the abstract-closure check on **P1 = Dom ONLY** → PASSES (0/64805).
- Do **NOT** closure-check the band/P2 → it FAILS abstract closure by construction (38421/62196); its
  gate is **"the band reduces to G2"** (a global structural reduction, not an abstract IH).

**✓ pp CROSS-CHECK (independent, confirms the split — the controller's binary resolved as SPLIT, not
either/or).** Re-verified each piece independently: P1=Dom abstract-closure 16875/16875 (my sweep) ≡
pp-hall's 0/64805 (wider); P2/band Y-scoped (NOT abstractly closed — confirmed); G2 NECESSARY for any
QFeasible perm 0/1360. **The earlier two framings were the two HALVES, not a conflict:** pp's
"Y-scoped guards from #74+dual" = the P2/band half (correct); pp-hall's "Dom abstractly-closed" = the
P1 half (correct). ⚠️ **NAME the band-guard lemma `G2 = largestK_j(Y) ≥ largestK_j(FULL M)`** — NOT the
widths-only "#74-dual `largestK_j(Y) ≥ largestK_j(M[1:])`": the two COINCIDE on the achiever Y (both
0/1360) but the widths-only bridge `∑M[:j] ≤ ∑(j largest M[1:])` FAILS 1017/1360, so only the full-M
G2 is the correct statement for the band. (pp's earlier "lower-fit = #74-dual" was a true-but-wrong-
TARGET; G2 over full M is the bridge.) **Answer to the route's gate-binary: BG IS provable, via P1
abstractly-closed (a114e07e's closure-check PASSES on Dom) + P2 Y-scoped-reduces-to-G2 (a114e07e does
NOT closure-check it).**

**ENGINE-1 — min-suffix-optimality (abstract, Y-FREE, the novel reusable engine).** Under `Dom(b,R)`,
`backwardGreedy` is well-defined (never stalls) and produces `q*` with (a) `q*` a permutation of `R`,
(b) `q*_j ≥ b_j ∀j`, (c) `∀j, ∑_{i≥j} q*_i ≤ ∑_{i≥j} p_i` for EVERY arrangement `p` of `R` with
`p_i ≥ b_i ∀i` (min-suffix, simultaneously ∀j). PROOF: right-to-left induction. ATOM — the rightmost
pick `= min{v∈R : v≥b_{n−1}} ≤ p_{n−1}` for any feasible `p` (`p_{n−1}∈R, ≥b_{n−1}`). STEP — removing
the pick preserves `Dom` (= ENGINE-2) ⟹ induct. [verified abstract: 0 stalls, 0 opt-fail / 20884.]

**ENGINE-2 — Dom closure** (= the P1 invariant's one-step closure, stated above; the abstract-checkable
piece). [0 no-pick-under-hyp, 0 closure-fail / 64805.]

**G1 / G2 — the achiever-`Y` structural facts (the ONLY Y-specific content; reduce to #45's good_c arithmetic):**
- **G1** (feeds P1 / Dom's hypothesis): `sortAsc(Y)[i] ≥ sortAsc(M[1..L])[i] ∀i`. Factors
  `sortAsc(Y)[i] ≥ a_{i+1} ≥ sortAsc(M[1..L])[i]` (2nd = drop-`M⁰` sort fact; 1st via good_i⟺β). [0/3900]
- **G2** (feeds the band P2 — ORDER-FREE `largestK`-majorization): `∀j∈[1,L], ∑(j largest of Y) ≥ ∑(j largest of M)`.
  ⚠️ **NOT the #74-dual** — does NOT reduce to `largestK(Y) ≥ largestK(M[1:])` (FALSE: `S_{j−1}` includes
  `M⁰`; `∑(M[:j]) ≤ ∑(j largest M[1:])` fails 1017/1360). G2 is a distinct majorization of `Y` over the
  FULL `M`. DERIVATION: (i) `j ≤ L−c`: EQUALITY (the j largest of Y = the j largest widths, Y's tail);
  (ii) `j > L−c`, `m := j−(L−c)`: BETA-BLOCK `∑(m largest β) ≥ ∑a[c−m+1..c]`, from the COUNT BOUND
  `#{i≤c : a_i ≥ b+1} ≤ r` (`b=⌊S_c/c⌋, r=S_c mod c`) ⟹ `∑a[c−m+1..c] ≤ m·b + min(m,r) = ∑(m largest β)`. [0/3900]
- **good_i ⟺ β** (load-bearing achiever arithmetic, shared with #45): `β_sorted[r] = ⌊(S_c+r)/c⌋` (0/3900);
  `good_i ⟺ β_sorted[i−1] ≥ a_i` (1≤i≤c, 0/19525), via `⌊(S_c+i−1)/c⌋ ≥ a_i ⟺ S_c+i−1 ≥ c·a_i`, and
  `good_i ⟹ S_c+i−1 ≥ c·a_i` algebraically: `S_c ≥ S_i+(c−i)·a_i` [`a` asc] `+ S_i ≥ i·a_i−i+1` [good_i]
  ⟹ `S_c ≥ c·a_i−i+1`. (Uses only good_i + `a` ascending.)

**ASSEMBLY → 3-sided corridor → Adm → value:** run `backwardGreedy(b=M⁽·⁺¹⁾, Y)` (perm of Y, `q*_j≥M⁽ʲ⁺¹⁾`
by ENGINE-1(a,b)+G1). The three `admPred` clauses:
- **B1 antitone** ⟺ `u` antitone ⟺ `q*_j ≥ M⁽ʲ⁺¹⁾` [P1]. ✓
- **B0 band** `T*_j ≤ admBound_j` ⟺ `u_j ≤ M⁽ʲ⁾` ⟺ (`u_j = S_j − prefix_j(q*)`) `prefix_j(q*) ≥ S_{j−1}`.
  P2 = ENGINE-1(c) + G2: `prefix_j(q*) = ∑Y − ∑_{i≥j}q*_i ≥ ∑Y − minsuffix = MAX-prefix(lower-feasible)
  ≥ ∑(j largest M)` [G2] `≥ S_{j−1}` [trivial: a positional prefix of `M` ≤ the `j` largest]. NON-CIRCULAR
  (no 3-sided existence). (j=0's `min(M⁰,M¹)` is implied by antitone + `≤M¹`.) ✓
- **B2 last-zero** `T*_{L−1}=0` ⟺ `u_L=0` ⟺ `∑q*=∑M`, automatic (`∑Y=∑M`). ✓
⟹ `T* ∈ Adm M`. [0/1360]
**VALUE:** `edgeQ M T*=q*` (perm of Y) ⟹ `∑edgeQ²=∑Y²` ⟹ (green `edge_identity`, factor 2:
`2·Mval = ∑(edgeQ)² + 0² − ∑(Mseq)²`) `2·Mval M T* = ∑Y²−∑M² = 4·cleanCore(c, sortedSmallest M c)`
[via `balancedSplit_sq_int` + `cleanCore_perm`; the `L−c` tail widths cancel] ⟹ `Mval M T* = 2·cleanCore`
⟹ `lambdaCore M = ½ min Mval ≤ ½ Mval T* = cleanCore`; with #45 (≥) ⟹ `lambdaCore_eq_clean`. [0/1360]

**NET:** the ONLY genuinely-new theory is `ENGINE-1` + `ENGINE-2` (elementary, Mathlib-free — the Dom
closure IS the Hall content, done by hand, no polymatroid/Rado/Gale-Ryser). `G1/G2/good_i⟺β` reuse #45's
achiever arithmetic. The telescope-inverse is `ring`/coord. The value reuses `edge_identity` (#74). So the
"same irreducible Hall as #85" framing above is superseded: P1's Hall content **is** abstractly closed
(the part #85's forward-greedy could not close); only the band is Y-scoped, and it's a clean global
reduction to G2, not an irreducible per-step Hall guard. (Escapes #85's residual-realisability gap: P1
certifies only pick-existence — NOT residual-realisability — and the band is global, not a carried
local invariant.) Reproducibles: pp-hall `/tmp` verifications (ENGINE-1 0/20884, ENGINE-2 0/64805,
G1/G2 0/3900, good_i⟺β 0/19525, telescope→Adm+value 0/1360, original-M-positional incl. descending 0/1360).

### VERDICT (pp adjudication — updated after the Codex red-team)
**Recommend ROUTE T (sort M + smallest-in-window greedy + exchange invariant).** It is the controller's
windowed greedy, made to close by sorting first; its only substantial pieces are the one-swap exchange
step-lemma + the shared perm-invariance — no Rado theorem, no bubble-transport. **Route B (Rado–Gale)**
remains the most *general/reusable* (one named feasibility theorem) but ⚠️ **Codex flagged a real
caveat**: the implication `∀A sumSmallest(|A|,Y)≤ρ(A) ⟹ ∃ exact assignment` is FALSE for arbitrary
integer-polymatroid bases (the residual counterexamples refute the general statement). So B must be
proven as a SPECIAL top-level theorem for the actual `ρ` and the structured `Y` — NOT inferred from
"submodular + Gale". That makes B heavier than it first looked. **Route S** is the concrete-no-abstract
fallback but L²-fiddly. ORDER OF PREFERENCE: **T > S > B** for Lean cost (T's exchange lemma is the
lightest substantial piece; S avoids abstract theorems but is fiddly; B needs a carefully-scoped
special theorem). All three route through perm-invariance + the achiever `Y`; all verified 0-fail.

**Decorrelation note.** Codex `xhigh` (restored) RED-TEAMED the greedy-invariant claim and (a) correctly
caught my over-claim — a checkable closed invariant `GreedyOK` *does* exist but is tautological, so the
honest claim is "no INDEPENDENT Gale-style closed invariant on unsorted W"; (b) independently confirmed
the residual gap is parametric (`u=a,W=[a,b],rem={0,2a+b}`) and produced a fresh exact-feasibility-not-
greedy-closed CX on unsorted W (`u=2,W=[3,1,3],rem={1,3,5}`); (c) flagged the Route B general-implication
caveat. I re-verified BOTH Codex counterexamples exactly (`/tmp/verify_codex_cx.py`) and every earlier
claim by enumeration. The NEW positive finding (sorted-W exchange invariant ⟹ Route T) is mine,
cross-checked against Codex's "exact feasibility not greedy-closed on UNSORTED W" (consistent: it IS
closed on sorted W). Two angles, converging — the decorrelation worked as intended.

**Reproducible verification (`/tmp/a1_*.py`).** `a1_corridor_exact.py` (existence 0/1360 + exact corridor
clauses); `a1_perm_invariance.py` (`minMval M = minMval sortM` 0/3000); `a1_abstract_closure.py` (the
residual two-sided predicate is NOT inductively closed: window-fail 1186, closure-fail 100);
`a1_true_gale.py` (two-sided pred ≠ abstract feasibility, mismatch 1924/3239 — the achiever-Y structure
is essential); `a1_rado_gale.py` (Route B: ρ polymatroid + Gale⟺assignment + Gale-for-Y + ⟹QFeasible,
all 0/1360); `a1_rado_induction.py` (searched-pivot construction 0/1360); `a1_our_rho_pivot.py` (no
deterministic pivot: largest-width-slot fails 206/1360); `a1_sorted_trivial.py` (Route S sorted achiever
`q=sortY` 0/19525); `a1_final_reduction.py` (Route S full bubble-transport 0/19525); `a1_conemap.py`
(per-swap cone map adm+Mval preserved 0/747). Codex prompt+answer:
`threads/14-r1-design/codex/a1-existence-{prompt,answer}.md`.

### ★★ THE BAND CERTIFICATE (`hband`, the last A1 seam) — pp-hall, 2026-06-21 ★★

The single open `sorry` in `lambdaCore_eq_clean` (commit e593989) is `hband`, in the exact green name:

    ∀ j : Fin L, (∑ i ∈ Finset.range (j+2), Mseq M i) − admBound M j  ≤  ∑ i ∈ Finset.range (j+1), qStar M i

i.e. with `n := j`: `prefix_{n+1}(q*) ≥ S(n+2) − admBound_n`, where `q* = backwardGreedy (Mwidths M) (Ymulti M)`,
`Mwidths = [M¹,…,Mᴸ]` (POSITIONAL, unsorted), `Ymulti = multiset Yvec`. For `n≥1`, `admBound_n = M^{n+1}`,
so the RHS is `S(n+1) = M⁰+…+Mⁿ` (the "lower-prefix band"); for `n=0`, `admBound_0 = min(M⁰,M¹)` so the
RHS is `max(M⁰,M¹)`.

**The (A)+(B) stress-test verdict (faithful enumeration model, `/tmp/band_model.py` matching the Lean
defs exactly — `Yvec`, `cAch`/`goodAch`, positional `Mwidths`, `backwardGreedy`; band 0-fail over 200k
random + 4830 exhaustive cases):**

- **(A) The static fact `u_{n+1} ≤ admBound_n` for the achiever q\*: SOUND.** 0/200k+4830. (Tried to
  refute; could not.)
- **(B) The circularity is REAL but CONFINED to the abstract level.** The per-position step-1
  `q_n ≥ u_{n+1}` holds 100% for the achiever q\* (0/4830) but FAILS for arbitrary Dom-feasible
  arrangements (~20%: simplest CX `M=(1,0,0)`, feasible `p=[0,1]`, `u=[1,1,0]`, `p₀=0<u₁=1`). So
  "all-picks-≥-u" is NOT abstractly closed under Dom — proving it for q\* would itself need the band.
  **Confirms: a114e07e's step-1 route is circular with the band.** → use a non-circular bridge.

**The non-circular reduction chain (all band-free except the final tight inequality):**
1. **uTel telescoping** (green): `u_{n+1} = S(n+2) − prefix_{n+1}(q*)`. Band ⟺ `prefix_{n+1}(q*) ≥ S(n+2)−admBound_n`.
2. **prefix = total − suffix** + **total = ∑Ymulti = ∑M = TOT** (green perm + `htot`).
3. **min-suffix optimality** = green `BGEngine.backwardGreedy_suffix_le`: for ANY feasible `p` (perm of Y,
   `p_i ≥ Mwidths_i`), `suffix_k(q*) ≤ suffix_k(p)`. So `prefix_{n+1}(q*) ≥ prefix_{n+1}(p)`.
4. Band SUFFICES from: SOME feasible `p` has `prefix_{n+1}(p) ≥ S(n+2)−admBound_n`. **But NO fixed/closed-form
   witness works** — refuted 4 candidate rules: sorted-Yvec (infeasible 290/775 + undershoots 155/775),
   rank-matched (feasible but undershoots 167/775), front-load-largest (band-OK but infeasible 290/775),
   suffix-Yvec (both fail). The min-suffix witness is **data-dependent = q\* itself**. ⇒ the band cannot be
   closed by an external witness; it needs the greedy's own structure.

**Two band-FREE structural facts that DO hold abstractly (0/4830), the genuine new content for the lift:**
- **Suffix locality:** `q*[n+1:] = backwardGreedy (Mwidths[n+1:]) Ymulti` (right-to-left greedy fills the
  suffix positions first from the untouched full pool). Pure structural fact about `backwardGreedy`.
- **Order-free min-suffix:** `sum(q*[n+1:]) = greedyMatch(sorted(Mwidths[n+1:]), Ymulti)` — the min feasible
  suffix sum depends only on the *multiset* of suffix widths, not their order (standard min-sum-assignment).
- **Total excess = M⁰ exactly:** `∑_i (q*_i − Mwidths_i) = M⁰` (perm + ∑Y=∑M). The band ⟺
  prefix-excess `∑_{i≤n}(q*_i − Mwidths_i) ≥ M⁰ − admBound_n`, equivalently suffix-excess `≤ admBound_n`.
- **j=0:** `q*_0 ≥ max(M⁰,M¹)` (0/4830).

**The single load-bearing inequality (where `good_floor_core` bites, NOT band-free):**

    greedyMatch(sorted(Mwidths[n+1:]), Ymulti) ≤ sum(Mwidths[n+1:]) + admBound_n     [0/4830, min_slack=0 — TIGHT]

This is the order-free band; `min_slack=0` in both the balanced (`n<c`) and tail (`n≥c`) regions ⇒ the bound
is tight, so `good_floor_core` (the achiever arithmetic `c·aS_i ≤ Sprefix(c+1)+(i−1)`) IS NEEDED — a pure-Dom
pool would not satisfy it. Suffix excess is NOT single-position (up to 3 nonzero positions occur), so the
sum bound does not collapse to a per-element bound; it is a genuine sum-of-excess statement.

**Reconciliation with shapeInv (controller's note):** my earlier `shapeInv`/`band_count_bound` and a114e07e's
static route both reduce to THIS shared inequality (= the (A) static core). The difference is only the
bridge: a114e07e's "all-picks-≥-u" step-1 is **circular** (B above), so the **non-circular bridge wins** —
and the cleanest non-circular bridge is min-suffix-optimality (green) + suffix-locality + the order-free
reduction above, NOT a carried per-step `shapeInv` (the data-dependent shape-tracking is avoidable). The
order-free min-suffix collapses the data-dependence: the suffix SUM is determined by the multiset of suffix
widths, so the formaliser bounds it without tracking the per-step residual pool `R_i`.

**Reproducibles (`/tmp/`):** `band_model.py` (faithful model: band 0/200k+4830, suffix-locality, total-excess,
j0 all 0-fail); `static_exact.py` ((A) 0-fail; (B) abstract-fail 163/775,444/1360 vs achiever 0-fail);
`witness_search.py` + `shift_witness.py` (4 fixed witnesses all fail); `headcount_route.py` (order-free
min-suffix 0/4830); `orderfree_count.py` (order-free band 0/4830, min_slack=0, both regions).
