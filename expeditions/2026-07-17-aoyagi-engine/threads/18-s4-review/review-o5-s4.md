# Review — o5 §4 realization arc (FIDELITY + non-vacuity)

**Reviewer:** controller-spawned, fidelity function. **Target:** `tStar_realized` +
`o5_core_realized`, `lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean`.
**Integration HEAD reviewed:** `88babb1dd` (merge of `origin/expedition/aoyagi-engine--t06-s4`);
branch `review/o5-s4`. **Method:** read of cert §§3–5, both design consults, defect #4, the
target file (all 892 lines) + the consumed defs (`widthMinUpto`, `IsFullMonomialization`,
`Mval_tStar_eq`, `Clearable`, `realizedProfiles`); one decorrelated Codex consult (xhigh,
`codex/fidelity-redteam-{prompt,answer}.md`); a by-hand trace of `conOracle` on the `![2,2,0]`
counterexample.

## Verdict: SURVIVED on the audited theorems — all 6 checklist items PASS.

One **secondary fidelity escalation** (report-only): the *sibling, still-sorried* target
`realizedProfiles_eq_clearableAdm` (R7) is stated width-free and is **false** at `![2,2,0]` by the
same `hMpos` mechanism. Not a defect in the audited theorems (which are correctly guarded), but it
must be flagged before R7 is attempted.

---

## Checklist

**1. Statement fidelity — PASS.** `tStar_realized` (O5Realization:869) is literally
`tStar M ∈ realizedProfiles M` (the ∃-leaf-∃-analytic-divisor form of `realizedProfiles`,
ClearableReify:56). It is a single-profile existence — the minimizer only — NOT `realizedProfiles ⊇
Adm` (false, defect #4) and NOT `= Clearable-Adm` (R7). Matches cert §4's minimizer-only ⊇ claim,
instantiated at `a = tStar` via `clearable_tStar` (§3). Names honor the pin: `*_realized`, no
`*_complete` / `*_eq_Adm`. `o5_core_realized` (O5Realization:882) is the `divExp = minAdm` corollary.

**2. hMpos scoping — PASS; hypothesis is naturally sharp.** `hMpos : ∀ i, 0 < M i` present on both
theorems; zero-width caveat co-located in both docstrings (O5Realization:857-863, 877-878) with the
`![2,2,0]` witness. I verified the counterexample against the actual Lean `conOracle` (not the python
sim): for `M = ![2,2,0]` (L=2), `tStar M = (2,0)` (unique `Mval=0` minimizer); layer-0 Case-2 twice
emits `(0,0)@t̃=0` and `(1,1)@t̃=1`; at layer 1 the rollover guard `widthMinUpto M 2 = min(2,2,0) =
0 ≤ cleared` fires immediately, so `(2,0)` never lands — `realizedProfiles(![2,2,0]) = {(0,0)}`.
Tightness: `widthMinUpto M L = min(M 0 … M L)` over all `L+1` entries (EngineDefs:121), so
`0 < widthMinUpto M L ⟺ ∀ i, 0 < M i` — `hMpos` is exactly Codex's suggested condition, not a
weakening. The **last** width `M L` is load-bearing (the witness has `M 2 = 0`); no prefix-only
positivity supports the uniform theorem. Codex caveat preserved: strict logical minimality over
arbitrary predicates is not established (isolated zero-width instances could realize), but
all-width-positivity is the sharp *uniform* running-min condition. Not gratuitously strong.

**3. SteerInv fidelity + non-vacuity — PASS.** The 3-phase `SteerInv` (O5Realization:427-456)
transcribes both consults clause-for-clause: `SteerPre` = envelope head + `cleared ≤ a^layer` + low-
level occupancy; `SteerAnchored` = suffix-below-envelope + **LowCover** (`∀ q ≤ a^layer, ∃ k,
divTilde k = q`) + anchor `divProfile A = cut a layer q`, `divTilde A = q`, `a^layer ≤ q <
widthMinUpto layer`, landed/pending disjunction; `SteerDone` = `L ≤ layer ∧ ∃ A, divProfile A = a ∧
divTilde A = 0`. `cut` (line 412) matches the consults' `cut a S q`. The suffix clause uses
`widthMinUpto M (i+1)` = the consults' `runMinWidth M i` (`runMinWidth_eq_widthMinUpto`) — a sound
rephrasing. **Non-vacuity:** base holds (`SteerInv_conRoot`, vacuous `pre` at layer 0); phases
genuinely transition — `PRE→ANCHORED` only via the Case-2 birth at `cleared = a^layer`,
`ANCHORED→DONE` only via rollover at `layer+1 = L`; at a terminal both `pre`/`anchored` are impossible
(`conOracle_terminal_le` forces `L ≤ layer`, both carry `layer < L`), so `SteerInv` at a terminal ⟹
`done` ⟹ a real anchor with profile `a`, read off by `leafOfState_carries`. The predicate has real
content (it *fails* at `![2,2,0]`, so it is not trivially satisfiable).

**Pull brick — PASS, real proof consuming LowCover.** Case-1(1) `f = A` (O5Realization:731-772): `A`
is pending (`hgt' : a^layer < q`); the `hclear` sub-proof takes `cleared < a^layer` and derives a
contradiction — LowCover supplies a divisor at level `cleared+1`, which the chain
`cleared < a^layer < q = target < widthMinUpto layer` makes eligible, so `target ≤ cleared+1`, but
`target = q > a^layer ≥ cleared+1` — hence `cleared = a^layer`, and `setTail` lands `A` as
`cut a layer (a^layer)`. This is the level-coverage argument from both consults; **no** domination
lemma (`step1_dominates`) is used for the landing (it enters only indirectly via `OracleInv`
preservation). Codex independently verified the same reasoning has no gap.

**4. WF fold + child selection — PASS.** `exists_steered_child` (O5Realization:517) selects
`c ∈ (conOracle M s).stepChildren` — a genuine emitted child (rollover/Case-2 singletons, or the two
literal `case1Decision` entries steered by `a^layer < target`), not an abstract child; the `chooseMin
= none` fallback is discharged by `chooserTotalOnChain_of_sameLevel`. `childLeaves_subset`
(O5Realization:330) propagates in the correct direction — `leaves(child) ⊆ leaves(parent)` — so a
realized leaf found deep in the tree is a leaf of the whole tree (`realize_aux`:850-851). Composition
`o5_core_realized` (O5Realization:884): `IsFullMonomialization.1 k` gives `divExp k = (Mval M
(divProfile k)).toNat`; with `hk : divProfile k = tStar M` and `Mval_tStar_eq : Mval M (tStar M) =
(minAdm M : ℤ)`, the chain `divExp k = ((minAdm M : ℤ)).toNat = minAdm M` closes via
`Int.toNat_natCast`. The read-off needs only `hL` (width-free); `hMpos` enters purely through
`tStar_realized`, consistent with the width-free `⊆` bound.

**5. No upstream edits — PASS.** The entire t06-s4 arc (commits `04c85bf98 … ed14ef446`, incl.
`fc82de575`) touches only `lean/…/O5Realization.lean` + `statement-card-o5-s4-realized.md`. No
upstream Lean file edited; consumed lemmas (`OracleInv_conOracle_stepChildren`,
`chooseMin_spec`, `conOracle_terminal_leaf`, `divTilde_stepAppendAdvance_*`, `tildeOf_setTail_eq`,
`isFullMonomialization_buildTree_conRoot`, `Mval_tStar_eq`) are the banked defs (no redefinition).
Target file is genuinely sorry-free (`grep` finds `sorry` only in a docstring).

**6. Wording scrub — PASS.** `grep -rniE` of the banned list over the file: no hits. Docstrings are
object-level.

---

## Secondary escalation (fidelity, report-only) — R7 is false as stated

`realizedProfiles_eq_clearableAdm` (ClearableReify:70, **sorried**) is stated width-free
(`_hL : 0 < L` only): `realizedProfiles M = { a | a ∈ Adm M ∧ Clearable M a }`. **This is false at
`![2,2,0]`.** `realizedProfiles(![2,2,0]) = {(0,0)}` (my `conOracle` trace); but the RHS contains
`(1,0)` — `(1,0) ∈ Adm`, and `Clearable M (1,0)` holds *vacuously* (the descent at `j=1` has
`a 0 = 1 ≠ widthMinUpto M 1 = 2`, so the Lean `Clearable` implication is vacuous) — and also `(2,0)`.
So LHS ⊊ RHS. The same `hMpos` mechanism that breaks `tStar_realized` breaks R7; `clearable_tStar`
is width-free, so `tStar M = (2,0)` is Clearable-but-unrealized at `![2,2,0]`.

Consequences to escalate (all caveat-omissions, not math errors):
- **R7's Lean statement needs `hMpos`** (or a revised RHS predicate). Attempting the current
  width-free statement is attempting a false theorem. Its docstring (ClearableReify:65-67) caveats
  only `L = 0` — it must also caveat positive widths.
- **cert §1 / `verify-realization-gap-defect.md`** state `P(M) = Clearable-Adm(M)` "EXACT" and "the
  strongest true statement" with **no positivity caveat**; the battery was positive-widths-only
  (per `s4-invariant-answer.md`). The characterization holds only for positive widths.
- The target file's docstring (O5Realization:18) points to R7 as the `⊇ Clearable-Adm` target
  without the caveat — harmless in isolation (the audited theorems are minimizer-only and guarded),
  but it should carry the pointer that R7 needs `hMpos`.

## Confirmed-expected (tracked, controller-owned) — downstream re-signature

`o5_core` (EngineConstruction:2611) is still **sorried and width-free** (`hL : 0 < L`); `o5_realization`
(EngineObligations:64), `monomialization_terminates` (:83), `resolutionOf` (:94) call it width-free.
When `o5_core` is replaced by the `hMpos`-requiring `o5_core_realized`, all of these must acquire
`hMpos`. This is the move-at-landing batch already owned in the statement card §"Composition note";
Codex confirmed the mismatch. Not a new finding — but load-bearing, and the RLCT payoff must have
positive widths available (true for genuine DLN architectures: all layer dimensions ≥ 1).

## Decorrelation
`codex/fidelity-redteam-{prompt,answer}.md` (xhigh). Codex confirmed items 1-3 PASS, ranked item 4
(downstream) HIGH RISK, and independently surfaced the R7 falsity. Inference-vs-fact preserved: my
`realizedProfiles(![2,2,0]) = {(0,0)}` and the RHS membership of `(1,0)`/`(2,0)` are hand-computed
from the pasted defs; the `conOracle` rollover trace is on the actual Lean object.
