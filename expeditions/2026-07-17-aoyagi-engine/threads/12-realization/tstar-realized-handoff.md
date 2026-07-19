# t05 → t06 handoff — the `tStar_realized` deep arc (o5_core §4)

*architect-t05 consolidation at a banked boundary (ceiling honesty, controller ruling #4 tick-190).
t05 carried four arcs this seat — decision package (ADOPTED), sub-gap-1 (clean-three, wired), §3
(clean-three), §4 SPECIFY (crux isolated, o5_core_realized proven). `tStar_realized` is the engine's
hardest single proof (cert §4: "where the Lean effort concentrates") and gets a FRESH dedicated seat
per the t02/t03 pattern — a mapped handoff costs one re-grounding arc; a degraded grind costs more.
This note is t06's entry surface.*

## State (all banked + pushed, branch `expedition/aoyagi-engine--t01-r2`, HEAD `982c657f3`)

- `lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean` builds green, **exactly one live sorry**:
  `tStar_realized` (line ~326). Everything else in the file is clean-three (§3 + the plumbing).
- `o5_core_realized` (same file) is **PROVEN modulo `tStar_realized`** — `#print axioms = [propext,
  sorryAx, Classical.choice, Quot.sound]`, `+sorryAx` via `tStar_realized` ONLY. It is the
  MOVE-AT-LANDING target: when `tStar_realized` lands clean-three, the controller migrates `o5_core`
  from `EngineConstruction` here (its sorry deleted), `EngineObligations` imports `O5Realization`, one
  atomic batch, full-batch gate. Don't touch that wiring — surface to the controller at landing.

## The target (verbatim, in `O5Realization.lean`)

```lean
theorem tStar_realized (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = tStar M
```

`tStar M` (the banked `Mval`-minimizer, `RouteMAchieverPath`) is **`Clearable`** — `clearable_tStar M`
(PROVEN, §3, same file). `t̃ = 0` is automatic (`tStar ∈ Adm`, last coord `0`). MINIMIZER-ONLY: this is
`tStar`, NOT general `Clearable-Adm` (= R7, `realizedProfiles_eq_clearableAdm`). NAMING PIN: `*_realized`
/ `minAdm_mem_terminalExponents`-class; NEVER `*_complete` / `*_eq_Adm`.

## The cert + the plan

- **Cert:** `threads/12-realization/cert-o5-realization.md` §4 (the steering rule `R(tStar)` + the
  anchor-descent invariant, Lean-ready shape) + §5 (boundary cases: root/layer-0, rollover, L=1, the
  minimal/envelope-touching profiles).
- **Controller-approved arc order (fuse #1+#2):** ONE WF-induction (the path-existence ∃-lemma and the
  anchor-descent invariant are the SAME induction — the cert's §4 proof is a single descent; splitting
  in Lean duplicates the case analysis). Then the pull-ordering brick in the descent case. Bank each
  independently (the ∃-lemma skeleton alone is a green push; the invariant statement + base is another).
- **Codex design consult:** FIRED (`b7d5ahhim`); prompt at `codex/s4-structure-prompt.md`, answer at
  `codex/s4-structure-answer.md` (was still running at handoff — READ IT FIRST; it covers the induction
  shape, the invariant predicate, which lemma discharges the pull-ordering brick, and the top risks).

## Proof structure (t05's design, cross-check against the Codex answer)

The existential analog of `leaves_isFullMono` (the ∀-over-leaves WF-induction TEMPLATE, `EngineConstruction`):
1. **WF-induction on the state** (`(conRel_wf M).induction`), generalized over states satisfying an
   **anchor-descent invariant** `AnchorInv M s a` (the anchor divisor `A` present with coords `1..layer`
   = `a`'s prefix, level `a^{layer-1}`) — prove `∃ l ∈ leaves (buildTree M (conOracle M) s), ∃ k,
   divProfile k = a` for `a = tStar M`.
2. At a **terminal** `s` (`conOracle` terminal ⟹ leaf = `leafOfState s`): the invariant at the leaf gives
   the anchor as a `t̃=0` divisor with `divProfile = a`. Read it off `leafOfState` (`t0Indices`).
3. At a **step** `s`: pick the `R(tStar)`-STEERED child `c` among `(conOracle M s).stepChildren`
   (case-1(1) iff target `ℓ > a^S`, else 1(2); case-2/rollover forced), show `AnchorInv M c.child`
   (anchor-descent MAINTENANCE — base/plateau/descent), and `leaves (buildTree c.child) ⊆ leaves
   (buildTree s)` (via `buildTree_step`: leaves of a branch = union of children's leaves) chains the
   witness up. The steered child IS one of `conOracle`'s emitted `StepChild`s (case1Decision emits
   `[stepCase11 s f, stepAppendAdvance …]`; case2Decision one `stepAppendAdvance`).
4. **The pull-ordering brick** (the FLAGGED sub-lemma, descent case): `A` lands at EXACTLY `a^S`,
   Def-4-least at its level. Reuses banked o4 — see below. TRIPWIRE: if this fights beyond a couple
   honest attempts, STOP + report the precise sticking point (controller spawns the pnp-o5 consult seat).

## Reuse machinery (grounded, signatures verified at HEAD — `EngineConstruction.lean`)

- `LiveHeadDom M s` (`:886`): `∀ a b, divTilde a < divTilde b → divTilde b < widthMinUpto M layer →
  ∀ i < layer, divProfile a i ≤ divProfile b i` (head-domination among live divisors).
- `step1_dominates s hlhd hft hwd hlive hx hy hJ hℓ` (`:904`): at a case-1 node, a level-`ℓ` divisor
  `x` dominates a level-`≤J` divisor `y` componentwise (`∀ i, divProfile y i ≤ divProfile x i`). THE
  descent-case brick's core (the anchor at the top level is pulled last, Def-4-least).
- `chooseMin_spec s target hk` (`:1830`): the chosen divisor is at `target` AND componentwise-≤ all
  same-level divisors (Def-4 minimality).
- `chooserTotalOnChain_of_sameLevel s hchain` (`:1861`): on a `SameLevelChainInv` state the chooser
  never falls back (so the case-1 `none` fallback is off the reachable cone).
- `OracleInv M s` (the invariant bundle) + `OracleInv_conOracle_stepChildren` (`:2158`): threads the
  cone-goodness — every reachable state satisfies `OracleInv` (⟹ `SameLevelChainInv`, `LiveHeadDom`,
  `WeakDecInv`, `FlatTail`, `StateInvariant`). You'll thread `OracleInv` alongside `AnchorInv`.
- `buildTree_step` (`:440`) / `buildTree_terminal` (`:431`); `leaves` of a branch = union (via
  `edgesLeaves_eq` `:2402`). `leaves_isFullMono` (`:2461` area) is the ∀-template to mirror.
- `conOracle` dispatch (`:` def) + `case1Decision`/`case2Decision`/`stepCase11`/`stepAppendAdvance`/
  `stepRollover` (the transitions). The horacle-reduction idiom for the nested dependent match: see the
  lean/CLAUDE.md gotcha t05 added (explicit `split` + `Option.some.inj (heq ▸ hyp)` on shadowed
  binders — the template split-chain fails in a reduced context).

## Biggest risks (t05's read; the Codex answer ranks them)

1. **The anchor-identity across the case-1(1) exponent bump.** `stepCase11` bumps `divExp` and tail-writes
   `divProfile` (the anchor's coords change per step). `AnchorInv` must track the anchor by a STABLE
   handle (its evolving `divProfile`/level), not a fixed index — the index `f` is re-chosen each layer.
2. **The steered child = an emitted `StepChild`.** The `R(tStar)` selection must land on one of
   `conOracle`'s actual children (case1Decision's two, or case2/rollover's one). Verify the steering
   rule's 1(1)-vs-1(2) choice matches which child is `stepCase11` vs `stepAppendAdvance`.
3. **The pull-ordering brick** (descent case): `step1_dominates` gives domination but "lands at EXACTLY
   `a^S`" needs the intra-layer ordering (lower levels clear first as `J` advances; the anchor pulled
   last at `J = a^S`). This is the flagged brick — the tripwire's target.

## Battery / ground truth

`threads/12-realization/battery/realization-battery.py` B6: the steering rule `R(a)` realizes EXACTLY
the clearable profiles (847 instances, 0 counterexamples). The original validated simulator:
`threads/08-atlas-probe/battery/nonmono-2232-sim.py` (runmin/FIX-A). Use these to sanity-check any
concrete instance while building.
