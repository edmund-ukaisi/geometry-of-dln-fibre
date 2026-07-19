# Review — A+B+C construction spine (fidelity + bedrock-taste)

**Target:** `isFullMonomialization_buildTree_conRoot` and the definitions/lemmas it rests on, in
`lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean` + `EngineDefs.lean` (integration HEAD
`1e039cbfa`).
**Function:** fidelity + bedrock-taste (report-only; no fixes, no edits outside this file).
**Reviewer:** independent (branch `review/aoyagi-spine-abc`, own worktree). Decorrelated Codex read:
`threads/13-spine-review/codex/isfullmono-fidelity-{prompt,answer}.md`.

## Verdict: SURVIVED

The spine is faithful to the certs, the paper (with FIX-A correctly applied), and defect #4; it is
non-vacuous (no sorry / no axiom / no `native_decide`); the invariant kit matches
`cert-compchain-o4`. Three low-severity notes below (two precision/wording, one benign guard
observation) — none is a fidelity mismatch, soundness break, or refuting case. All report-only.

## Per-checklist

**1. Statement fidelity of `IsFullMonomialization` — PASS (one precision note).**
`EngineDefs.lean:209-216`. The analytic side is `Fin l.numDiv` (t̃=0), and every constraint on it is
correctly restricted:
- C1 `∀ k : Fin l.numDiv, divExp k = (Mval M (divProfile k)).toNat ∧ divProfile k ∈ Adm M` — the
  `∈ Adm` is on the ANALYTIC side only, i.e. the SAFE `P ⊆ Adm` direction (each realized t̃=0
  profile is admissible), which the certs prove (`leaf_mem_Adm`, 0 extra / 847). It does NOT assert
  `Adm ⊆ P`. Codex-confirmed with an explicit `M=(2,2,2)` countermodel to completeness.
- C2/C3 are the two-sided t̃=0 sublist tie (each analytic divisor matches a t̃=0 full divisor; every
  t̃=0 full divisor is matched). This is fork 12(b)(ii): the analytic enumeration is the t̃=0 sublist,
  NOT an unrestricted `∀ k` over the full ledger (which would be FALSE — the leaf carries t̃>0
  stranded divisors, defect #4).
- `divExp = Mval(divProfile)` coherence is genuine, not an alias: `divExp` is an independently
  accumulated field (`ResolutionTree.lean:133`) and the equality is proven via the maintained
  `MvalCoh` invariant (`EngineConstruction.lean:1365`), not baked in.

*Precision note (low):* the EngineDefs:205 docstring says the analytic side is "EXACTLY the t̃=0
sublist." C2+C3 in fact guarantee equality of the `(divExp, divProfile)` VALUE SUPPORTS (set-level),
not a multiset/index bijection — duplicate values may collapse. This is harmless for the intended
downstream use (SET / MINIMUM of t̃=0 exponents in `terminalExponents`; min is support-only), and the
actual `leafOfState` constructor IS a genuine index sublist (`t0Indices` filter), so the tree the
headline is about does satisfy the stronger property. But the predicate as an interface is weaker
than "EXACTLY the sublist." Multiplicity-sensitive consumers (component counts, coordinate products)
could not rely on C2+C3 alone. Codex independently flagged the same gap. Report-only.

**2. No smuggled completeness — PASS.** `grep -rniE` over the Engine modules found no `⊇ Adm` /
`== Adm` / "enumerates Adm" claim; every "enumeration" hit refers to the t̃=0 SUBLIST tie, and the
`⊇` hits are cube-covering geometry in `PivotCover`, unrelated to `Adm`. Names denote content: the
headline proves `IsFullMonomialization` (per-leaf full-monomialization), not stratum-completeness.
The minimizer-realization (`minAdm ∈ terminalExponents`) and the lower bound live in
`CanonicalResolution`'s exponent-hook conjuncts (task D), separate from this spine.

**3. FIX-A implementation — PASS.** `stepUpdate` case-2 (`EngineDefs.lean:151-154`) sets the new
divisor's profile head to `runMinWidth M p` (the running-min cap), NOT raw `M p.succ`; the docstring
(`:146-150`) carries the `DEVIATION-FROM-PAGE (FIX-A)` note citing
`verify-case2-rawwidth-defect.md`. No code path uses the raw p.20 label. `conOracle` emits
`resRows = widthMinUpto M s.layer − s.cleared` (running-min corank `M(S)−J`) and
`resCols = M ⟨s.layer+1⟩ − s.cleared` (raw `M^{S+1}−J`) for both case-1 and case-2
(`:2112-2120`). The case-2 exponent `resRows·resCols` is FORCED equal to
`Mval_setTail_runMinWidth = (widthMinUpto layer − J)(M^{layer+1} − J)` (`:741`, `:2301-2304`) — the
running-min corank form, the FIX-A distinction (raw `M^{layer}` would not close `MvalCoh`, the
truth-signal). Case-1's `+= runLen·resCols` correctly uses raw `M^{layer+1}` (p.16 exponent,
unaffected by FIX-A) and is forced equal to the `Mval_setTail_delta` (`:806`, `:2339-2343`).

**4. Invariant kit fidelity — PASS.** All statements match `cert-compchain-o4`:
- `WidthBound` (`:872-874`) is LIVE-restricted — guard `s.divTilde k < widthMinUpto M s.layer`; the
  docstring records that the global form is FALSE at `(3,3,1,1)` (stranded `(2,2,2)` head `2 >
  runMinWidth 1`), matching cert Part 3/6 "for live a."
- `T0Bound` (`:1490-1491`) is unconditional / liveness-free; the docstring notes it survives a
  stranding terminal `widthMinUpto L = 0`, which is exactly why it (not `WidthBound`) gives leaf `∈
  Adm` at a bottleneck (`leaf_mem_Adm_t0`).
- `LiveHeadDom` (`:886-888`) = cert Part 6 (`t̃ a < t̃ b < widthMinUpto layer` ⟹ head-domination);
  `< widthMinUpto` guard excludes stranded divisors — why it survives the width-drops that refute the
  full chain.
- `FlatTail` (`:650-652`) = constant tail from `layer` (cert Part 3); `WeakDecInv` (`:540-541`) =
  weak-decrease; `SameLevelChainInv` (`:625-628`) = same-t̃ comparability (cert Part 2, the reshape
  from the refuted paper full chain).
- `BoundaryFlat` (`:1422-1424`) IS the case-1 bump-faithfulness fact — it is exactly the `hbdry`
  precondition of `Mval_setTail_delta`, the boundary flatness making the case-1 exponent bump equal
  the `Mval` delta.
- Chooser minimality is threaded (`hmin`) through the case-1 preservation lemmas
  (`OracleInv_stepCase11`, `_case12`), matching cert Part 7 (minimality is LOAD-BEARING, not demoted;
  the max pick breaks `SameLevelChainInv` at `(2,2,3,3,2)`). Docstrings carry the WHY next to each
  claim.

**5. Guard honesty — PASS (one benign observation).** The headline's `0 < L` is the only
hypothesis, over the specific `buildTree M (conOracle M) conRoot` — no hidden narrowing. Observation:
the headline is actually VACUOUSLY true at `L = 0` (`conRoot.numDiv = 0`, `classify` terminates at
the root since `0 ≤ 0`, so all three `IsFullMonomialization` conjuncts quantify over empty `Fin 0`),
so `0 < L` is not strictly FORCED for the top statement. It is genuinely needed inside
`leaf_mem_Adm_t0`/`le_tildeOf` for non-empty leaves; the docstring's "nondegenerate-chain guard"
framing is correct for where `hL` is consumed but slightly overstates its necessity for the headline.
This narrows the claim in the SAFE direction (excludes a degenerate single-layer case), so it is not
an infidelity — the theorem is if anything under-claiming. Report-only.

**6. At-exhaustion rollover guard (fork 13(Q3)) — PASS.** `StepRel`'s third conjunct
(`EngineDefs.lean:200`) is `e.case = rollover → widthMinUpto M (n.layer + 1) ≤ n.cleared` — a
SEPARATE conjunct, vacuous for case11/case12/case2, so the ledger equality stays rfl-class.
`classify`'s rollover trigger (`:1899`) is `widthMinUpto M (s.layer + 1) ≤ s.cleared` — the SAME def
`widthMinUpto`, same expression shape, not a lookalike copy. `rolloverDecision` (`:1919-1931`)
discharges the guard via `hex` = the exact `conOracle` dispatch condition, and its node
`s.toStepData` has `layer = s.layer`, `cleared = s.cleared` (`toStepData_layer` /
`toStepData_rootLedger_core`), so `StepRel`'s guard reduces to classify's condition. Structurally
pinned to the simulator-validated dispatch, matching fork 13(Q3).

**7. Wording scrub — mostly clean.**
- `load-bearing` × 4 (EngineDefs:56 "carried but not load-bearing"; EngineConstruction:139, 269,
  319) — all OBJECT-LEVEL technical descriptors of proof dependency (which field/hypothesis a step
  rests on). This is the "keep" class per `review.md` (distinct from the banned `this is
  loadbearing` self-reassurance). KEPT.
- `just` × 1 (EngineConstruction:724 "the running-min through layer 0 is just M⁽¹⁾") — minor
  removable filler; "is M⁽¹⁾" suffices. Flagged (low).
- No `honestly / importantly / fundamentally / of course / simply / clearly / obviously / the whole
  point is` in either spine file.

## Supplement (builder's worry-list, items 8-10) — all PASS

**8. Genuine-tree — PASS.** The capstone (`EngineConstruction.lean:2509-2512`) is
`IsFullMonomialization (buildTree M (conOracle M) conRoot)` — the REAL `conOracle` dispatch
(`:2090`), not a trivial/terminal stand-in. For a genuine `M` (`M 0, M 1 ≥ 1`), `classify`/`conOracle`
at `conRoot` (`numDiv=0`) takes the case-2 branch (`occ = []` ⟹ `min? = none`; not rollover since
`widthMinUpto 1 = min(M0,M1) ≥ 1 > cleared`), so the first step is genuine and the tree is a
non-trivial `branch`. The theorem is additionally robust to the off-cone `chooseMin = none` fallback
(it holds even if that fired, via `leaves_isFullMono`'s terminal branch), and on the reachable cone
the fallback never fires (`chooserTotalOnChain_of_sameLevel` from `SameLevelChainInv`). Not a vacuous
object.

**9. Non-vacuity — PASS.**
(a) A concrete nonempty-analytic witness exists: `CanonicalWitness224.lean` builds `tree224` for
`M=(2,2,4)` with `numDiv_leaf224 : leaf224.numDiv = 1` (rfl), `divExp = 4`,
`terminalExponents_tree224 = [4]`, `minAdm_M224 = 4`, and `canonicalResolution224_arithmetic` proving
the full `CanonicalResolution` arithmetic including `srcBox.Nonempty` — so the predicate has real
content on a genuine DLN. (This is a hand-built satisfiability witness mirroring the case-2 emission,
a separate object from `buildTree conOracle`; combined with item 8 it establishes both that the
predicate is contentful and that the constructed tree is non-trivial.) Empty analytic sides at
t̃>0-only leaves remain legitimately allowed (fork 12(b)), so the universally-quantified statement is
the correct shape.
(b) The `leafOfState` `flatDim = 0` `dite` branch is discharged by a PROOF, not an assumption:
`flatDim_pos_of_append` (`:1571`) proves `0 < flatDim M` from an append firing (`Nat.mul_pos` on the
two widths forced `≥ 1` by the guard `cleared < widthMinUpto (layer+1)`, then `single_le_sum`), which
feeds `NumDivFlatPos_stepAppendAdvance`; `NumDivFlatPos` is threaded from `NumDivFlatPos_conRoot`
(vacuous) through the reachability. In `leafOfState_isFullMono`'s else branch (`:2395-2397`),
`0 < flatDim` is contradicted from any full divisor `j` via `hnf`, so `flatDim = 0 ⟹ numDiv = 0 ⟹`
no divisor exists at all (subsumes "no t̃=0 divisor") — the empty analytic side is faithful. Genuine
proof.

**10. Non-circularity of the case-1 `Mval` delta — PASS.** `Mval_setTail_delta` (`:806`) has one call
site (`:2341`). Its `hbdry` precondition is supplied there (`:2336`) by `hbf hlive f …` — the PARENT
`BoundaryFlat` invariant (a hypothesis of `MvalBoundaryInv_conOracle_stepChildren`, threaded from
`BoundaryFlat_conRoot` via reachability), NOT assumed at the leaf; its `hflat` precondition comes from
`divProfile_tail_eq_tilde` off `inv.ft`/`inv.wd`. Circle check: the `BoundaryFlat_step*` maintenance
lemmas (`:1429`, `:1441`, `:1462`) do NOT reference `Mval` or the delta lemma (grep empty). So the
dependency is acyclic: the delta consumes `BoundaryFlat`; `BoundaryFlat`'s own maintenance is pure
profile/`tilde` facts, independent of the delta. Within the joint step the child's `BoundaryFlat` is
proven by `BoundaryFlat_stepCase11` (no delta) while the child's `MvalCoh` uses the delta with the
parent's `hbf` — a clean DAG, no feedback. (Codex's Q3 leg independently confirmed `divExp` is not a
definitional alias of `Mval`.)

## Bedrock

No `sorry`, `axiom`, `native_decide`, or `unsafe` in `EngineDefs.lean` / `EngineConstruction.lean`.
Non-vacuity of the headline: for a genuine `M` (`M 0, M 1 ≥ 1`), `conOracle` at `conRoot` STEPS
(case-2, since `occ = []` at `numDiv = 0` and `widthMinUpto 1 = min(M0,M1) ≥ 1 > 0`), producing a
non-trivial tree whose leaves carry real analytic divisors, with `divExp` genuinely accumulated
(proven `= Mval` via `MvalCoh`, not aliased). Codex confirmed the standalone predicate admits
vacuous/fabricated models (leafless tree; `numDiv=0` leaf; extensional `divExp`), but those are
fenced by the actual construction and by `CanonicalResolution`'s other conjuncts (`ChartBridge`,
attainment) — not this spine's concern. Build-greenness taken as given (controller-probe-verified,
clean-three); no `.olean` present in this review worktree, so I did not re-run `#print axioms`.

## Decorrelated Codex summary

Codex (gpt-5.6, xhigh, hypothesis-withheld) independently: (Q1) C1 is the safe `P ⊆ Adm` direction,
no smuggled completeness (explicit `M=(2,2,2)` countermodel omitting `minAdm`'s minimizer `(1,0)`);
(Q2) C2+C3 = value-support equality, not multiset/index — docstring "EXACTLY the sublist" is stronger
than the predicate, harmless for set/min use; (Q3) no definitional-alias vacuity (divExp independent,
`MvalCoh`-proven), predicate is extensional; (Q4) no t̃>0 re-admission (C1 analytic-only, C2/C3
t̃=0-gated), `.toNat` not a loophole (`Mval ≥ 0` on `Adm`). Fact/inference split preserved: Codex did
not re-run the 847-instance batteries or the 17-of-19 count; conclusions follow from the definitions.

## Findings ranked (all report-only, none blocking)

1. **[precision, low]** EngineDefs:205 docstring "EXACTLY the t̃=0 sublist" overstates
   `IsFullMonomialization`'s C2+C3, which give value-support (set) equality, not a multiset/index
   sublist. Suggest wording that scopes it to value/support (the construction itself is a genuine
   sublist; the predicate forgets multiplicity). No soundness impact.
2. **[precision, low]** Headline `0 < L` is not strictly forced (vacuous at `L=0`); docstring frames
   it as a needed guard. Benign (safe-direction restriction).
3. **[wording, low]** EngineConstruction:724 "is just M⁽¹⁾" — drop the filler `just`.
