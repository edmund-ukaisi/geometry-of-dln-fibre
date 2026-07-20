# Cert — T1 faithful-carrier + region_glue discharge (consolidated review)

Reviewer (independent, consolidated fidelity + soundness + μ-spine + bedrock/wording).
Branch `expedition/aoyagi-engine--revt1`, worktree `/home/ubuntu/workspace/rev-t1-wt`.
Date 2026-07-18. One round.

**VERDICT: scoped-VALIDATE.** The T1 faithful carrier (commits 4211a714b → 31a7bad6f →
904cc2921 → e6f8ac6b7) and the `region_glue` discharge (63753153c) are sound and faithful to
the banked spec and the page-pinned Aoyagi rules. The T-update matches the page rules EXACTLY
(my own `decide +kernel` re-derivation + a decorrelated Codex read agree to the component); the
μ-spine + discharge landings are axiom-clean exactly as documented. **T2 (recursion assembly)
opens.** Findings are all report-only prose / map-currency + three forward constraints on the T2
interface (§Findings); none block T2.

## Evidence base

- **Full-chain build** (fresh reviewer worktree, empty `.lake`): a scratch module importing
  `EngineConstruction`/`EngineObligations`/`EngineDriver`/`CanonicalWitness224`/`CoRank2Spike`
  built green — `Build completed successfully (8621 jobs)`, `EXIT 0`. This force-elaborates the
  engine + glue + Validate chain (no name-clash; no stale-olean masking, the module was new).
- **My own forced `#print axioms`** (fresh module, so elaboration is forced per lean/CLAUDE.md):
  - μ-spine — `tildeOf_le`, `tildeOf_setTail_le`, `pendingCount_stepCase11_lt`,
    `conRel_stepCase11`, `conRel_stepAppendAdvance`, `conRel_stepRollover`, `conRel_wf`:
    **all `[propext, Classical.choice, Quot.sound]`** (clean-three, no `sorryAx`).
  - coherence/trace witnesses — `node334_merge_divProfile`, `node334_merge_coherent`,
    `node334_case2_divProfile`, `mergeLeaf_divExp`, `mergeEdge_stepRel`,
    `canonicalResolution224_arithmetic`: **all clean-three**.
  - discharge — `region_glue_of_chartBridge`: **clean-three**; `region_glue`: `[propext,
    sorryAx, Classical.choice, Quot.sound]`; `engine_box_threshold_finite`: same `+sorryAx`.
    Matches the AxCheck watch entries verbatim.
- **My own independent `decide` re-derivation** of the trace values (in the scratch; all passed,
  build exit 0): `(1,1)→(1,0)` exp `4→8`, `Mval(3,3,4)(1,0)=8`, `minAdm(3,3,4)=8`; case-2 at
  layer 1 `→(3,0)` exp `12`, `Mval(3,0)=12`; appended case-2 exp `= resRows·resCols`.
- **Decorrelated Codex** (xhigh, hypothesis withheld — given only the page rules + the Lean
  `stepUpdate`): FAITHFUL. Independently confirmed the `n.layer ≤ p.val` boundary is exact,
  `fun p => M p.succ` is the correct case-2 reset, both (3,3,4) traces reproduce, and `layer < L`
  is the correct + caller-suppliable precondition (`layer ≤ L` insufficient). Artefacts:
  `codex/t1-fidelity-{prompt,answer}.md`.
- **Re-ran cited batteries** (clean re-run reproduces headlines): `g-case11-merge.py`
  (page-16 formula on a sweep True; parent=5,J₁=2,resCols=3→11 True; child MUST be read True),
  `g-case2-exponent.py`, `g-engine-ratio-consistency.py` (minAdm(3,3,4)=8, (2,2,2,2)=3 EXACT;
  separated-leaf read undershoots OFF-chain → `IsFullMonomialization` precondition load-bearing),
  `g-minadm-groundtruth.py`.

## Item 1 — CARRIER FIDELITY vs the banked spec + the pnp rule: VALIDATE

- `divProfile : Fin numDiv → (Fin L → ℕ)` is PRIMITIVE on `StepData`/`LeafData`/`RootLedger`
  (`ResolutionTree.lean:109,134,254`) and `ConState` (`EngineConstruction.lean:52`); no stored
  `divTilde` field anywhere. `divTilde` is DERIVED (`tildeOf = min`, dite-guarded on `0 < L`,
  total, `ResolutionTree.lean:276-299` + `ConState.divTilde` `EngineConstruction.lean:60`).
  Matches the T1b/T1c spec (`t1b-execution-spec.md:9-17,61`).
- **The T-update in `stepUpdate` (`EngineDefs.lean:106-136`) matches the page-pinned rule
  EXACTLY.** `setTail T p := if n.layer ≤ p.val then n.cleared else T p` — tail iff `layer ≤
  p.val`, the load-bearing 1-indexed↔0-indexed reconciliation (Lean layer = S−1; profile index
  p ↔ tⁿ⁺¹). Verified against the pnp trace by my own `decide` AND Codex:
  - case11 `(3,3,4)` merge at layer 1 (`node334`): `(1,1)→(1,0)` (head t⁽¹⁾ preserved, tail
    t⁽²⁾:=J=0), `divExp 4→8 = 4 + 1·4`, `= Mval(1,0) = minAdm` (`CoRank2Spike.lean:91-99`).
  - case2 head-RESET at layer 1: `fun p => M p.succ` gives base `(M⁽²⁾,M⁽³⁾)=(3,4)`, tail-write
    `→(3,0)`, `divExp = resRows·resCols = 12 = Mval(3,0)` (`CoRank2Spike.lean:104-106`).
  - case12 head INHERITED via `setTail` of the parent's `divProfile mergeIdx`, dite-guarded
    (`EngineDefs.lean:129`); exponent `divExp(mergeIdx) + runLen·resCols`, dite-guarded base.
  Exponent rule `+= runLen·resCols` (case11/12) / `resRows·resCols` (case2) = `J₁(M⁽ˢ⁺¹⁾−J)` /
  `(M(S)−J)(M⁽ˢ⁺¹⁾−J)` since `resCols := M⁽ˢ⁺¹⁾−J`, `resRows := M(S)−J`. Faithful.
- `genDivExp : Fin numGen → Fin numDiv → ℕ` is a multiplicity field; `support` is DERIVED as the
  nonzero locus (`ResolutionTree.lean:286-290`, `StepData.support`). Matches the ratified
  redesign (`g-delta-flatten` — a flatten is a type error).

## Item 2 — COHERENCE (`divExp = Mval(divProfile)`): VALIDATE

Machine-checked and clean-three where claimed: `canonicalResolution224_arithmetic`'s
`IsFullMonomialization` conjunct (`divExp = (Mval M divProfile).toNat ∧ divProfile ∈ Adm`, by
`fin_cases; decide`, `CanonicalWitness224.lean:100-106`) — the arithmetic bank piece is
clean-three (my forced print). `node334_merge_coherent` (`divExp=8 ∧ Mval(1,0)=8`) and
`node334_case2_divProfile` (`Mval(3,0)=12`) decide-checks are REAL (I read them; the build's
exit-0 + my independent re-derivation confirm they pass) and match the banked `Mval`/`minAdm`
(cross-checked by `g-engine-ratio-consistency.py`, `g-minadm-groundtruth.py`).
Minor: `node334_case2_divProfile` pins `Mval(3,0)=12` but not the `stepUpdate` exponent `=12`
directly (it is `resRows·resCols=3·4`, definitional; I added an explicit `decide` of it — passes).

## Item 3 — THE CHOOSER TYPE `IsEligibleMinimalChoice`: VALIDATE

`IsEligibleMinimalChoice (s) (k : Fin s.numDiv) (runLen)` (`EngineConstruction.lean:233-236`):
in-range enforced by TYPE (`k : Fin s.numDiv`), clearing-level `s.divTilde k = s.cleared +
runLen` (= t̃ = J + J₁, `runLen` = J₁ correctly), Def-4 componentwise minimality
`∀ k' at the same level, ∀ j, divProfile k j ≤ divProfile k' j`. Matches p.15 (fix u_{s,k} with
t̃ = J+J₁ AND T_{s,k} ≤ T_{s',k'} for all t̃_{s',k'}=J+J₁). Docstring cites the
comparability-preservation finding correctly in substance ((2,2,2,2) node (3,0,1): wrong pick
`(2,1,0)` incomparable with `(1,1,1)`, minAdm 3 under both — value blind to a wrong tie-break);
matches cert-atlas-probe-2222 verdict (c). Proofs deferred to T4 with the kill-witness map
pointer (reject `(2,1,1)` at that node). Two trivial citation nits in §Findings.

## Item 4 — μ-SPINE INTEGRITY: VALIDATE (one forward constraint on T2)

All 4 `conRel` lemmas + `tildeOf_setTail_le` + `pendingCount_stepCase11_lt` + `conRel_wf` are
clean-three by my own forced `#print` (above). The lex-triple measure `μ = (L+1−S, layerCap−J,
pendingCount)` and the three descents (component 3 case11, component 2 append-advance, component
1 rollover) are sound; the kill-condition (no step drops nothing) is cleared.

**The added precondition `layer < L` on the case11 descent is correctly threaded as an explicit
hypothesis, but is NOT suppliable from `StateInvariant`** (which gives only `layer_le : s.layer ≤
L`). This is CORRECT — `layer < L` holds for every real (non-terminal) blow-up step (S ∈ 1..L ⟺
Lean layer ∈ 0..L−1, so `layer ≤ L−1 < L`); the terminal `layer = L` is where no step fires (and
`setTail` would create no tail coordinate, so t̃ could not drop). Codex concurs. **→ T2
constraint (below): the recursion body must supply `layer < L` on the case-1(1) branch; the
invariant alone does not.**

## Item 5 — THE DISCHARGE LANDING: VALIDATE

`region_glue`'s proof is the validated one-liner `region_glue_of_chartBridge (resolutionOf M)
hbridge c' hrat` (`EngineObligations.lean:94`) — binder-for-binder the shape rev-glue elaborated
(`cert-glue-fidelity.md` item 1). AxCheck watch entries confirmed by MY OWN forced `#print`:
`region_glue_of_chartBridge` clean-three (assembly not re-opened); `region_glue` `+sorryAx`;
`engine_box_threshold_finite` `+sorryAx`. **The architect's type-level `sorryAx` analysis is
CORRECT**: `region_glue`'s TYPE mentions `resolutionOf M = (monomialization_terminates M).choose`
(sorried), so the footprint carries `sorryAx` THROUGH THE TYPE while the proof term is the clean
one-liner (`region_glue_of_chartBridge` is parametric in an abstract `t`, no `resolutionOf`, hence
clean); the sole `sorryAx` source is `monomialization_terminates`. The AxCheck comment
(`AxCheck.lean` tail) documents this accurately.

## Item 6 — RAZOR-GUARD SWEEP: VALIDATE (two report-only wording notes)

The struck `EngineConstruction` razor "stores ONLY what the measure reads" is GONE (grep empty).
Scope notes are named as SEQUENCING with rung pointers, not scope-trims: support propagation →
`genDivExp`/R4 (`ResolutionTree.lean:246`, `EngineDefs.lean:101`, `StepRel` docstring
`EngineDefs.lean:153`, "named so they do not vanish"); tie-break/gap → chooser/T4 (`EngineDefs
.lean:148-153`, `EngineConstruction.lean:232`). Two residual razor-vocabulary hits (§Findings).

## Item 7 — MAP FLIPS: VALIDATE (two map-currency notes, report-only)

(a) `case-step-lemmas` faithful-flip has LANDED and is reviewed here: `StepRel` (`EngineDefs
.lean:158-162`) is the faithful ledger equality `rootLedger e.child = stepUpdate n e.case
e.subst` ∧ the both-case eligibility conjunct (in-range + t̃ = J + runLen for case11 ∨ case12).
The old childless/existential form is retired (kill-witnesses `dummyDivisor_not_stepRel`,
`vanishingDivisor_not_stepRel`, `oobSplit_not_stepRel` all present + clean, `CanonicalWitness224
.lean:196-242`). The case12 in-range guard is landed (rejects the oob-split base-drop). Map
currency: the `claims.yaml` `case-step-lemmas.prop` field (line 106-108) still describes the OLD
ideal-preservation framing, and its note says the eligibility conjunct is "landing" — now landed.
(b) The `resolution-tree` note (line 90) ends at the carrier-review round; it does not record the
T1b/T1c landing (divProfile PRIMITIVE, `tildeOf` derived, `genDivExp` multiplicity field,
`RootLedger (L)` parametrized). Both are controller map updates; non-blocking.

## Item 8 — BEDROCK / WORDING: VALIDATE

Banned-wording grep clean across the six files (no honestly/importantly/fundamentally/simply/
just/clearly/obviously/…). Names = content (`RootLedger`, `IsEligibleMinimalChoice`,
`stepUpdate`, the kill-witness names). Docstrings are one-line-ish and object-level.

---

## Findings (most severe first — all report-only or forward-looking; none block T2)

**F1 (T2 interface constraint — NOT a defect).** `conRel_stepCase11` / `pendingCount_stepCase11
_lt` require `s.layer < L` AND `hi : s.cleared < s.divTilde i`. Neither is derivable from
`StateInvariant` (which gives `layer ≤ L` only). T2's case-1(1) dispatch must supply BOTH:
`layer < L` from "we are in a live layer" (holds S ∈ 1..L), and `hi` (target pending) from the
eligibility conjunct `t̃ = J + runLen` WITH `runLen ≥ 1`. **`runLen ≥ 1` is the deferred gap
condition** (`StepRel` docstring, "the encoding takes `runLen` as given"): `IsEligibleMinimalChoice`
does not currently require `runLen ≥ 1`, so with `runLen = 0` the "eligible" divisor has t̃ =
cleared (not pending) and the descent's `hi` is unfillable. Flag for the T2/T4 interface: the
chooser must establish `runLen ≥ 1` (equivalently t̃ > cleared) to feed the case-1(1) μ-descent.
Soundness of what LANDED is unaffected — the lemmas are guarded by explicit hypotheses.

**F2 (fidelity carry-forward to T2, low severity — consistent with the current cert).** case12
keeps the parent divisor's exponent/profile UNCHANGED and appends the new pivot (`EngineDefs
.lean:124-130`: `numDiv+1`, `divExp := Fin.snoc n.divExp …`). Whether Aoyagi's case-1(2) chart
ALSO transforms the parent `u_{s,k} → u'_{s,k}` (reducing its exponent) is NOT exercised by any
positive witness (only the oob-rejection). This matches the pnp cert's INFERRED "divisor
persistence after Case-1(2)" (cert-atlas-probe.md Codex "most likely wrong" flag: persistence is
inferred from the b-chain, not page-pinned). Not a new break; pin it when T2 builds a real
case-1(2) node with a passing trace witness.

**F3 (precision, report-only).** `EngineConstruction.lean:18-19` lists `runLen` among "Derivable
data (`resRows`/`resCols`/`runLen`/`depth`/`minAdm`) … computed from `M`, `S`, `J`." `runLen` =
J₁ is determined by the divisor-profile clearing-level occupancy (the gap to the next occupied
t̃), NOT by M/S/J alone — indeed the chooser takes it as an explicit parameter precisely because
it is state-dependent. Recommend dropping `runLen` from that list (the other four are genuinely
M/S/J-derivable). Non-blocking prose.

**F4 (razor-vocabulary, report-only).** `ResolutionTree.lean:76` (`jacPow` docstring): "no
obligation reads `jacPow`, so it may be corrupted without changing the certificate." This is the
retired razor's vocabulary on a construction field. The field IS carried and the Jacobian content
lives in `LeafJacobian`'s `Dβ` (fork-8 area-formula route), so the statement is factually true,
but "may be corrupted without changing the certificate" invites the struck attitude. Recommend
rewording to the object-level fact ("the leaf Jacobian is pinned by `LeafJacobian`'s `Dβ`, not
this ledger"). Non-blocking.

**F5 (citation nits, trivial).** (i) `EngineConstruction.lean:230` attributes the
total-comparability invariant to "p.14"; per the pnp page-pins the invariant is p.15 (p.14 is
Def 4, the order). (ii) The (2,2,2,2) wrong-pick→incomparable finding is cert-atlas-probe-2222
verdict (c); the docstring labels it "pnp-atlas verdict-2" (which is the L≥3 necessity). Substance
is faithful in both; labels are slightly off. Non-blocking.

## Constraints the verdict hands to T2 (the recursion assembly)

1. **Supply `layer < L` on the case-1(1) branch** — not derivable from `StateInvariant`; comes
   from "in a live layer" (F1).
2. **Supply the μ-descent `hi` (target pending) from eligibility + `runLen ≥ 1`** — the chooser /
   gap condition must establish `runLen ≥ 1` (F1).
3. **Pin case-1(2) parent handling** with a positive trace witness when a real case-1(2) node is
   built (F2).

## Scope

This certifies the T1 carrier's fidelity to the banked spec + the page rules, the coherence
decide-witnesses, the chooser TYPE, the μ-spine axiom-cleanliness, and the `region_glue`
discharge landing. It does NOT certify the T2 construction (`monomialization_terminates`) can
build a tree satisfying `CanonicalResolution` (the recursion assembly — the next rung), nor the
T4 propagation/chooser PROOFS (deferred, mapped).
