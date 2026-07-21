<!-- COMPASS — the fork-history (WHY + how-we-know). Charter.md is the invariant core (WHAT); read it FIRST.
     Elder is sole author; controller commits. May grow; compacted deliberately. Target ≤2 pages.
     COMPACTED 2026-07-20 (post-checkpoint) to the CURRENT frame: objects A–E, ideal-level.
     The retired chart Engine's internals are HISTORY (journal ticks ≤340, RETIRED.md, git), not truth. -->

# Compass — aoyagi-engine

## The live question (current frame)
Build **Aoyagi's resolution machinery as reusable objects A–E at full generality** (charter §1). The
RLCT LOWER bound is **IDEAL-level** — the chart route is a proven category-dead end (F1). The
destination `aoyagi_learning_coefficient` unconditional is a corollary/test, not the objective.
**The hard part, named and front-and-centre: the COUPLED corank ≥ 2 resolution** (Object B, width ≥ 3) —
the case the chart drifts, the MVP shortcuts, and the per-layer recursion were all routes AROUND, each
failing late. It holds its own lane and is never scoped to a footnote.

## The load-bearing strategic picture — the RLCT lower bound is a three-part ideal composite
1. **RESOLUTION [Object B]** — the blow-up monomialises `⟨∏C⟩ = ⟨diag(b)⟩`; the `b_i` are monomials in
   the exceptional coords. `rlct⟨b_i⟩ = ½·min M_{s,k}` is the min over THESE divisors.
2. **LEMMA 1 — ideal-RLCT domination [Object A, category-NEW, Mathlib-absent]** — `⟨∏C⟩=⟨b_i⟩ ⟹
   Σ(∏C)² ≍ Σb_i²` locally ⟹ integral comparison (worked.tex:153–158). REPLACES the category-wrong
   chart-diagonalisation. The `≤`/`≥` structure is elementary in outline; **the full-generality Lean
   statement (both directions) is the workhorse to build** (do NOT pre-price it "elementary" — see counsel).
3. **DIVISIBILITY-CHAIN NORMAL CROSSING [Object B, established]** — `b_1|b_2|…|b_M` (worked.tex:484) ⟹
   `Σb_i² = dominant²·(unit ≥ 1)` per leaf ⟹ `rlct = ½·min` directly. Claimed toric-trivial (single
   dominant monomial) — VERIFIED only in the clean regime; UNVERIFIED at coupled corank≥2.
Objects C (monomial-ideal ½·min) and D (codim = minAdm = cCodim, θ, perm-inv; banked) feed the read-off.

## Settled forks, WITH WHY
**F1. The chart route is a GOAL-LEVEL category error — why we are ideal-level (SOUND, settled).**
Every `(∏C)ᵢⱼ` is a nonzero poly; any a.e.-injective/det-1 chart has open image; a nonzero poly is ≢0
on a dense open set; exact diagonalisation forces ≡0 (a non-open, det-0 projection). So NO det-1/
a.e.-inj map diagonalises the loss on an open set. Survived long because the gap is det-1 (invisible to
Jacobian + cover); only the value LOWER bound sees it — the value lane + decorrelated pnp caught it, the
order-blind det lane would have shipped green over an unbuildable spine. Witnesses:
`cert-full-value-walk §6` (+6 batteries), `cert-exactly-diagonal-mechanism`, `cert-collection-lemma`.
CONSEQUENCE: the ideal reframe is forced; the chart Engine is RETIRED (charter §3, RETIRED.md).

**F2. `⟨∏C⟩ = ⟨diag(b)⟩` transfers as an IDEAL fact — the salvaged truth (SOUND).** Unimodular Q,P are
ideal-preserving (worked.tex:375–390), a standard fact; so the InvVal3/prefix/b-chain REDUCTION the
chart route computed (Q1-verified end-to-end at 4 M's) is the IDEAL identity, NOT a chart identity — it
transfers to Object B unchanged. (The specific `diag(b)` SHAPE at COUPLED instances is part of the B
frontier, not yet verified — F4.)

**F3. Clean (uncoupled, width ≤ 2) telescopes — VERIFIED; the honest boundary (SOUND, scope-bounded).**
At (2,2,2,2): the per-chart ideal reduction is an EXACT symbolic matrix identity at depth-2 AND depth-3;
`δ=ρ` is DERIVED from the blow-up (mechanism depth-blind); RLCT 3/2 = ½·min. Controller-verified against
the batteries. EVIDENCE HYGIENE (do not inherit the gap): cite the PEEL IDENTITY (exact) + `structure_v2`,
NOT "5 batteries" — `ideal_equality_rigorous.py` exits 0 while PRINTING a superseded free-δ intermediate
(exit-0 ≠ content-true). BOUNDARY: (2,2,2,2) is all-width-≤2, the CLEAN shallowest instance, exercises NO
coupling. "Tractable in general" is EARNED only here; coupled width≥3 is the gate for any tractability
pricing. FIRST LANDING = clean recursion; NEXT PROBE = coupled diag(b) at width≥3 (load-bearing).

**F4. The coupling at corank ≥ 2 is REAL — flatten-style decompositions provably break (SOUND
obstruction; Object-B constraint).** At corank≥2 the carried monomials couple (the `b_i` share divisors
via `b_1|…|b_M`). A per-row-multiplicity FLATTEN — treating each `b_i`'s exponent independently — loses
the shared-divisor structure and returns the WRONG min. Witnessed exactly: `minAdm(3,3,4)=8` is achieved
COUPLED-ONLY (`battery/g-coupled-binding-334.py`; the (3,3,4) coupling = two coupled/equal divisors,
load-bearing); a flatten breaks (`battery/g-delta-flatten.py`). WARNING: any flatten/split of the coupled
ideal is a dead route — Object B must reproduce the coupled diag(b), not decompose it row-wise.

**F5. Aoyagi is the fidelity touchstone; Q2 LOCKED (tick 421).** The coupled resolution is her own
Cases 1&2 (read from the paper images; worked.tex references them): transcribe HER choice + verify her
claimed monomialisation — not our invention. At each route/statement ask "within Aoyagi's scope?" and
cite the page; a deviation is a DOCUMENTED typo-fix, never a silent Lean-convenience.

## Paper-fidelity ledger (documented Aoyagi typos; the mechanism stands)
- **Def-3 broken** (verified typo) — use the geometric `½·min_t Mval(t)`. Witness `battery/g-def3-broken.py`.
- **Lemma 1 direction**: worked.tex:156 prints `≥`; the correct/used direction is `≤` (`rlctAt_mono`) —
  harmless for the equality use.
- **T-profile total-comparability (NEW paper defect, thread-31; Def-3-class).** Aoyagi's claim that the
  carried `T`-profiles are totally comparable is FALSE: at widths (2,2,1,1) the profiles (1,1,1) and
  (2,1,0) are componentwise-incomparable, both with Mval = 1. Codex-found, battery-verified
  (`theory/aoyagi-2023-reproduction/g-monument-mval-instances.py`; controller+elder re-runs green). The
  v4.2 record is structurally immune: `hchain` orders the threshold-side b-monomials (`bexp`), never
  profiles — profiles have NO record field, so the false claim has no formal representation to corrupt.
  The b-chain `b₁|…|b_M` is Aoyagi's own invariant and SURVIVES; only the profile-comparability reading
  dies. Recorded so the monument seat does not transcribe it.
- **Case-2 raw-width vs running-min — CLOSED (thread-31; was UNCERTAIN).** Resolved structurally: the
  ideal-route record carries NO rank-profile label field (only `bexp` + `jac`), the exponent accumulation
  is governed by the RUNNING-MIN, so the p.20 raw-width head-reset label has no representation that could
  corrupt `hlb`/`hattain`; at the witness widths (2,2,3,2) the defect divisor is NON-BINDING. The earlier
  hypothesis that the fork dissolves in the ideal route (no separate T-label) is CONFIRMED. Witnesses:
  `g-monument-mval-instances.py`, `verify-case2-rawwidth-defect.md`,
  `threads/31-monument-construction/certificate.md` §d. Image residual CLOSED (elder pass
  2026-07-21): p.20 confirmed — raw-width head-reset printed, Case-1(2) inherits (p.17); worked.tex (T-E).
- **Realization "profile-set ⊇ Adm" (Engine-tree artifact; surviving kernel banked).** The paper's
  implicit stratum-completeness (the resolution realises every admissible profile) is FALSE for the
  built tree — but this was a property of the Engine's leaf-profile-set, which does NOT exist in the
  ideal route (it reads min over the `b_i` directly). The SURVIVING TRUTH: the min IS achieved
  (`minAdm ∈ P`, proved), so `rlct = ½·minAdm` stands = Object D (`minAdm=cCodim`, banked). Ledger:
  `verify-realization-gap-defect.md`. Not carried as a live constraint; recorded so the truth is not re-derived.

- **Per-step principality — the invariant SPLITS (thread-34; elder delta-ratified 2026-07-21).** The
  sketched per-step `PrincipalInv` (divisibility + Bézout bundled) is statement-FALSE at the root and
  every interior state: with a pending tail (S<L) every quotient vanishes at the deepest point, so a
  Bézout identity forces 0=1 by continuity; principality is BORN terminally (S=L ∧ J≥1). This is the
  paper's own structure (elder image-verified: p.15 inductive statement = the ideal identity WITH the
  pending tail, never principality; principality only at the terminal p.22 display; the pnp's cofactor
  Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹ reproduces the printed P of pp.18/21 verbatim). The formal shape:
  per-step `StepInv` (region-quantified, divisibility-only, chain) + terminal `terminal_bezout`;
  `PrincipalInv` assembled terminally at the path fold. Recorded as a fidelity CORRECTION toward the
  paper (elder D4). Witnesses: `threads/34-case1-invariant/` (certificate + 3 batteries, controller
  re-run green); corroboration thread-28 + worked.tex:659.

## The honest gap — coupled-B, stated plainly (front-and-centre)
- **KNOW:** clean regime exact (F3); `⟨∏C⟩=⟨diag(b)⟩` transfers as an ideal fact (F2); the coupling is
  real and flatten breaks (F4); minAdm = cCodim banked (D); the category error forces the ideal route (F1).
- **LANDED (strike wave 1, sorry-free at tip):** (a) Lemma 1 both directions + weighted forms,
  junk-guarded [A]; (c) the guarded S2 monomial rule — `DivChain` excludes the coupled counterexample
  [C]; the corollary reduction (linear flatten + m.p.-homeo invariance + homogeneous global=local-at-0,
  `GlobalHomog`). D banked earlier.
- **DON'T HAVE (the remaining new math):** (b) the COUPLED diag(b) ATLAS at corank≥2 — B's 4 leaves +
  `exists_coreResolution` (the monument; thread-31 certificate is the playbook); (d) order ρ / zeta-pole
  [E, deferred per §1-E].
- The coupled case is Aoyagi's ACTUAL content and the historical dodge-point. BUILD it; do not route around
  it, do not pre-declare it tractable. This gap is the thing the compaction must keep unmissable.

## Standing counsel (rising-sea)
- **BUILD THE RIGHT OBJECT — DO NOT MINIMUM-VIABLE IT (operator, 2026-07-20; the elder's own
  recalibration).** The whole α-chart programme tried to reach the lower bound WITHOUT building the
  ideal machinery Mathlib lacks; the category error is the PROOF a chart cannot dodge it. The elder ALSO
  drifted — characterising the follow-up as "just Lemma 1, toric-trivial, elementary ≥," an unverified
  clean headline of exactly the falsified shape. DURABLE: build the RLCT-ideal-and-resolution library as
  a proper STANDALONE GENERAL library (rlct as ideal/germ invariant; Lemma 1 both directions +
  ideal-inclusion monotonicity; monomial-ideal RLCT / Newton in full generality; the resolution CoV; the
  analytic/zeta foundation for ρ) — to full generality from the START, not a patch to unblock a headline.
  DLN-specific simplifications (toric-triviality, the explicit tree) FALL OUT downstream; scoping the
  object BY them is the error. NEITHER avoid the hard part NOR avoid the large build.
- **KILL-SET ADEQUACY.** Every pre-committed kill set must exercise each KNOWN failure mechanism
  (interior-bottleneck width-drop; L≥4 non-monotone depth). A green pre-committed battery is NEVER
  sufficient for a universal claim — the gate reads a DECORRELATED hunt. Provenance: "clean telescopes"
  ⇏ "coupled tractable" is the shallow-instance confound that has bitten this expedition repeatedly (an
  "== Adm at all 4" kill sat green while false at 84/351 — all 4 instances bottleneck-free).
- **MATHEMATICAL SENSE OVER CASE ANALYSIS (operator).** Understand the mechanism at conceptual altitude
  (iterated blow-ups monomialising the ideal, ONE uniform idea whose "cases" are charts) THEN transcribe;
  build the uniform object and DERIVE the cases. When a case-grind feels authoritative but shapeless, stop.
- **MATHEMATICAL NECESSITY IS THE BAR, not Lean-build progress (operator).** Judge a shape by whether the
  MATH necessitates it; Lean cost is a secondary tiebreaker. When a ruling leads with "zero ripple /
  unblocks the build," STOP and re-derive from the math.
- **DECORRELATED GATES.** In-house nice-instance witnesses MASKED gaps repeatedly (resRank fold; srcBox
  boundedness; the realization gap — caught by pnp's independent scan, not the battery). The GATE reads an
  independent seat, never the builder. An in-file witness is necessary, never sufficient.
- **Survey banked state before commissioning anything** (3 redundant commissions on a prior run). Reuse
  dev's determinantal RESULTS for D; keep the RLCT-ideal work on the DLN side (the cite lives there).

## Landmarks (A–E frame; ≤9 — why these)
- **Object A** (Lemma 1 ideal-RLCT invariance) — the category-NEW workhorse; the missing half of the lower bound. LANDED (wave 1).
- **Object B** (`⟨∏C⟩=⟨diag(b)⟩`) — the geometric heart; **coupled corank≥2 = the hard part**, holds a lane.
- **Object C** (monomial-ideal ½·min) — LANDED (guarded S2; `DivChain` boundary honest).
- **Object D** (codim = minAdm = cCodim, θ, perm-inv) — banked in `Core` (+ dev merge).
- **`cited_aoyagi_lower_ax`** — the kill-target; the destination made concrete (prove via A+B+C, delete).
- **category-no-go (F1)** — why the ideal route; the retired chart Engine's tombstone (RETIRED.md).
- **(2,2,2,2)-clean-telescoping** — the verified clean landing (peel identity + structure_v2).
- **(3,3,4) / (3,3,2,2)** — the coupled frontier probe (minAdm=8 coupled-only).

## History — retired chart Engine (POINTERS ONLY; not truth)
The chart Engine's internal design is JOURNAL/GIT HISTORY — do NOT rebuild against it. Retired as
DEAD-ROUTE ARTIFACTS (chart-atlas constructions with no ideal-frame analogue; their frame-independent
CONTENT lives in A–E, above): `ChartBridge` / `region_glue` (the chart→integral
interface → replaced by A + C + the resolution CoV); `IsFullMonomialization` the PREDICATE
(EngineDefs:268) is ledger-COMBINATORIAL (divExp = Mval of admissible profiles) and is SALVAGED into
the Object-B adapter (mon-rec, elder-ratified, conditions C1/C2) — only its bundle-role inside
`CanonicalResolution`/`ChartBridge` is retired; `terminalExponents` / `divExp` / `divProfile` /
`genDivExp` / `divTilde` (per-node exponent-ledger fields → the `b_i` exponents / min = minAdm, Objects
C/D); the resolution-tree carrier + edge-labelled sharing + `StepRel` / `stepUpdate`; the Q5
banked-RLCT-transport route; the full-mechanism R1–R7 rungs; the coverage theorem + theorem4-localization
+ region-glue division-of-labor; the concrete monomialization oracle; diagonal-normalization; the α-atlas
`LeafPullback` / `geoAtlasNorm`; the two-lane / hbox / mint-PR endgame. See journal ticks ≤340, RETIRED.md.
SALVAGE correct kernel-checked det/tree pieces into Object B by re-importing the specific module, never by
resurrecting a chart hole (charter §3).
