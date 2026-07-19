# Carrier interface — t05 checkpoint review (of coverage-t08's proposal)

*Reviewer: `architect-t05` (carrier co-design, the disposer to coverage's proposer). One pass,
confirm-or-counter per section, + the two flagged positions (§8 field-home; the centerSplit
reassignment). Grounded in: `carrier-interface-proposal.md`, `cert-psi-mix.md` (R-b), the
CARRIER-ADJACENT REUSE INDEX (banked-families.md), the ψ-cert structural fact relayed by the
controller. Review-then-hold: elder gate fires after; the build follows ratification.*

## Verdict: CONFIRM the R-b interface shape, with ONE structural counter (§8 → sibling record, decisively) + one AGREE (centerSplit → coverage). The counter RESHAPES the division of labour (§6) — my carrier shrinks to DATA exposure; the per-pivot geometry is coverage's.

---

## The two flagged positions

### §8 (field-home) — POSITION: **sibling `GeoChart` record, NOT a `ChartSubst` extension.** Decisive.

The load-bearing reason is the ψ-cert structural fact (T1/T2): the ledger (spine) tree has ONE edge per
ledger-child, but the geometric fan-out is pivot-indexed:
- the case-1(1) ledger edge ↔ EXACTLY the `u`-chart — ONE `localSub` (β_u, the genuine `u`-blow-up);
  a single per-edge field carries it fine;
- BUT the case-1(2) / case-2 ledger edges ↔ the `d_center` d-FAMILY — one `β̃_e` PER PIVOT
  (`d_center` of them, pivot-indexed). **A single `ChartSubst.localSub` per edge cannot faithfully
  carry a pivot-indexed family** — it would collapse `d_center` charts to one, the exact undershoot the
  corrected type exists to fix (`cert-cov-rungs12`, R2 probe).

So the per-pivot geometry MUST live off-spine, in a `GeoChart` record consumed by `geometricLeafPaths`
(which fans out the pivots). This:
- honors the sub-gap-3 pin (fan-out is atlas data, never spine edges; `StepRel` stays the quotient);
- keeps `ChartSubst`/the spine provably chartMap-blind — no spine type change, no spine re-elaboration,
  no MANDATORY elder gate on a `ChartSubst` type change;
- matches coverage's lean and the corrected type (atlas = `leaves t_geo`, not spine `leaves`).

**Correction to the reuse-index line "the carrier populates `ChartSubst.localSub = β̃_e`"**
(banked-families.md (a)): that is faithful ONLY for the case-1(1) `u`-edge (one `localSub`). For
case-1(2)/case-2 the per-pivot `β̃_e` cannot go on the single spine edge — confirming the sibling
`GeoChart`. The spine `localSub`s stay `id` (spine path-fold STRUCK moot, already ratified); the
geometric fold is `geometricLeafPaths` over the `GeoChart`s, NOT the spine `leafPaths`.

### The centerSplit reassignment — AGREE.

`centerSplit = paramsEquivFlat ∘ center-permutation` (§1) is pure finite-coordinate machinery in
coverage's geometric domain (fork B: coverage owns pivotChart / the q-split / β/det). Coverage builds
the concrete `q`. My carrier exposes the **center-INDEX data** (which flat coordinates are the node's
center: the residual `d`-block entries + the `u`-pivot coord for case-1; the residual block for
case-2). No contest.

---

## Consequence: the division of labour (§6) RESHAPES — my carrier shrinks to DATA

With §8 → GeoChart (coverage) + centerSplit → coverage + the spine path-fold struck + β_e/α_e/β̃_e in
the GeoChart (coverage's geometry), the §6 "t05" items are NOT mine as written:
- "per-edge β_e/α_e/localSub_e on the construction side" → these are the GeoChart's (coverage), per §8.
- "the buildTree path-accumulator so leafOfState.chartMap = the fold" → MOOT (spine path-fold struck;
  the atlas fold is geometricLeafPaths, coverage's).

**What my carrier actually owes (the DATA coverage's centerSplit/GeoChart/geometricLeafPaths consume):**
1. per-node `d_center` — ALREADY computable from existing spine fields: case-1 `= e.subst.runLen *
   node.resCols + 1`, case-2 `= node.resRows * node.resCols` (StepData `resRows`/`resCols` + ChartSubst
   `runLen`). Likely just a named helper, if not read directly.
2. per-node center-INDEX selector (which `Fin (flatDim M)` coords are the center) — the one possibly-new
   piece; relates to `divCoord` (sub-gap-1, DONE) + the residual-block flat layout. Needs a design
   check: is it derivable from the node's ledger + `paramsEquivFlat`, or does it need a carrier helper?
3. the pivot enumeration (the `d_center` pivots per node) — falls out of (1) (`Fin d_center`).

**Budget implication (honest):** if the center-index (2) is derivable from existing fields, my carrier
is a SMALL bounded arc (a helper or two exposing d_center + the center-index) — well within budget. If
coverage can read it all off the existing spine (StepData + ChartSubst + divCoord + paramsEquivFlat),
my carrier is essentially a confirmation + a thin helper, and coverage owns the rest. Either way this is
FAR smaller than the §6 "populate all per-edge geometry + path-accumulator" framing — the reassignments
move the substance to coverage's geometric lane. I flag this so the elder gate + sequencing reflect the
true (small) carrier size; no budget concern on my side for a data-exposure arc.

---

## Per-section confirm/counter

- **§0 (why this shape):** CONFIRM. R-b, flat atlas, fan-out in the atlas — all settled + consistent
  with cert-psi-mix + the ratified type.
- **§1 (concrete q / centerSplit):** CONFIRM the shape; AGREE the reassignment to coverage (above). The
  center coords per case are page-correct (`page-pin-centers`).
- **§2 (per-edge R-b fields):** CONFIRM the R-b factorization `localSub_e = β̃_e = β_e ∘ α_e⁻¹`, `α_u =
  .refl`, `α_d =` inverse-Schur unipotent (matches cert-psi-mix §R-b). COUNTER on the HOME: these are
  GeoChart fields (per §8), NOT spine `ChartSubst` — and per-pivot, not per-ledger-edge.
- **§3 (`d_center` family / `hbij`):** CONFIRM. Full-family emission via `geometricLeafPaths`, off-spine
  (sub-gap-3). `d_center` computable (above).
- **§4 (`geometricLeafPaths`):** CONFIRM it's coverage's sibling recursion (different `acc` payload than
  `leafPaths` — the reuse index CQ2 + the recalibration agree). Clause (D)'s two-sided honesty test is
  the right anti-vacuity instrument.
- **§5 (what coverage consumes):** CONFIRM. Note `LeafPullback` is o5/analytic (not coverage geometry),
  correctly placed; the `pivotChart` det atom (§7.3) is a real owed piece.
- **§6 (division of labour):** COUNTER — reshaped per the two positions (above): my carrier = DATA
  exposure (d_center + center-index + pivot enumeration); coverage = ALL the per-pivot geometry
  (centerSplit, GeoChart β_e/α_e/β̃_e, geometricLeafPaths, the fold, the 3 Props, clause D).
- **§7 (owed Lean pieces):** CONFIRM all four as coverage's (centerSplit, α_e frames + β̃ identity,
  pivotChart det atom, geometricLeafPaths). Add: my (small) carrier helper for d_center/center-index if
  not directly derivable.

## For the elder gate
- The §8 counter means NO `ChartSubst` type change → the "ChartSubst type change would make the gate
  mandatory" trigger does NOT fire; the gate rules on the GeoChart shape + the division-of-labour
  reshape instead.
- One design check to resolve at/after the gate (owner: whoever builds the center-index): is the
  per-node center-index selector derivable from the existing ledger + `paramsEquivFlat`, or does it need
  a carrier-side helper? This determines whether my carrier arc is "a thin helper" or "essentially
  already exposed."
