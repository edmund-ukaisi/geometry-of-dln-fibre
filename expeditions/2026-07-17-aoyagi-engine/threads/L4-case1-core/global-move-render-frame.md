# The global-move render frame (#74) — L4D's restate (gate-PASSED) + controller deltas

**Status**: the turn-key frame for the (i)-(iv) re-architecture render. L4D's restate passed the
controller's gate 2026-07-23 with two deltas (§3). Executor: a fresh render seat (**seat-GM**);
L4D stays def-owner consult. Both design gates were green before this frame existed: the elder's
§8 ruling (`capstone-object-ruling.md`) + pnp's cleared-StepInv soundness check (ee527be2c —
raw FAILS / cleared HOLDS on archetype + wide + double-boost).

## §1 L4D's restate (verbatim, 2026-07-23)

> WHAT STAYS RAW (§8 boundary, untouched): the shear data
> (edgeShearRaw/blockShear/canonNormalizationOf/blockBlowupMap),
> buildTree/conOracle/IsRealBranch/termination/OracleInv, AND the raw fold trio
> foldG/foldB/foldResid themselves (they remain — the F-side of the Q₁-lift). Nothing in
> MonumentAtlas's shear/oracle layer changes.
>
> THE CLEARED OBJECTS (built ON CAPR's substrate — couplingClear/couplingCoords/sourceClearedResid
> are CAPR's primitives; I do NOT duplicate them): the cleared fold trio = the raw trio precomposed
> with CAPR's `couplingClear` (pnp's "source-clear precomposed then blow-up path", (A)-primary):
> sourceClearedResid = foldResid∘couplingClear (CAPR, exists) + foldG_cleared := foldG∘couplingClear,
> foldB_cleared := foldB∘couplingClear (NEW, my lane). Consequence I lean on: the cleared StepInv
> identity `coreGen(foldG_cleared u)=∑ q·foldB_cleared·sourceClearedResid` is the RAW StepInv
> evaluated at couplingClear(u) — true wherever raw is; the NEW content is the DIVISIBILITY
> (foldB_cleared | coreGen∘foldG_cleared) now HOLDS at case11 because couplingClear sets the
> coupling to 0, killing the remainder (pnp ee527be2c, all witnesses).
>
> FoldStepInvAt-on-C ((i) core): a cleared invariant over the cleared trio (both conjuncts: ∃q
> cleared-StepInv + Deg1SupportedSlot of sourceClearedResid). FLAG: current FoldStepInvAt lives in
> MonumentAtlas (single-writer). I define FoldStepInvAt_cleared in my lane (or CAPR's substrate
> module), NOT editing MonumentAtlas; you wire/relocate at merge. Summit consumes the cleared
> invariant; the Q₁-lift (iv) bridges rlctGlobal(∑foldResid²)=rlctGlobal(∑sourceClearedResid²) at
> the payoff → destination statement character-unchanged.
>
> PER-CASE APPEND SPLIT (BLOCKER 1, (ii)+(iii)): `stepInv_child_delta1_append` re-derived on the
> cleared trio, consuming `sourceClearedResid_stepMap_eq_pivot_mul` (CAPR) + the cleared transports
> `sourceClearedResid_extend_delta1/delta0` (couplingClear/quot & couplingClear/stepMap
> commutations — (ii), NEW). case11 feeds the cleared boostReady Deg1; case12 feeds the cleared
> cover route (deg1SupportedOn_center_of_hslot on C — (iii)); δ=0 = stepInv_child_delta0 on C
> ((iii)). All produce cleared-StepInv. The wall/case1_conjA/case1_preserves_stepInv' re-point to
> the cleared invariant.
>
> SUCCESS CRITERION (my two consumer shapes, pnp-verified): (1) cleared StepInv shape, pivot factor
> in foldB_cleared; (2) child↔parent commutation. pnp cross-check: my per-step def lands → pnp
> re-verifies vs its natural precompose form.

## §2 The faithfulness criterion (elder delta, relayed to L4D pre-gate)

The cleared-fold def need only be a **faithful** cleared fold — matching the certificate's object
up to CAPR's `couplingClear` precompose — not a bit-identical transcription of pnp's natural form
(pnp: "the divisibility restoration is def-agnostic"). The gate that confirms *faithful* is
**pnp's cross-check of the exact rendered def against the natural precompose** — a NAMED
render-gate item (the def-fidelity anchor; `sourceClearedResid_eq_restrict`'s rfl-tightness
generalized to the whole cleared trio). Run it at def-stabilization: post-SPECIFY, pre-proof-grind.

## §3 Controller gate deltas (additions, not corrections)

1. **The region obligation — make it a STATED lemma at SPECIFY.** The consequence in §1 ("the
   cleared identity is the raw identity evaluated at couplingClear(u)") silently needs
   `couplingClear` to map the region of the cleared statement into the raw statement's region
   (`foldRegion`). Plausible (the region pins shear/pivot coordinates; couplingCoords are
   below-pivot cleared-column leaves), but it must be an explicit SPECIFY item — either
   `couplingClear` maps `foldRegion` into `foldRegion`, or the cleared statements are stated on
   the preimage — never an implicit assumption. Same for the continuity transport
   (q_cleared = q∘couplingClear needs couplingClear continuous into V).
2. **(iv)'s landing shape is a SPECIFY decision.** The Q₁-lift bridge
   (`rlctGlobal(∑foldResid²) = rlctGlobal(∑sourceClearedResid²)`) must appear as a NAMED Lean
   statement in this unit; whether it lands proven (the certificate §7.8 has the route) or as a
   named sorry-frontier with a map comment is decided at SPECIFY + the elder's delta — not
   discovered mid-grind.

## §4 The named render gates (in order)

0. **Mini-restate** (seat-GM → controller): short own-words confirmation of the boundary, the
   def shape, the append split, and the gates — the transplant-loss check.
1. **SPECIFY** (defs + full statement list, NO proofs): the def block verbatim → controller →
   **pnp def-fidelity cross-check**; the SPECIFY doc → controller → **elder delta-read** (the
   elder verifies: cleared defs match the certificate object; FoldStepInvAt + the StepInv chain
   restated on C; survivors untouched; Q₁-lift wired from rlctGlobal; consumers re-pointed;
   census/axiom-cone clean with sorryAx only at the named cleared-content frontier).
2. **Proofs** (only after both gates green).
3. **Exit gates**: full build green; forced `#print axioms` on the payoff root
   (= `[propext, Classical.choice, Quot.sound]` + expected sorryAx accounting); census delta
   accounted named-frontier-by-named-frontier; cordon (no `native_decide`; `decide +kernel`);
   lane pushed; report.

## §5 Substrate + ownership

- Base: `origin/expedition/aoyagi-engine-CAPR` @ 1388f6192 (canonical + SourceClearedResid.lean
  + the reshaped MergeBoostSplit.lean; canonical has NO Lean commits the lane lacks, verified
  2026-07-23).
- `SourceClearedResid.lean` = CAPR's file (single-writer): do not edit; request missing
  primitives through the controller. `MonumentAtlas.lean`, `DLNFibre.lean` (aggregator) =
  controller-only. New defs go in a NEW module (suggested: `ClearedFold.lean`).
- CAPR's STEP-3 (the INV spine) lands on the same lane in parallel; the controller reconciles at
  the integration merge (#73/#74).
- L4D = def-owner consult (append hard-wiring, cleared-trio composition, FoldStepInvAt-on-C
  shape) — route questions through the controller.

## §6 pnp's all-nodes upgrade + THE ORDERING CONSTRAINT (2026-07-23, commit 816f5de19; controller re-ran: exit 0)

Soundness upgraded from case11-only to **every node type** (case2 δ=1, case2 δ=0, rollover,
case11 δ=1) on all three witnesses ((2,2,2,2), (2,3,2,2) wide, (3,3,2,2) double-boost), with both
of L4D's consumer shapes exhibited verbatim on the explicit construction:

- `clearedFoldG_C = foldG ∘ couplingClear`, `clearedFoldB_C = foldB ∘ couplingClear`,
  `clearedFoldResid = sourceClearedResid`.
- **clearedFoldB_C is a clean MONOMIAL** = ∏(δ=1 pivots) at every node — the pivot factor lives
  in the B-side *by construction* (shape-1 satisfied where the raw foldB failed).
- (S1) cleared StepInv (`clearedFoldB_C | coreGen∘clearedFoldG_C` AND membership in
  `⟨B_C·C_j⟩`): TRUE at every node. (S2) the child↔parent commutation (child C = parent C ∘ the
  δ=1 strict-transform quot): TRUE — the append's `q' = q∘stepMap` closes on C exactly as on F.

**THE ORDERING CONSTRAINT (binding on SPECIFY).** The per-step INTERLEAVED clear-BEFORE-blow-up
does **not** equal the precompose — false at *every* node (the script prints the comparison
per-node; an interleaved attempt even corrupts clearedFoldB into a non-monomial). So the faithful
cleared fold is the **precompose form** (global source-clear on the input, THEN the blow-up
path). seat-GM's def must be the precompose — or, if a per-step recursion form is wanted for the
Lean wiring, it must follow Aoyagi's literal order (blow-up THEN clear), and whether *that* order
equals the precompose is a pending pnp check (commissioned 2026-07-23). Until that check returns,
SPECIFY on the precompose form only.
