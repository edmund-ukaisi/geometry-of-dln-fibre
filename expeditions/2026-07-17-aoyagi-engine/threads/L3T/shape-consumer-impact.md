# Consumer-impact table — the faithful descended-support SHAPE + the b-chain FIELD (seat-L3T2, read-only)

Charge: enumerate every current statement reading `supportAt / blockCoords / Deg1SupportedSlot /
PerLayerDeg1From / FoldStepInvAt`, and for each say — under the three descended-support SHAPE candidates
and the b-chain FIELD addition — whether it is TRUE-as-stated / needs RESTATEMENT (what changes) /
UNPROVABLE / UNKNOWN. Flag proof-difficulty DIVERGENCES between candidates. Read-only; -L3T2 + L3T3 lean
files untouched. Confidence tagged; honest UNKNOWN where determining it needs proof work I did not do.

## The candidates (as I understand them)

SHAPE of the descended append support `supportAt d (child).layer (child).cleared` (currently
`blockCoords(S+1)`, which the cap-escape makes UNPROVABLE — recoord (ii) writes layer-`(S+1)` col =
pivot-ROW, row-uncapped, escapes when `d_{S+1} > widthMinUpto(S+1)`):
- **(a) WIDEN** — `:= layerCoords(S+1)` (drop the col cap; the full layer).
- **(b) REMNANT** — `:= blockCoords(S+1) ∪ {layer-(S+1) coords at col = pivot-row}` (cap + explicit escape account).
- **(c) THROUGH-RECOORD** — support stated in the recoordinatized entries (support in the `N_p`-image frame).

FIELD: the b-chain / value-vanishing addition to the carried invariant (`Deg1SupportedSlot` or
`FoldStepInvAt` gains a conjunct: the extra-block `∃c` coefficients VANISH at `u_pivot = 0`). Forced
because ROUTE β is dead — `Deg1SupportedSlot`'s `∃c` are CONTINUITY-only (:547-548), insufficient for the
case11 boost split, which needs the b-chain (path-inductive, canonFlatten-root-anchored).

## Table (Consumer | shape a | shape b | shape c | FIELD addition | confidence)

### L3T lane + abstract machinery — SHAPE-INSENSITIVE (definite; my territory)
- **coreGen_layerHomogeneous(') , foldResid_layerHomogeneous(')** — read `layerCoords`, NOT supportAt.
  TRUE / TRUE / TRUE. FIELD: no invariant field; but see the KEY OBSERVATION below (they PRODUCE the field's
  vanishing content). **INSENSITIVE to shape.** HIGH.
- **homogeneousDeg1On_comp_of_fixing / affineOn_comp_of_linear / homogeneousDeg1On_comp_of_linear** —
  abstract over a generic block `X`. TRUE / TRUE / TRUE; the consumer supplies `X`. FIELD-neutral. **INSENSITIVE.** HIGH.
- **perLayerDeg1From_comp_of_fixing** — over `layerCoords`. TRUE/TRUE/TRUE. INSENSITIVE. HIGH.
- **deg1_comp_of_fixing** — abstract (takes `hfix` as hypothesis). STATEMENT TRUE/TRUE/TRUE. NOTE: its
  APPLICABILITY at `ℓ=sl` is gone post-N_p (`hfix` false there — recoord writes `sl`); the append/δ=0 consumers
  shift to `comp_of_linear`. Proof-side, not statement-side. HIGH.
- **exists_graded_decomp / exists_ignoresCoords_decomp** — abstract over `S'`. TRUE/TRUE/TRUE (S'-agnostic).
  INSENSITIVE. HIGH.
- **blockCoords_subset_layerCoords / canonCenterOf_append_subset_layerCoords / canonCenterOf_decode_layer_le /
  decode_layer_of_mem_layerCoords** — pure geometry of blockCoords/layerCoords/canonCenterOf, no descended
  support. TRUE/TRUE/TRUE. INSENSITIVE. HIGH. (Under (a), any downstream `support ⊆ layerCoords` step becomes
  trivial; under (b)/(c) unchanged.)

### The SHAPE-SENSITIVE producers — RESTATE under ALL candidates (definite; my territory)
- **realBranch_appendResidDescent** (the cap, clause-1 `∃c, resid = ∑_{i∈supportAt(child)} cᵢ·uᵢ`):
  current `blockCoords(S+1)` = **UNPROVABLE** (cap escape). (a): RESTATE `S:=layerCoords(S+1)`, PROVABLE
  (escape admitted; comp_of_linear on the full layer). (b): RESTATE to the union, PROVABLE (remnant account).
  (c): RESTATE to the recoord frame, PROVABLE **iff** the recoord basis-change confines (the structural hope
  — unverified; = the wall). FIELD: appendResidDescent is `∃c`-only; the FIELD addition adds the vanishing to
  it (needed for case11 boost). RESTATE to carry vanishing. HIGH on shape; the (c)-confinement is the open bet.
- **realBranch_multiAffine_step(')** — child `Deg1SupportedSlot`: clause-1 = appendResidDescent (RESTATE per
  shape); clause-2 (`PerLayerDeg1From`, layerCoords) INSENSITIVE. FIELD ripples via the slot def. HIGH.
- **descent_delta1_append / descent_delta0** (MultiAffineStepWire slot arms): clause-1 RESTATE per shape
  (provable via comp_of_linear); clause-2 INSENSITIVE. FIELD via the slot def. HIGH.
- **descent_delta1_case11** — shear = id, NO recoord, NO escape ⟹ clause-1 cap HOLDS. **shape-INSENSITIVE**;
  but **FIELD-SENSITIVE** (case11 is exactly where the b-chain boost split bites — the sorried
  boostReady_case11). HIGH on shape; the field is the case11 content.

### The DEF-level FIELD change — ripples to EVERY consumer
- **Deg1SupportedSlot / FoldStepInvAt** (defs): the FIELD addition is a DEF change (new conjunct/field).
  MECHANICAL RESTATE of every consumer (thread the field); the CONTENT (produce/consume the b-chain) is the
  real work, concentrated in the wall lane. Shape and field are ORTHOGONAL axes: shape = which `S`; field =
  the extra vanishing conjunct on the `∃c`. HIGH (that it ripples); the content survivability is below.

### The wall lane — STATEMENT restate is mechanical; PROOF survivability UNKNOWN (not my build)
- **case1_preserves_stepInv(') / case2_preserves_stepInv(')** — carry `FoldStepInvAt(supportAt)` parent→child.
  STATEMENT: RESTATE under all shapes + field (thread the shape + field through hinv and the conclusion).
  PROOF survivability: **UNKNOWN** — the re-factoring (exists_graded_decomp / BlockDivision) producing the
  restated support + the b-chain field is the wall content; I did not build it. DIVERGENCE (for the elder):
  (a) widen makes the CHILD support easier to produce but also WIDENS the parent `hinv` (weaker input to the
  next step); (b)/(c) keep the cap tighter (stronger, but the producer must account for the remnant/recoord).
- **realBranch_boostReady_case11** (Case1Wire:386, SORRIED, TRACKED-OPEN) — reads `hslot`(parent supportAt),
  concludes `Deg1SupportedOn(ed.center)`. **UNKNOWN** under all shapes; its provability IS the b-chain wall
  (Route β dead). DIVERGENCE + KEY: it reads the parent slot + concludes on the CURRENT-layer center — both at
  layer `S`, NOT the descended `S+1` — so I expect it **shape-INSENSITIVE but FIELD-CRITICAL** (needs the
  b-chain field, independent of a/b/c). If so, the SHAPE ruling does not unblock boostReady; only the FIELD does.
  MEDIUM (structural read; the exact dependence is proof work).
- **deg1SupportedOn_center_of_hslot** (Case1Wire:292) — derives center-support from `hslot`; the center
  (canonCenterOf) is CURRENT-layer. Likely **shape-INSENSITIVE**; field-neutral (the δ=1 case12 cover route,
  not the b-chain). LOW-confidence UNAFFECTED; **UNKNOWN** if the hslot shape/field change breaks the derivation.

### Descent tail / terminal / L5 base — SHAPE-INSENSITIVE (the recoord doesn't reach them)
- **lastLayer_clear_preserves / terminal_edge_stepInv** — support exhausts to `∅` at `S+1=N` (no layer-`N`
  matrix ⟹ no recoord write). TRUE/TRUE/TRUE on shape; FIELD threads mechanically (vacuous on `∅`). HIGH.
- **realBranch_cover** — cover at `cleared=0` is the CURRENT-layer block ⊆ center, upstream of the descent.
  Shape-INSENSITIVE; field-neutral. TRUE/TRUE/TRUE. MEDIUM-HIGH.
- **foldStepInvAt_to_lastLayerInv** — consumes FoldStepInvAt→lastLayerInv at the exhausted (∅) support.
  Shape-INSENSITIVE; FIELD: mechanical thread unless lastLayerInv must consume the b-chain. LOW-confidence
  UNAFFECTED; **UNKNOWN** on the field-consume.
- **L5 base (root FoldStepInvAt)** — root support `blockCoords(0)`, no recoord. Base shape-INSENSITIVE + field
  mechanical; the L5 STEP inherits case1/case2's shape+field sensitivity (so L5's overall survivability tracks
  the wall lane). HIGH on base; step = UNKNOWN (tracks case1/case2).

## DIVERGENCES the elder most needs
1. **appendResidDescent / the slot clause-1 + case1/case2 re-factoring**: (a) WIDEN is the CHEAPEST to PRODUCE
   (escape admitted into the full layer, comp_of_linear closes it) but yields the WEAKEST invariant (a wider
   parent `hinv` downstream). (b) REMNANT keeps the cap + an explicit escape account (more to produce, stronger
   invariant). (c) THROUGH-RECOORD is the structural form whose provability is unverified (= the confinement wall).
   The trade is PRODUCE-cost vs DOWNSTREAM-strength — decided by whether any consumer NEEDS the cap.
2. **Does any consumer NEED the cap (⟹ (a) too weak)?** The candidate is `boostReady_case11` / the case11 boost
   split. My structural read: boostReady reads the parent slot at layer `S` and concludes on the layer-`S`
   center — it does NOT read the descended `S+1` support — so I expect it **shape-insensitive**, needing the
   FIELD (b-chain) not the cap. IF that holds, **(a) WIDEN is safe** (no consumer needs the S+1 cap) and the
   FIELD does all the work. This is the load-bearing UNKNOWN — it decides whether shape can be the cheap (a).
   Recommend the elder confirm boostReady's support-read is at `S`, not `S+1`, before ruling (a) vs (b).
3. **SHAPE ⟂ FIELD**: the shape ruling (a/b/c) is about WHICH `S` in clause-1; the field ruling is the extra
   vanishing conjunct. They are independent — the field is needed for case11 REGARDLESS of the shape.

## KEY OBSERVATION — the homogeneity lane PRODUCES the FIELD's vanishing content
`foldResid_layerHomogeneous` gives, per layer `ℓ ≥ supportLayer`, VANISHING: `(∀ x ∈ layerCoords ℓ, u x = 0)
→ resid u = 0`. That is exactly the "extra-block coefficients vanish at `u_pivot = 0`" content the b-chain
FIELD needs (the value/vanishing candidate field V). So the homogeneity induction — though shape-INSENSITIVE
(uncapped layerCoords) — is the natural PRODUCER of the FIELD's vanishing half, canonFlatten-root-anchored
exactly as Route-β's requirement demanded. The elder's field-V (value/vanishing) candidate ≈ what my
induction supplies; the field-S (structural ChainNF) candidate would be a heavier carried object. If field-V
suffices for boostReady, the homogeneity lane feeds it directly. (Confidence MEDIUM — the exact match between
homogeneity-vanishing and the b-chain-vanishing boostReady consumes is worth the elder's check; flagged, not
asserted.)

## HONEST UNKNOWNs (need proof work I did not do)
- case1/case2 re-factoring PROOF survivability under (b)/(c) (the BlockDivision internals).
- boostReady_case11 exact support-read layer (`S` vs `S+1`) — decides divergence #2.
- foldStepInvAt_to_lastLayerInv / deg1SupportedOn_center_of_hslot field-consume behaviour.
- Whether field-V (vanishing) alone suffices for boostReady, or field-S (structural) is required.
