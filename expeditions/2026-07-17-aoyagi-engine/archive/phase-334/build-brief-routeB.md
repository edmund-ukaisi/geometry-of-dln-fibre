# Build brief — the transformed-center resolution (route-B shape) — v2, audit-corrected

**Decision (operator, 2026-07-25): BUILD (A) — the cite-free lower — in the route-(B) shape.** This v2
folds in the decorrelated obstruction audit (`threads/audit-routeB/obstruction-catalogue.md`, exact algebra
+ Codex, both agreeing). **No math wall** (coreGen symmetries real; spine render-bounded; full-fan cover
atom banked; equal-b holds general-`d`). But the v1 ECONOMY claim ("resolve representatives only; collapses
the monument") was **REFUTED** — corrected below. Objects-only stays the STOP-fallback.

**Honest re-pricing (O3).** Route-B does NOT shrink the general-`d` `hideal` monument; it (i) collapses the
*cover* monument (the flat-fan ball-cover → the per-step `Covers` fold, validated §2), and (ii) reduces the
leaf COUNT via orbit symmetry. The load-bearing labour remains: the general-`d` L-A/L-B/L-C spine per
K-orbit representative + the route-a full-fan cover + a **node-stabilizer / chart-path coherence theorem**
(O2, new, named below). This is the "substantial multi-tide monument" originally priced.

## §0 The idea (validated) + the TWO pathologies (audit-corrected §1)

**Fan the CONSTRUCTION, not the composite.** The recursion over `buildTree d (conOracle d) conRoot` presents
each stage's blow-up in that branch's CURRENT coordinates; each transformed-center chart is individually
valid (banked pnp-chartarch: `|jacDet|` monomial, `injOn` off exceptional, `g 0 = 0`, two-sided `hideal`).
This cures the **fixed-shear** pathology (a globally-fixed shear wrong for the pivots it wrote).

**BUT there are TWO independent pathologies, not one.** The escape-cone is ALSO a **col-pin /
fan-completeness** artifact (the col-pinned atlas misses ~67% of the box — the max entry sits in a non-pinned
column), INDEPENDENT of the fixed-shear error. The fix for THAT is **route-a full-fan emission** (pivots
over ALL of each center `S`, not the col-pinned ledger). Both fixes are needed; the full-fan emission then
feeds into O1/O2 (every pivot chart needs a certificate).

## §Atlas identity — DECIDED UP FRONT (resolves O2's fork)

**The atlas = the tree's full-fan leaf g-maps** (charts ARE `buildTree` leaves). Consequence:
- **Cover** (`Resolution.hcover`): the banked route-a full-fan cover applies to the tree g-maps directly
  (`LeafCoverTiling.covers_subset` + `closedBall_subset_iUnion_blockBlowup_image_radius`). ✔ (§2)
- **Certificate** per leaf: every leaf needs a certified two-sided `hideal`. Transport (coreGen K-symmetry)
  reaches only the K-ORBIT of a resolved leaf; the rest are resolved from scratch. So: resolve one rep per
  K-orbit (the general-`d` spine), transport within each orbit, and prove the orbits exhaust the leaves.
- **O2 coherence**: the transported chart of a leaf `L` along a coreGen symmetry `σ` must BE the tree leaf
  `σ·L` — a STRUCTURAL chart↔path identity retaining exponent-to-AXIS incidence (not just the ℕ-value the
  `AtlasRealizesExponents` seam matches). This is the named replacement for v1's "one induction, two clauses."

## §1 What the fold produces (the seam)

`exists_coreResolution :311` reduces **sorry-free** (`RecursionAdapter.exists_hlb_hattain_of_exists_atlasRealizesExponents`)
to `∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res`. The fold produces:
- a `Resolution` = the tree full-fan leaf atlas (per-leaf `Chart`: g, analytic/inj, bexp/k₀/hchain/hbind/
  hunit_mult from the ledger, jac+hjac, **hideal_fwd/bwd**) + **hcover** (§2, banked route-a);
- `AtlasRealizesExponents` = the value-support match (ledger read-off, banked). **NOTE (O2):** this seam is
  the numerical value adapter AFTER a genuine `Resolution` (chart validity + coverage) is supplied — it is
  NOT a transport/coverage seam. Coverage is established structurally (§2 + the O2 coherence), not by
  exponent values.

## §2 The cover — validated (collapses the cover monument)

Per-step coverage = the standard charts of each stage's blow-up cover the stage box (argmax block-atom,
banked `closedBall_subset_iUnion_blockBlowup_image_radius`). The tree fold is `covers_subset`
(`Covers f t R → closedBall 0 R ⊆ leafImages`, clean-three). `FanTree.node S hS σ child` carries per-pivot
shears + per-pivot children — the route-a FULL fan (all pivots of `S`). This IS the flat-fan ball-cover
monument, collapsed into the recursion. Runs on the TREE g-maps (= the atlas, per §Atlas identity). ✔

## §3 The certificates — per-K-orbit dedup (NOT per-node collapse) — audit-corrected

Per-step ideal mechanism (banked/general): L-A `regionRepresents_of_matrix_mul` + symbolic Schur (any
`CommRing`; general-`d` via `SchurClearTwoSided`); L-B `maintenance_step_two_sided` (general, b-chain-cond.);
L-C `terminal_bezout` (general). Composition: `regionRepresents_comp` + `.trans` + `terminal_bezout`. The
general-`d` L-A/L-B/L-C **spine, composed down a branch, is the load-bearing per-leaf build** (render-bounded
detail-at-scale, genuinely unbuilt).

**Transport = K-orbit dedup, not per-node collapse.** `transportChart` (banked, `-5d-transport`) transports a
certified `Chart` across a `coreGen` symmetry `σ` under `hequiv : ∀ i, coreGen_i ∘ permOf σ = coreGen_{τ i}`.
The coreGen symmetries are ONLY: **end-perms** (`α`/`β` on output/input, `τ≠id`) + **matched-gauge** (the
shared/contraction index in BOTH adjacent layers, `τ=id`). The parent stabilizer is **NOT transitive** on a
node's pivots (O1: the matched-gauge swap of an intermediate pivot co-permutes the adjacent layer; if it
carries an ancestor pivot, the chart lands under a different parent). So transport de-dups along the K-orbit
of LEAVES; it does NOT let you skip a node's non-orbit siblings. Resolve one rep per K-orbit from scratch;
prove the orbits exhaust the leaves.

**THE ONE NEW LEMMA — restated (O4).** NOT "the stage family `{b·Xᵢ}` is fixed under within-run relabeling"
(wrong family — the stage family relates to coreGen by unimodular cofactors, not a permutation; and a uniform
within-run swap is unsound). The CORRECT lemma: **`coreGen` (the product) is equivariant under the per-stage
`σ` induced by a within-run index swap — END-perm for output/input runs, MATCHED-gauge (two adjacent layers)
for intermediate runs.** The general-`d` analog of the banked `Corank2CoreGenEquivar` (which IS this
construction for (3,3,4): `ρ` in both A0/A1 blocks = matched-gauge, `α,β` = ends). Detail-at-scale.

## §Guards / STOP-conditions — audit-corrected (trip on O1/O2, NOT equal-b)

- **STOP (i) — O1 orbit-coverage fails:** a leaf-orbit whose representative's general-`d` spine does not
  close, OR the coreGen orbits do not exhaust the tree leaves (some leaf reachable by no resolved orbit).
- **STOP (ii) — O2 coherence fails:** the transported chart cannot be identified with its tree leaf (the
  chart↔path structural map, with exponent-to-axis incidence), so the cover and the certificate cannot be
  reconciled on one atlas.
- (equal-b run legality is NOT a STOP — it holds general-`d`, incl. Case-2 successive clearing; do not gate on it.)
- Either STOP → objects-only close (cite `cited_aoyagi_lower_ax`, charter-faithful #94).
- Standard: sorry-free; `#print axioms` clean-three (force-elab); `#assert_banked_clean_batch` on new roots;
  full `scripts/lb DLNFibre` green + name-clash gate before "integration-ready".

## §THE DE-RISK GATE — before any full-team commit (audit's recommendation)

A **general-`d`** (NOT (3,3,4)) end-to-end of ONE intermediate-layer node, green-all, clean-three:
1. resolve the node's representative branch's stage (L-A block-elim + L-B maintenance) at a general
   intermediate layer (minimal witness class d=(2,2,2) or the smallest with an intermediate node);
2. the **matched-gauge `hequiv`** + the **ancestor-pivot bookkeeping** (verify where the transported chart
   lands — the O1 crux);
3. the **O2 coherence** (transported chart = the sibling tree leaf, exponent-to-axis incidence retained);
4. the cover on the tree g-maps at that node.
GREEN-all → route-B-corrected viable, commit the full team. WALL on any → STOP to objects-only, report the
exact obstruction first. (3,3,4) is REGRESSION evidence only; the build is general-`d` from the start.

**Acceptance checklist (audit-routeB's decorrelated review criteria — the gate must satisfy ALL, and a green
build is NOT sufficient without them):**
1. `σ` is the MATCHED gauge (touches BOTH adjacent layers), NOT a single-layer/single-entry swap — check the
   actual permutation, not just that `hequiv` type-checks.
2. `hequiv` is stated on `coreGen` (the product family), NOT the Schur stage family `{b·Xᵢ}`.
3. Ancestor-pivot bookkeeping: verify the transport does NOT silently move an ancestor pivot — either the node's
   shared index is NOT ancestor-born, OR the coherence theorem explicitly handles the parent-change. (Where O1
   bites; a green build can still be wrong here.)
4. The transported-chart COVER is proven on the ACTUAL atlas charts (O2), NOT inferred from exponent-support
   matching (guard the `{β₁,β₁}` failure mode — same exponents, missing coverage).
5. It is a genuine INTERMEDIATE-layer node (middle gauge), NOT an output/input end-run (`α`/`β`) — the end case
   is the easy one and does not exercise O1.
audit-routeB will re-run decorrelated exact algebra on the concrete node the gate uses.

## Banked assets pinned by interface

- `Core.Aoyagi.Corank2Proto` (`regionRepresents_of_matrix_mul`, `Q1_C1_Q2_eq_diag`, `regionRepresents_comp`).
- `Core.Aoyagi.Corank2MaintenanceProto.maintenance_step_two_sided`; `Corank2TerminalProto`/`terminal_bezout`.
- `Core.Matrix.SchurClearTwoSided` (general-`d` block-elim atom).
- `DLN.Aoyagi.LeafCoverTiling` (`covers_subset`, `FanTree`, the block-atom).
- `DLN.Aoyagi.ChartTransport.transportChart` + `Corank2CoreGenEquivar` (`-5d-transport`).
- `DLN.Aoyagi.RecursionAdapter` (`exists_hlb_hattain_of_exists_atlasRealizesExponents`, `AtlasRealizesExponents`).
- Ledger: `Engine.minAdm_le_terminalExponents`, `o5_core_realized`.
- `Core.Aoyagi.ProductResolution` (`Chart`, `Resolution`).
