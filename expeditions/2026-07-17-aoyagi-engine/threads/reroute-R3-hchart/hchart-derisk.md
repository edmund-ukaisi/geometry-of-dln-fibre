# R3 `hchart` de-risk (#177) — VERDICT: hchart = SANDWICH+cover = PRICED; born-per-pivot CLEAN; transport AVAILABLE-BUT-AVOIDABLE

**Seat:** pen-and-paper (reroute-R3-hchart), decorrelated. Exact algebra (sympy over ℚ) + own
Codex xhigh (`codex/hchart-{prompt,answer}.md`, EXIT 0) — CONVERGED independently. NO Lean.
Scripts (this dir): `sandwich334.py`, `mismatch_cover334.py`. Read the REAL Lean assets first
(`SurvivorFanCover.lean`, `ImageTreeCover.lean`, `StepConstructor.lean`,
`Core/Aoyagi/ProductResolution.lean`, `Corank2Chart334.lean`, `Corank2ChartJac.lean`) + the
prior de-risks (#167/#169/#170/#172) — verified against, not assumed.

## NET: R3's per-node clause is a BUILD (wiring priced pieces), not a monument. Born-per-pivot is
## transport-free and CONFIRMED on the real (3,3,4) charts. KILL-CONDITION NOT TRIGGERED.

---

## JOB 1 — WHAT `hchart` IS (decompose)

The elder's per-node `hchart` = what each born chart must satisfy to feed BOTH engines R3 unifies:

- **COVER engine** (`ImageTreeCover.node_clause_of_survivorAtom` ⟵ `SurvivorFanCover`): the
  SET-COVER `∀ a, survivorRegion R gen a ∩ box ⊆ g_a '' dom_a` + hole-nullity
  `volume (commonZero gen) = 0` + null-transport (banked `nullTransport_of_differentiable`,
  cheap from `Differentiable`).
- **VALUE engine** (the ADOPTED (A) lower bound, compass F10): the per-chart **R>0 SANDWICH**
  `loss = monomial_a² · R_a`, `R_a(0) ≠ 0` — banked structural lemma `SurvivorFanCover.sumSq_residual`
  (kept-survivor ⟹ `R(0)=1`, `R ≥ (kept)²`).

**Verdict: (a) — `hchart` = the R>0 SANDWICH + the survivor-entry set-cover + cheap hole-nullity.
NOT (b): there is NO separate loss-isometry / matched-pairing STRUCTURE beyond this.** The
"matched-pairing" is the *indexing* of the fan (which product-entry survives), and the sandwich
`R_a(0)=1` is a *per-chart consequence* of that chart's own blow-up monomial being a matched
product term of its survivor generator — not an extra certificate. (Codex Q1 independently: "No…
no loss-isometry structure is required.")

**Sharp refinement (load-bearing): for the ADOPTED (A) route, `hchart` does NOT need `binv`
(the two-sided ideal identity `⟨(∏C)∘g⟩=⟨diag b⟩`).** The sandwich (a one-sided floor
`loss ≥ monomial² · c`) is strictly weaker and suffices (F10). The two-sided `binv` is the
(B)-fallback (full `Resolution` atlas / `Chart.hideal_fwd/bwd`); at (3,3,4) it is already banked
(`chart334`, `nbhd=univ`, single monomial, `hideal_coreGen_fwd/bwd`), general-d it consumes the
inferred terminal-single-chain-principality monument (#167). So: **(A) = sandwich, all priced,
R3 = wiring; (B) = +binv, cite-the-inference fallback.**

### Exact-algebra CONFIRMATION on the real (3,3,4) born charts (`sandwich334.py`, exact ℚ)
`C1` 3×3, `C2` 3×4, `X=C1·C2`, `loss=‖X‖²`. A born chart = block blow-up of a matched pivot PAIR
`(C1[i,k],C2[k,j])` (one additive term of survivor `X[i,j]=Σ_k C1[i,k]C2[k,j]`), radials `r1,r2`,
monomial `m=r1·r2`:
- **All three matched pairs of `X[0,0]` give `survivor/m(0)=1` and `R(0)=1`** — sandwich holds,
  each from ITS OWN pair. [FACT, exact]
- **Control (`mismatch_cover334.py`): a MISMATCHED pair `(C1[0,1],C2[0,0])` gives `R(0)=0`** —
  sandwich FAILS ⟹ not a fan member; its region recurses (matches #170 addendum). [FACT, exact]

## JOB 2 — W3 KILL-CHECK (the sharp one): born-per-pivot vs inter-sibling orbit-transport

**VERDICT: born-per-pivot is CLEAN and SUFFICIENT — transport is NOT REQUIRED. But the DANGER is
REAL and NAMED: the banked *pre-reroute* (3,3,4) fan skeleton reaches for exactly the retired O1
transport, and R3 must NOT wire through it.**

- **Transport-free construction CONFIRMED** (`mismatch_cover334.py` JOB2 + Codex Q2/Q4). The
  survivor-entry fan = 36 born charts (12 survivors × 3 matched pairs); **each chart's monomial is
  a DISTINCT coordinate pair, its sandwich computed from that pair alone; no chart references
  another's coords.** The cover is discharged by ARGMAX (`SurvivorFanCover.iUnion_survivorRegion`:
  route each point to the generator that dominates → the born chart for that generator covers it) —
  **no permutation / isometry appeal anywhere in the cover proof.** The loss-isometry orbit is at
  most an *interpretation* of which generators index the fan, never a proof ingredient. (Codex Q2:
  "symmetry may enumerate the fan indices, but no certificate for chart A must be derived from a
  sibling B.")
- **THE CREEP TO GUARD (the O1 wall, compass F9).** `Corank2Chart334.lean:122–123` (the PRE-reroute
  route-P fan-cover skeleton) proposes to build the (3,3,4) fan as "a `FanTree 21` whose leaf
  path-composites are the **K-orbit of `gWrap`** (each an isometry-conjugate… 'resolution charts =
  canonical + K-symmetry orbit')". **That IS the retired two-object σ-transport** (sibling =
  isometry-image of the canonical chart) — O1: transport-group ⊥ cover-set on node pivots, and a
  valid gauge co-permutes the adjacent layer (moves an ancestor pivot). If R3 discharges `hcover`
  via `resolution334_of_fanCover` with a K-orbit fan, O1 re-enters = DEAD ROUTE.
- **The mandated alternative (guardrail-0, confirmed viable):** born each sibling from
  `StepConstructor.bornSiblings` (per-pivot, own `CleanClearing`, `blockBlowupMap` pivot-parameterized,
  shear-outermost so W/escape pivots also give det-monomial + `R(0)=1` — #170 addendum), and fold
  with `ImageTreeCover.glue_null` (per-child domains, no cross-sibling reference). Transport is
  AVAILABLE (banked pre-reroute note) but STRICTLY AVOIDABLE.

Codex Q4 (verbatim intent): the reintroducing move = "proving chart A's certificate as the σ-image
of chart B's"; "directly constructing the matched blow-up at every pivot makes this entirely
avoidable."

## JOB 3 — W1 note (same chart/region)

**Same region for (A).** For a born chart, the cover conjunct (its survivor region = where its
generator dominates) and the sandwich conjunct (`R_a(0)=1`, `R_a>0` on a ball of that region) hold
on the SAME chart's domain (Codex Q3: "Same… no algebraic change of region is forced"). No
`D_p`-different-region split for the sandwich route. CAVEAT for (B) only: the two-sided `binv`
localizes to `{unit≠0}⊊univ` at separated depth (#167) and inherits the R1 terminal-shrink⋈cover
coupling (recursion-rzero R1) — a (B)-fallback residual, NOT an (A) issue.

## THE R3 FIRST-BRICK (recommended shape)

At ONE node (start (3,3,4) root), as a THEOREM, transport-free:
1. Instantiate `SurvivorFanCover` with `ι` = the node's residual-ideal generators (`coreGen` entries
   `X[i,j]`), `gen` = those, `chart a` = the `bornSiblings` chart making generator `a` survive (its
   matched pivot pair, shear-outermost), `dom a` = its inflated box.
2. Discharge `hchart a` (set-cover) from the block-blow-up covering atom (`GeneralGeoAtlas §1`,
   `blockShear_covers_of_norm_bound`) — per-pivot, its own image.
3. Discharge `hnull` (hole = `{X=0}`) from `volume_commonZero_eq_zero_of_single` (one nonzero
   generator, codim ≥ 1 — cheap).
4. Feed `node_clause_of_survivorAtom` → the per-node up-to-null cover; the sandwich per chart from
   `sumSq_residual` (its own monomial's matched survivor).
5. **The genuine wiring content (detail-at-scale, NOT a monument):** the CORRESPONDENCE
   `ι (node generators) ↔ bornSiblings pivots`. `bornSiblings(Z,c)` emits one chart per pivot in a
   center `Z`; the survivor-entry richness (36 leaves) is the buildTree BRANCHING, not one node's
   `bornSiblings`. Verify at R3 that node N's per-node fan enumerates node N's survivor generators
   (each born from its own pivot). This is the abstract-atom-`ι` ⋈ concrete-`bornSiblings` marriage —
   transport-free by construction (both atoms are per-child-independent), but it is the concrete
   first-brick to nail.

## CLOSE
FIRMEST [FACT, exact + decorrelated]: `hchart` = the R>0 sandwich + survivor-entry argmax-cover +
cheap hole-nullity; every piece banked/priced; born-per-pivot, transport-free (matched pairs give
`R(0)=1` each from its own coords; mismatch `R(0)=0` recurses; cover 100% off `{X=0}` by argmax).
MOST LIKELY TO BREAK IT: R3 wiring the cover through the banked pre-reroute `resolution334_of_fanCover`
K-symmetry-orbit fan (`Corank2Chart334.lean:122`) — that smuggles the retired O1 transport back;
avoid it, born the fan from `bornSiblings`. NEXT: the first-brick above (node-N generator ↔
bornSiblings-pivot enumeration), one-node theorem, then fold via `glue_null` through `conRel_wf`.
KILL-CONDITION (hchart general-d = monument OR requires inter-sibling transport): NOT triggered —
R3 is a build; destination stays (A) lower-bound, no monument.
