# t05 → t07 carrier-build spec — the concrete q_node / centerIndices arc

*architect-t05's last deliverable (hatch granted, tick-210). The carrier build (the concrete
coordinate-layout arc) goes to a fresh seat t07 rather than split intricate coordinate work across a
six-arc seat and a fresh one. This doc is t07's complete, authoritative spec: the ratified interface,
the banked foundation, the qNodeOf plan, the u-pivot parameter, the per-case shapes, and the
verification gate. t07 spawns when this + pnp-slot's slot-stability cert are both in.*

## 0. Scope + ownership (elder-gate9 + tick-208/210)

- **t07 owns (its files):** the concrete per-node `centerIndices` selector + its assembly into
  `qNodeOf` (the node-indexed coordinate-split `Homeomorph`); the per-edge `d_center` exposure. In
  `Engine/CenterIndices.lean` (banked foundation, §2) + wherever `qNodeOf` reads the node/edge.
- **coverage owns (after the carrier):** `α_e` (source det-1 gauge) + the domain-reparam identity
  `β̃ '' αD = β '' D`; `geometricLeafPaths`; the cover fold; the 3 Props; clause (D). The `GeoChart`
  sibling record (§8 ruling — per-pivot geometry off-spine; `ChartSubst`/`StepRel` stay the untouched
  quotient, NO type change).
- **o5:** `LeafPullback` (analytic). **DO NOT touch** EngineDefs.ChartBridge / ChartBridgeWiring /
  RegionGlueAssembly (coverage's re-typing batch, MERGED) or the spine.

## 1. The ratified interface (proposal `carrier-interface-proposal.md` f0a8363fd + my review
`carrier-interface-review.md` 3fe01c45e + elder-gate9)

- **Route R-b (source reparam), settled** (`cert-psi-mix.md`): `localSub_e = β̃_e = β_e ∘ α_e⁻¹`,
  `α_u = .refl`, `α_d =` inverse-Schur unipotent (det 1); chart IMAGES = pure-β images, so the PURE
  `node_pivotCover_of_atom` tiles (the sheared variant retires to `ψ=.refl`).
- **Per-edge d_center counts (elder-gate9 amendment 1 — THE off-by-one guard):** the pivot family
  PARTITIONS across the case-1 node's TWO edges (different children, EngineConstruction:2041-2044):
  - case-1(1) edge (→ child11): **1** chart (the `u`-pivot).
  - case-1(2) edge (→ stepAppendAdvance): **runLen·resCols** (the d-family, `J₁ × (M^{S+1}−J)`).
  - case-2 edge: **resRows·resCols** (`(M(S)−J) × (M^{S+1}−J)`).
  - rollover edge: **0** (chartless).
  Node `d_center` = the SUM. **NEVER emit the node total on the case-1(2) edge** (double-counts `u` —
  the same off-by-one class as the original 2-rep undershoot).
- **Seam pin (buck-stops at your→coverage boundary):** expose `qNodeOf` as a NODE-INDEXED DEF
  (`qNodeOf : StepData M → (Params M ≃ₜ (Fin d_center → ℝ) × …)`, or edge-indexed), node-DERIVED from
  `centerIndices` — NEVER a free/existential carrier field. Coverage's `β_e` conjugates YOUR `qNodeOf`;
  an opaque existential would let the fold stop being a function of `t` alone and a fabricated `q_node`
  satisfy clause (D) internally.
- **Uniform u-geometry (elder-gate9):** the `u`-chart's data lives in the `GeoChart` too — its
  uniqueness is in the COUNT (1), not a special location.

## 2. BANKED FOUNDATION — `Engine/CenterIndices.lean` (0d38f748c, green, 0 sorries)

*Committed before the hatch ruling arrived; a clean proven sub-unit t07 INHERITS (extend it, or absorb
it into a coherent whole — t07's call; nothing here is half-built, all green + injective).*

- `flatCoordOf M s i j : Fin (flatDim M)` — the flat coord of the `(i,j)` entry of the `s`-th weight
  matrix, `= Fintype.equivFin (FlatIdx M) ⟨⟨s,i⟩,j⟩` (the reindex `paramsEquivFlat` uses,
  `ParamsFlat.lean:80-84`). `+ flatCoordOf_injective` (via `eq_of_heq` on the fixed-`s` sigma).
- `resBlockCenterIndices M s J rows cols (hrow : J+rows ≤ M s.castSucc) (hcol : J+cols ≤ M s.succ) :
  Fin (rows*cols) → Fin (flatDim M)` — the residual sub-block `[J,J+rows)×[J,J+cols)` flattened
  (`finProdFinEquiv.symm`), each cell → `flatCoordOf`. `+ resBlockCenterIndices_injective`.
  **Instantiate:** case-2 `rows,cols = resRows,resCols`; case-1(2) `rows,cols = runLen,resCols`.
- The bounds are HYPOTHESES = the reachability invariants (`resRows = M(S)−J` and `M(S) = running-min
  ≤ M s.castSucc`, so `J+resRows ≤ M s.castSucc`; likewise cols). t07 discharges them from the node's
  `OracleInv`/`StateInvariant` (`WidthBound`/`live_width`) at the reachable nodes.

## 3. The u-pivot slot — PARAMETER, wired to pnp-slot's verdict

The case-1(1) center is the d-block PLUS ONE existing divisor `u_{s,k}` (`page-pin-centers.md` p.16;
the p.15 tie-break fixes WHICH: `t̃_{s,k}=J+J₁`, Def-4-minimal). Its flat coord is ledger/birth-tied,
NOT arithmetic on the node's local data. **pnp-slot is running the slot-stability page-check**
(hypothesis: substitution-in-place `d_ij = u·d'_ij` ⟹ each divisor keeps its BIRTH CORNER's flat slot
in every later chart ⟹ the map is an IMMUTABLE per-divisor birth record — a `divBirthCoord` field set
at case-1(2)/case-2 births to the corner `flatCoordOf M s ⟨J⟩ ⟨J⟩`, carried VERBATIM by every
transition [congruence maintenance, not invariant work]; the case-1(1) centerIndex = the chosen
divisor's stored birth coord). t07: READ pnp-slot's cert directly; if slot-stable, the u-coord folds
into `qNodeOf`'s case-1 selector as `flatCoordOf M s ⟨J⟩ ⟨J⟩` (the corner) + the `divBirthCoord`
birth-record field + its congruence maintenance through stepCase11/stepAppendAdvance/stepRollover. If
NOT slot-stable, the map is dynamic (bigger) — surface to the controller. The cert also adjudicates
whether `divProfile` alone recovers `(s_birth, J_birth)` without a new field.

## 4. qNodeOf — the Homeomorph assembly (the intricate half; t07's main build)

`qNodeOf (node) : Params M ≃ₜ (Fin d_center → ℝ) × (Fin (flatDim M − d_center) → ℝ)`, node-derived:
1. `paramsEquivFlat M` as a HOMEOMORPH (use `paramsEquivFlatCLE` — the continuous-linear-equiv,
   `ParamsFlat.lean` — its `.toHomeomorph`, or the banked homeomorph; the measurable-equiv
   `paramsEquivFlat` also has continuity both ways, `ParamsFlat.lean:104+`).
2. a permutation `Fin (flatDim M) ≃ Fin d_center ⊕ Fin (flatDim M − d_center)` built FROM the injective
   `centerIndices` (§2 + §3): the center coords are the `Fin d_center` image (injective ⟹ extend to a
   full permutation via `Equiv.Perm` / `Equiv.sumCompl` on the range complement).
3. the `arrowCongr` split `(Fin (flatDim M) → ℝ) ≃ (Fin d_center ⊕ rest → ℝ) ≃ (Fin d_center → ℝ) ×
   (Fin rest → ℝ)` (`Equiv.sumArrowEquivProdArrow`), as a Homeomorph (each step continuous).
Coverage reads ONLY: `qNodeOf node` is a `Homeomorph` and its first factor carries exactly the
`d_center` center coords (so `pivotChart` acts on them, spectators pass through). No other property.
TOTALITY: like `leafOfState`, `qNodeOf` needs `d_center ≤ flatDim M` + injective centerIndices (hold on
reachable nodes); use a `dite`-fallback for the junk-state totality, correctness on the reachable cone.

## 5. Per-case shapes (summary for t07)

- **case-2 node:** center = the residual block `resRows × resCols`; `centerIndices = resBlockCenterIndices
  M s J resRows resCols _ _`; no `u`; `d_center = resRows·resCols`.
- **case-1 node:** TWO edges. case-1(1): `d_center_edge = 1`, the `u`-pivot (§3 parameter). case-1(2):
  `d_center_edge = runLen·resCols`, the d-family = `resBlockCenterIndices M s J runLen resCols _ _`.
  The node's full center = the d-block (runLen·resCols) + `u` (1); per the partition, the selector is
  per-EDGE.
- **rollover:** 0 (chartless, `localSub = id`).

## 6. Verification gate

Full-batch (elder-gate8): full `lake build DLNFibre` green + `#print axioms` on ALL watched roots at
expected footprints + the (2,2,4) witness re-elaboration, one batch. Protected-set re-probe with the
batch (`canonicalResolution224_arithmetic`, `region_glue_of_chartBridge`, `minAdm_le_terminalExponents`,
`isFullMonomialization_buildTree_conRoot` — additive `CenterIndices.lean`/`qNodeOf` must not perturb
them; they're in disjoint files, but confirm). `qNodeOf` node-indexed (seam pin) — no existential.

## 7. Pointers

- Interface: `threads/10-coverage/carrier-interface-proposal.md` (f0a8363fd) + `threads/11-construction/
  carrier-interface-review.md` (mine, 3fe01c45e) + the elder-gate9 verdict (journal tick 206) + tick-208/210.
- Geometry: `threads/10-coverage/page-pin-centers.md` (the case-1/2 centers, VERBATIM); `cert-psi-mix.md`
  (R-b + `α_e`); `threads/15-psi-adjudication/`.
- Reuse: `map/overlay/banked-families.md` § CARRIER-ADJACENT REUSE INDEX (cartographer-4) — pinned
  `file:line` for `ChartSubst`, the `leafPaths`/`leafPathImages` fold family, `node_pivotCover_of_atom`.
- u-pivot: pnp-slot's slot-stability cert (pending) — READ it directly for the `divBirthCoord` verdict.
