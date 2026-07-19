# STATUS — 2026-07-17-aoyagi-engine

updated: 2026-07-19 (cartographer-6, tick 289 — endgame rewrite + placement-check refresh; the
2026-07-17 version pre-dated the entire endgame)

## the one-line position

The engine has ONE analytic hole left: `chartBridge_buildTree` (`EngineObligations.lean:53`). Every
other conjunct of `monomialization_terminates` is clean-three; `o5_realization` closed (t06 s4);
`region_glue` is a proven composition awaiting only the bridge. Discharging `chartBridge_buildTree`
flips `engine_box_threshold_finite` → `hbox` → repoints `aoyagi_learning_coefficient` (the mint). The
discharge routes through the (D) R-split (tick 289, projection-enforced): a HIGH `ChartBridgeFaithful`
module proves the faithful A∧B∧C∧D over `geoAtlas`, and `chartBridge_buildTree` fills as its projection.
The geo-atlas lane now owes only: the fold-Jacobian cocycle (`geoAtlas_fold_det`, task #43) and clause
(D) statement + node-walk (task #44). DONE since tick 265: cover (clean-three, tick 288), per-pivot
emission fix (task #35), fold-spine gate-wiring. Placement VERIFIED clean import-add, no cycle
(wiring-endgame §2e).

## landmarks (8 carried)

  ★ mint-repoint [stated] unconditional mint = gen ∘ hbox + L1 fold; wiring-only once hbox lands
  ★ hbox-root [stated] ∀-M box-threshold finiteness; discharged by `engine_box_threshold_finite`
  ★ engine-route [adopted] transform-only Aoyagi engine: reduce → tree → coverage → thresholds
  ★ resolution-tree [LANDED + validated] edge-labelled carrier; ledger spine 0-sorry (EngineConstruction)
  ★ coverage-theorem [IN FLIGHT — the one hole] `chartBridge_buildTree` via `geoAtlas`; cover t10, fold+D owed
  ★ exponent-ledger-bridge [proven projection] of `resolutionOf_spec`
  ★ theorem4-localization [adjudicated] pure-homogeneity domination (no chain-IH)
  ★ rr4-precedent [adjudicated] (r,r,4) end-to-end 0-sorry (OUTER-plumbing precedent only)

## the engine hole ladder (what feeds `chartBridge_buildTree`)

  ✔ o5_realization [DONE, clean-three] `minAdm ∈ terminalExponents` + live attainment; crux
      `o5_core_realized`/`tStar_realized` landed (t06 s4); `hMpos` required. `o5_core` DELETED from
      EngineConstruction (move-at-landing done).
  ✔ ledger carrier [DONE, 0-sorry] the A→C construction spine (ConState/RootLedger/stepUpdate/leafOfState);
      `leaves_numDiv_le_flatDim`, `minAdm_le_terminalExponents` clean-three.
  ✔ chart-emission carrier [DONE, BEDROCK] QNodeCarrier (736 LoC, 0-sorry, reviewed PASS): per-node
      center `dCenterOfNode` + `dCenterOfNode_edgeSum`/`_le_flatDim` + `qNodeOf` + the q-det trio.
  ✔ reachability (coord clauses) [DONE, clean-three] DivBirthReach: `DivBirthInv_conOracle_stepChildren`
      → `leaves_chart_clauses_conRoot` (divCoord/resCoord inj + disjoint per built leaf).
  ✔ fold-Jacobian SPINE [BANKED sorry-free, GATE-WIRED @13b86217a] GeoJacobianSpec (`geoChartMap_fderiv_det`
      per-edge atom) + GeoJacobianFold (`abs_det_fderiv_foldr_comp` parametric fold); AxCheck:12 import +
      5 watch lines (was a gate-orphan at the carto6 snapshot; closed post-snapshot).
  ✔ cover (clause A) [DONE, clean-three, tick 288] `geoAtlas_imageCover` (GeoCoverSpec.lean:370); 0∈U reshape.
  ✔ per-pivot divCoord/divExp emission fix [DONE — task #35 FINAL] the parametric-gauge seam-fix
      (geoChartMap = (β∘S)∘g, S concrete, g det-1 slot); co-folds chartMap + per-pivot ledger.
  ▶ fold cocycle regrouping [IN FLIGHT — task #43] `geoAtlas_fold_det` (GeoLeafJacobian.lean:35 sorry) —
      the finding-2 regrouping cocycle over the banked atoms (`geoChartMap_swap_fderiv_det` + the fold).
  ▶ clause (D) statement + node-walk [IN FLIGHT — task #44] statement-gate first; dCenterOfEdge-GATED
      phrasing (tick 262 rollover counter-sign). Lands in the HIGH ChartBridgeFaithful module (R-split).
  ⧗ LeafPullback [NOT built] loss-factorization; pnp-loss commissioned (residualCore-leak kill-condition).

## discharge → mint ladder (post-hole) — the (D) R-split, projection-enforced (tick 289)

  ⧗ ChartBridgeFaithful.lean [NEW HIGH module] `def ChartBridgeFaithful` (A∧B∧C∧D) +
      `chartBridgeFaithful_buildTree` discharge + `toChartBridge` projection. Placement VERIFIED clean
      import-add, no cycle (wiring-endgame §2e).
  ⧗ EngineObligations gains `import ChartBridgeFaithful`; `chartBridge_buildTree := (…).toChartBridge`
      (+ hMpos signature widening). CORDON: a direct A∧B∧C fill is a fidelity regression.
  ⧗ AxCheck watch flips chartBridge_buildTree / monomialization_terminates / engine_box_threshold_finite /
      region_glue → clean-three; NEW watch `chartBridgeFaithful_buildTree` MUST-clean-three
      (canonicalResolution224 does NOT flip — separate (2,2,4) sorry).
  ⧗ mint re-point [staged, ~10 lines] land bare `aoyagi_learning_coefficient` on `_gen`; enforced
      axiom-gate (R5 #guard_msgs, extended to chartBridgeFaithful_buildTree).
  ⧗ cordon census [just-before-PR].

## engine-cone sorry census (grep-verified HEAD aac2dc391, tick 289)

  - `EngineObligations.lean:53` — `chartBridge_buildTree` (THE hole; the gate's one live +sorryAx for the spine).
  - `GeoLeafJacobian.lean:35` — `geoAtlas_fold_det` (fold cocycle #43; GATE-ORPHAN so off the build footprint).
  - `ClearableReify.lean:78` — `realizedProfiles_eq_clearableAdm` (R7 reify-now; +sorryAx until R7, expected).
  - `CanonicalWitness224.lean:135` — `canonicalResolution224` (2,2,4) ChartBridge conjunct (separate forecast).
  - (`GeoCoverSpec.lean` cover sorry CLOSED tick 288; plus any live (D)-draft sorry from task #44.)

## deferred / off-critical-path

  - R6 regular-peel transcription (OWED first-class; cost-probe-gated, the SchurCore depth-≥3 wall).
  - R7 `realizedProfiles = Clearable-Adm` full proof (descent invariant §4 + strand obstruction §2).
  - the RlctPayoff layer (needs `minAdm = codim`; the NEXT expedition's runway).
