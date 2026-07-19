# STATUS — 2026-07-17-aoyagi-engine

updated: 2026-07-19 (cartographer-6, tick 265+ — full endgame rewrite; the 2026-07-17 version
pre-dated the entire endgame)

## the one-line position

The engine has ONE analytic hole left: `chartBridge_buildTree` (`EngineObligations.lean:53`). Every
other conjunct of `monomialization_terminates` is clean-three; `o5_realization` closed (t06 s4);
`region_glue` is a proven composition awaiting only the bridge. Discharging `chartBridge_buildTree`
flips `engine_box_threshold_finite` → `hbox` → repoints `aoyagi_learning_coefficient` (the mint). The
discharge is the `geoAtlas` fed to `chartBridge_of_pieces`; the geo-atlas lane owes: cover (t10),
per-pivot emission fix (finding 3), fold regrouping+instantiation (finding 2 cocycle), and clause (D)
landing.

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
  ▶ cover (clause A) [IN FLIGHT — t10] `geoAtlas_imageCover` (GeoCoverSpec.lean:38 sorry); 0∈U reshape.
  ⧗ fold cocycle regrouping + instantiation [GATED — finding 2] pnp-fold cert running (the 3 per-case
      intermediate-point substitution identities) + task #30 (regroup onto source-w ledger).
  ⧗ per-pivot divCoord/divExp emission fix [PENDING — finding 3, task #35] geoAtlas inherits the leaf's
      divCoord; each fan-out copy needs its OWN pivot's exceptional coord. Transfers to t11 post-t10.
  ⧗ LeafPullback [NOT built] loss-factorization; pnp-loss commissioned (residualCore-leak kill-condition).
  ⧗ clause (D) landing [GATE — task #10] (D) must be IN the ChartBridge type BEFORE the discharge;
      dCenterOfEdge-GATED phrasing (tick 262 rollover counter-sign).

## discharge → mint ladder (post-hole)

  ⧗ t12-assembly seat [spawns at t10 merge] (D) + `chartBridge_of_pieces` discharge + the mechanical
      import/watch-flip batch (wiring-endgame §2). Coverage contributes its nodes_cNode walk.
  ⧗ AxCheck watch flips [staged] chartBridge_buildTree / monomialization_terminates /
      engine_box_threshold_finite / region_glue → clean-three (canonicalResolution224 does NOT flip —
      separate (2,2,4) sorry).
  ⧗ mint re-point [staged, ~10 lines] land bare `aoyagi_learning_coefficient` on `_gen` (avoid the 3
      legacy Skeleton stubs); enforced axiom-gate.
  ⧗ cordon census [just-before-PR].

## engine-cone sorry census (4, grep-verified HEAD c342c55fb)

  - `EngineObligations.lean:53` — `chartBridge_buildTree` (THE hole; the gate's one live +sorryAx for the spine).
  - `ClearableReify.lean:78` — `realizedProfiles_eq_clearableAdm` (R7 reify-now; +sorryAx until R7, expected).
  - `CanonicalWitness224.lean:135` — `canonicalResolution224` (2,2,4) ChartBridge conjunct (separate forecast).
  - `GeoCoverSpec.lean:38` — `geoAtlas_imageCover` (t10; GATE-ORPHAN, so off the build's +sorryAx footprint).

## deferred / off-critical-path

  - R6 regular-peel transcription (OWED first-class; cost-probe-gated, the SchurCore depth-≥3 wall).
  - R7 `realizedProfiles = Clearable-Adm` full proof (descent invariant §4 + strand obstruction §2).
  - the RlctPayoff layer (needs `minAdm = codim`; the NEXT expedition's runway).
