# genm-rescopefin — head-split (a)/hstrict per-shell finiteness (subset route)

**Seat:** formalisation (tide). **Base:** `origin/genm-sj5-good` @ `8672869f6`.
**Branch:** `genm-sj5-rescopefin`. **Module:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJShellSubset.lean`.

## Target (as briefed)
For `1 ≤ j < r`, `shellSpineIntegrand M (t★+j) κ ε r ⟨j⟩ c' < ⊤` for `c' < carrierThreshold M = ½·minAdm M`
(**T1**, the whole-chain carrier), NOT the per-cut comparator range T2. Design-first (pen-and-paper +
decorrelated Codex), then formalise via the subset/mnp route.

## Delivered (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`, forced `#print axioms`)
- `shellSpineIntegrand_le_layerBox` — the subset bound `shellSpineIntegrand M u κ ε r jf c' ≤
  routeMLayerBoxIntegral M c' 1` (general M, any flag level, `u ≤ M 0`). No domination constant.
- `shellSpineIntegrand_lt_top_of_box` — finiteness for `c' < T1`, given `RouteMBoxThresholdFinite M`.
- `shellSpineIntegrand_lt_top_leaf` — **L=0 finiteness UNCONDITIONAL** via banked `routeMBoxThresholdFinite_mnp`.
- Helpers: `shellSpine_inner_le_matBox` (per-`A'` un-free + block-reindex + drop pivot chart),
  `tailFront_box_eq_layerBox` (head-split reassembly to the bare box).

## Route (subset/mnp, decorrelated-confirmed sound)
Per `A'`: un-free (`chartInner_schurShearFree_eq` + `frobSq_schur_split_inv`) → block-reindex
(`chartInner_blockReindex_eq_of_emb`) → drop `IsUnit P` + shell (monotone) → head-split reassembly
(`paramsHeadSplit`/`_mp`/`_preimage_box` + `prod_headSplit`). The subset/mnp route CLOSED it — no
strong-minor-chart stratification was needed for the finiteness. Own Codex (xhigh, no repo access,
`codex/rescope-answer.md`) concurs on every load-bearing point.

## Scope / soundness (load-bearing, next to the claim)
- **Target T1, never T2** (anti-regression): the domination `deeperFlag_shell_le` uses the comparator
  finite up to T2; the SUBSET route uses the full box finite up to T1 — the correct, provable target.
- **L≥1 RLCT banking:** `RouteMBoxThresholdFinite M` is banked only for L=0 (mnp). For L≥1 it is the named
  open analytic gap (the recursion's own goal / the paper's codim result) — carried as an explicit
  hypothesis in `_of_box`, NOT buried.
- **Circularity (the key finding):** the subset bound is CIRCULAR for the box-finiteness induction (it
  bounds a peel-component of the chain-M box by the chain-M box). So it does NOT provide the
  reduced-comparator domination the capstone's L≥1 recursion needs. It closes the STATED per-shell
  finiteness target; the capstone's L≥1 domination remains Brick D (strong-minor). This matches
  shelljhunt §5 and Codex Q4.

## For the controller (integration + a landmine)
- `deeperFlag_shell_le` (`RouteMSJDeeperFlagCore.lean:750`) is FALSE as stated (only the lower bound
  `ab/2 < c'`, no upper bound) → its Brick D sorry is unprovable for `j > r/2`. Precise fix (shelljhunt):
  add `hc' : c' < carrierThreshold M`, threaded through `deeperFlag_spineToCore`, `headSplit_domination`,
  and its 4 consumers (`RouteMSJShellCover`, `RouteMSJDecoratedStep`, `RouteMSJDeeperFlagShell`,
  `AxCheck`). This is a shared-driver multi-file change — left to the controller (not a leaf-executor
  unilateral edit, to avoid conflicting with in-flight teammates).
- New module NOT yet wired into `DLNFibre.lean` (single-writer). Controller to add the import.

## Labour-vs-wall verdict (the one remaining sub-piece, for the CAPSTONE)
The stated per-shell finiteness is CLOSED. The capstone's L≥1 reduced-comparator domination (Brick D
`headSplit_domination`) is LABOUR, not a Mathlib wall (rescoperecon Risk-B: strong-minor Schur/GS charts,
uniform Jacobian, banked ½ab charge `shell_corankOffSector_le_unif`/`shell_corankPivot_coupled_le`, D-A
CoV `pivotBlock_radial_blowup`) — but the subset route does NOT shortcut it (circular for the induction).
