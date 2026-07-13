# endgame-lanes.md — the parallel-lane interface tracker (controller-owned, durable)

**Purpose (operator directive 2026-07-13).** The (□) endgame runs as PARALLEL LANES, not the serial
`D → F → base` chain. This doc is the controller's durable interface ledger: each lane's LOCKED statement
(what it PRODUCES + CONSUMES), its module, its worktree tide, and status. The controller integrates each
landed module one-at-a-time into the main checkout (wires aggregator + AxCheck, green-gates, commits) —
**tides never touch `DLNFibre.lean` / `AxCheck.lean` / `RouteMSJDeeperFlagCore.lean`**; those are
controller-single-writer. Refresh every tick.

## The target chain (unchanged)

`DecoratedDescent` (RouteMSJDecoratedRec:206 = `∃ adm, htriv ∧ DecoratedStepHyp adm ∧ DecoratedBaseHyp adm`)
→ driver `routeMBoxThresholdFinite_of_decoratedDescent` (:216, clean-three) → `(□) ∀M`
→ `aoyagi_learning_coefficient_gen`'s `hbox` slot → unconditional `_gen` → re-point unsuffixed `#108`.

**★ MILESTONE (2026-07-13): the (□) discharge is now decorrelated-confirmed LABOUR to the end — ZERO walls.** The last wall-candidate (Brick F's measurable eigen-frame) resolved to LABOUR (F2 adjudication a3648768: concrete Borel formula, no KRN). Every remaining piece is bounded labour with a banked or recipe'd route.

`DecoratedBaseHyp` (#4) = DONE/banked. `DecoratedStepHyp` (#5) = the mountain, TWO tracks:
- **Track (a) L≥1 head-split** = `deeperFlag_spineToCore` (RouteMSJDeeperFlagCore:655) = **F ∘ D-A✓ ∘ (D-B✓ + D-C✓) ∘ D-assembly**. Brick D bricks ALL landed (D-A @e45d434d, D-B, D-C core+corollary); F = F1 (building, around 1 isolated primitive) + F2 (building the primitive). Remaining track-(a) Lean: **D-assembly** (the join) + **F1/F2**.
- **Track (b) L=0 base** = the 3-width waist finiteness is **BANKED** (`routeMBoxThresholdFinite_mnp`, all widths); residual = the #5-compose waist-shell wiring (below), downstream.

## LANES (live)

| Lane | Module (NEW) | Tide | Status | Locked statement |
|---|---|---|---|---|
| **D-C core** | `RouteMSJKyFan.lean` | (landed) | ✅ @a09fdd26 clean-three | `finrank_add_weakCount_le` (Rayleigh≥c subspace ⟹ `finrank U + #{λ<c} ≤ k`) |
| **D-C corollary** | `RouteMSJShellContain` | ✅ @e45d434d | landed clean-three | `shell_subset_goodSet`: `A'₀·Z_deep ∈ singularShell` + box ⟹ `weakEigCount ε' Z_deep ≤ M₂−m` (Fact S / transport+CS / count-bridge, on the banked core). Self-reviewed 7 checks + Codex; controller fidelity-reviewed |
| **D-A** | `RouteMSJPivotBlowup.lean` | ✅ @e45d434d | landed clean-three | P-radial blow-up CoV. Full-space EXACT equality, ordinary unit sphere (no det-1), honest exponent `r^{u·M₁−1}` (drop downstream), finiteness OUT (D-B banked). `pivotBlock_radial_blowup` + reusable `lintegral_matrix_radial_polar_factor`. Vehicle = banked `RouteMSJRadialPolar`; 186 LoC. Controller fidelity-reviewed |
| **F1 (frame downstream)** | `RouteMSJHeadSplitFrame.lean` | ✅ @origin/genm-sj5-brickF1 (2cdda05b) | done, gated on F2 | `exists_headSplitFrame_impl` = verbatim RouteMSJDeeperFlagCore:492-501 (controller fidelity-confirmed), all 6 conjuncts PROVED around the ONE quarantined `measurableEigendecomp` sorry (= the F2 contract, verbatim). 395 LoC, green; clean-three once F2 lands. Reusable bricks left in-module (measurable_matrix_iff, antitone_tail_bound, frame0/mat0, floor_psd_aux) |
| **F2 (eigendecomp primitive)** | `RouteMSJMeasurableEigendecomp` (assembly @origin/genm-sj5-brickF2-assembly) | ladder (adjud a3648768 ✅ LABOUR) | 🔄 2 sub-tides | VERDICT LABOUR, no wall — but a ~2200-4500 LoC / **6-module MOUNTAIN** (every spectral-measurability primitive Mathlib-absent; decorrelated tide+Codex). Assembly banked (`frame_diagonalizes` clean-three + 2 recipe'd sorries). **F2a** (#163, ab20e852): `measurableEigenvalues₀` via Vieta+Lusin–Souslin (~450-950 LoC). **F2b** (#164, aa147a6d, checkpoint-first): eigenframe via zero-safe Lagrange projector + measurable pivot (~1350-2750 LoC, takes hλmeas as hyp). discuss#140 |
| **eigen-coord scout** | `eigen-coord-mathlib-recon.md` | a62dc7e4 | ✅ DONE | 3/4 lanes only PRESENT/BANKED (Weyl/SVD density absent but OFF-PATH); sole void = Cluster-1 Brick-F measurable frame. 2 surprises pre-paid (below) |
| ~~Base-Cayley / Base-routeC~~ | — | a41b29ac / a0bfe47b | ✅ RESOLVED (stood down) | **3-width base finiteness ALREADY BANKED** — `routeMBoxThresholdFinite_mnp` (RouteMSchurRectCapB:453), unconditional ∀m,n,p, clean-three, load-bearing R1-UPPER atom (verified). SVD/Cayley route redundant. Residual = the #5-compose waist-shell wiring (below) |
| **#108 mint pre-stage** | `RouteMSJMint.lean` | ✅ @c8302a0e | landed (green 8618) | `aoyagi_learning_coefficient_gen_of_descent`: conditional wiring `DecoratedDescent → _gen unconditional` verified end-to-end |

## Track-(a) integration DAG (the reconciliation order, controller-owned, when the branch bricks land)

All track-(a) bricks are built on branches (gaps quarantined); canonical stays clean-three. Integration order once the sub-bricks land:
1. **F2a** (`RouteMSJOrderedRootsMeasurable`, afbf70d4) → `measurableEigenvalues₀`; **F2b** (`RouteMSJMeasurableEigenframe`, aa147a6d) → `exists_measurableEigenframe`.
2. Reconcile **F2 assembly** (`RouteMSJMeasurableEigendecomp`, @origin/genm-sj5-brickF2-assembly): import F2a+F2b, replace its 2 sorries → `measurableEigendecomp` clean-three.
3. Reconcile **F1** (`RouteMSJHeadSplitFrame`, @origin/genm-sj5-brickF1): import the F2 assembly, DROP its local duplicate `measurableEigendecomp` sorry (same statement, verbatim) → `exists_headSplitFrame_impl` clean-three.
4. **GLUE-2** (7th brick, pending D-assembly's isolated statement) → closes `headSplit_domination_impl` (`RouteMSJHeadSplitDom`, a8a42c82 branch).
5. Controller fills the RouteMSJDeeperFlagCore stubs: `exists_headSplitFrame` := F1's impl; `headSplit_domination` := the D-assembly impl; then `deeperFlag_spineToCore` = compose → wire aggregator+AxCheck, green-gate clean-three, commit.

## D-assembly (the JOIN — NOT parallel; runs after D-A + D-C + F land)

**STATUS (2026-07-13):** `headSplit_domination_impl` ASSEMBLED sorry-free in its body (`RouteMSJHeadSplitDom` @origin/genm-sj5-headsplit-dom 71c2b6a6, green), reducing to TWO isolated correct-statement sorries:
- **GLUE-2** `headSplit_pivotDom` (the analytic crux — coupled pivot→decLoss domination, drops B₁₂·Q_b, non-pointwise): a SEPARATE tide a88527065 (#165, checkpoint-first, `RouteMSJPivotDom`), design = D-A + D-B + s1-Chle cert. The ~65-75%-new content, decorrelated-adjudicated labour.
- **`shellSpine_le_hsQ_box`** (the ~120-150-line head/row-split measure reduction — NOT bounded plumbing, honest re-scope): D-assembly tide a8a42c82 grinding it in-place (paramsHeadSplit + shell-indicator Tonelli + rowSplit + recombine + D-C rewrite).

On both + D-A✓/D-B✓/D-C✓: `headSplit_domination_impl` clean-three. Then `deeperFlag_spineToCore` = `exists_headSplitFrame(F1) ∘ headSplit_domination`. Controller wires the RouteMSJDeeperFlagCore stubs + breaks the `hsQ` import cycle at integration.

## Interface risks tracked

- **D-A ↔ D-assembly**: D-A's standalone statement must yield `commonDivisor(v)²·frobSq(Q̃_p)=decLoss` + monomial `∏|v_ℓ|^{jc_ℓ}` + finite `C_hle`. Checkpoint-locked before grind. Riskiest: angular C_hle finiteness (s1-Chle cert — σ_min(P̂) bounded below on det-1 sphere).
- **Cayley ↔ routeC**: the two base bricks MUST produce the same statement shape (differ only in s-range) so `deeperFlag_waist` = their union. Relay Cayley's locked statement to routeC.
- **F measurability**: Borel-func-calc eigen-frame selector may hit a thin Mathlib primitive → scout pre-maps; F isolates a minimal named gap if genuinely absent.
- **★ #5-compose waist-shell wiring (the live open architecture question).** The 3-width base finiteness is banked (`routeMBoxThresholdFinite_mnp`, all widths). The OPEN piece: how the hpiv-FAILING waist shells of `DecoratedStepHyp` are discharged — does the waist shell reduce to bare `RouteMBoxThresholdFinite` on a 3-width leaf (→ `_mnp` closes it), or need a `shellSpineIntegrand → 3-width-box` reduction lemma? Route-B orientation (peel good end) was REFUTED (no guaranteed good end, waist (2,1,2)), so the recursion structure that reaches 3-width leaves is unsettled. Downstream of D-assembly; controller to scope at #5-compose. NOT an SVD build.
- **F2 wall-vs-labour** (LIVE adjudication a3648768): the primitive `measurableEigendecomp` is classical/true; the KRN risk is isolated to measurable `U` through degenerate eigenspaces (sorted form removed the column-choice risk). Pen-and-paper adjudicating the resolvent-Riesz+gramSchmidt-without-KRN route; verdict → build recipe (labour) or escalate (wall). Conjunct (i) reduces to sorted-eigenvalue continuity (~1-module Weyl brick).
- **★ scout surprises pre-paid (import hygiene — bites EVERY eigen-coord lane's signature):** (#1) `Matrix (Fin m)(Fin n) ℝ` has NO Mathlib `MeasurableSpace` instance — any `Measurable (·: X → Matrix …)` MUST `import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution` (banked `instMeasureSpaceMatrixFinFin`) or use entrywise `RouteMSmearedPerFamily.measurable_matrix*`, else the signature won't elaborate. (#2) nested-pi `IsAddHaarMeasure` doesn't resolve by bare `infer_instance` — route linear/orthogonal CoV through the banked `RouteMSJGammaAtom.*ₚ` / `RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ`, not fresh Mathlib Haar-CoV calls.
- **L=1 at mint**: `_gen` needs `hL2:2≤L`; the unsuffixed headline (L≥1) needs the L=1 case via the separate unconditional path — a mint-time item, not blocking the pre-stage.
- **★ mint axiom footprint CONFIRMED clean-three (2026-07-13):** `aoyagi_learning_coefficient_gen` is `[propext, Classical.choice, Quot.sound]` — NO cited-Aoyagi axiom. `cited_aoyagi_dln` is a hypothesis-field of `RlctInterface`, used only in the SEPARATE `RlctPayoff`/`RlctPayoffGeneral` framing, NOT in the `_gen` headline (which computes the RLCT value directly via D1/L2/R1 given (□)). ⟹ the mint `_gen ∘ discharge` is genuinely UNCONDITIONAL + clean-three once `DecoratedDescent` lands — the "Cited Aoyagi" caveat applies to the alternate codim→RLCT payoff exposition, not the headline value.

## Canonical

HEAD @abdf5fca (0-sorry/0-axiom, clean-three). Tides build in worktrees off origin/expedition/aoyagi-full; controller integrates.
