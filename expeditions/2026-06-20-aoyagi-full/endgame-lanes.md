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

`DecoratedBaseHyp` (#4) = DONE/banked. `DecoratedStepHyp` (#5) = the mountain, TWO tracks:
- **Track (a) L≥1 head-split** = `deeperFlag_spineToCore` (RouteMSJDeeperFlagCore:655) = **F ∘ D-A ∘ (D-B✓+D-C) ∘ D-assembly**.
- **Track (b) L=0 base** (#156) = `deeperFlag_waist` = **Base-Cayley (s≥3) + Base-routeC (s≤2)**, then the base↔recursion wiring.

## LANES (live)

| Lane | Module (NEW) | Tide | Status | Locked statement |
|---|---|---|---|---|
| **D-C core** | `RouteMSJKyFan.lean` | (landed) | ✅ @a09fdd26 clean-three | `finrank_add_weakCount_le` (Rayleigh≥c subspace ⟹ `finrank U + #{λ<c} ≤ k`) |
| **D-C corollary** | RouteMSJKyFan/new | a8215839 | 🔄 running | `shell_subset_goodSet`: shell + box ⟹ `weakEigCount ε' Z_deep ≤ M₂−m` (consumes core; 3 pieces: Fact S / transport+CS / weakEigCount↔#{λ<c}) |
| **D-A** | `RouteMSJPivotBlowup.lean` | abbbbdb7 | 🔄 building (LOCKED) | P-radial blow-up CoV. **Locked**: full-space EXACT equality (B1), ordinary unit sphere (NO det-1 — refuted red herring), owns honest exponent `r^{u·M₁−1}` (drop to `minAdm−1` is downstream on-[0,1] dom), finiteness OUT (D-B banked). Vehicle = banked `RouteMSJRadialPolar`; ~120-180 LoC. Two lemmas: `lintegral_matrix_radial_polar_factor` + `pivotBlock_radial_blowup` |
| **F1 (frame downstream)** | `RouteMSJHeadSplitFrame.lean` | a19e744c | 🔄 building | `exists_headSplitFrame_impl` = verbatim RouteMSJDeeperFlagCore:492-501, EVERYTHING sorry-free around ONE isolated primitive (piecewise `Zf`/off-G data/PSD floor/rank/agreement/G-measurability). Primitive quarantined as clean sorry on branch |
| **F2 (eigendecomp primitive)** | (to commission) | — | ⏸ scoping | measurable Hermitian eigendecomposition of a measurable PSD family (`∃ (lam,U) measurable, A=U diag(lam) Uᵀ`). Mathlib-ABSENT, classical LABOUR. Commission after scout scopes substrate (continuity-of-eigenvalues / CFC-measurability / measurable Gram-Schmidt) — wall-vs-nested-gap check first |
| ~~Base-Cayley / Base-routeC~~ | — | a41b29ac / a0bfe47b | ✅ RESOLVED (stood down) | **3-width base finiteness ALREADY BANKED** — `routeMBoxThresholdFinite_mnp` (RouteMSchurRectCapB:453), unconditional ∀m,n,p, clean-three, load-bearing R1-UPPER atom (verified). SVD/Cayley route redundant. Residual = the #5-compose waist-shell wiring (below) |
| **eigen-coord scout** | `eigen-coord-mathlib-recon.md` | a62dc7e4 | 🔄 running | recon-map: Borel-func-calc / Jacobian-CoV / Weyl-density / O(n)-CoV — PRESENT/ABSENT/BANKED. Off critical path |
| **#108 mint pre-stage** | `RouteMSJMint.lean` | controller | (this tick) | `aoyagi_learning_coefficient_gen_of_descent`: conditional wiring `DecoratedDescent → _gen unconditional` |

## D-assembly (the JOIN — NOT parallel; runs after D-A + D-C + F land)

Fills `headSplit_domination` (RouteMSJDeeperFlagCore:513) by consuming D-A (pivot reorg) + D-B (`RouteMSJRankRCodim`, ✅) + D-C corollary (`shell_subset_goodSet`) + F frame + S3 (`shell_corankOffSector_le_unif`, banked) + L1 (`deeperFlag_shell_core_le`, banked). Then `deeperFlag_spineToCore` (:655) closes via `exists_headSplitFrame ∘ headSplit_domination`. Controller-owned (edits the shared module).

## Interface risks tracked

- **D-A ↔ D-assembly**: D-A's standalone statement must yield `commonDivisor(v)²·frobSq(Q̃_p)=decLoss` + monomial `∏|v_ℓ|^{jc_ℓ}` + finite `C_hle`. Checkpoint-locked before grind. Riskiest: angular C_hle finiteness (s1-Chle cert — σ_min(P̂) bounded below on det-1 sphere).
- **Cayley ↔ routeC**: the two base bricks MUST produce the same statement shape (differ only in s-range) so `deeperFlag_waist` = their union. Relay Cayley's locked statement to routeC.
- **F measurability**: Borel-func-calc eigen-frame selector may hit a thin Mathlib primitive → scout pre-maps; F isolates a minimal named gap if genuinely absent.
- **★ #5-compose waist-shell wiring (the live open architecture question).** The 3-width base finiteness is banked (`routeMBoxThresholdFinite_mnp`, all widths). The OPEN piece: how the hpiv-FAILING waist shells of `DecoratedStepHyp` are discharged — does the waist shell reduce to bare `RouteMBoxThresholdFinite` on a 3-width leaf (→ `_mnp` closes it), or need a `shellSpineIntegrand → 3-width-box` reduction lemma? Route-B orientation (peel good end) was REFUTED (no guaranteed good end, waist (2,1,2)), so the recursion structure that reaches 3-width leaves is unsettled. Downstream of D-assembly; controller to scope at #5-compose. NOT an SVD build.
- **F2 wall-vs-labour**: the measurable-eigendecomposition primitive is classical/true but may lean on a Mathlib-absent measurable-selection substrate (Kuratowski–Ryll-Nardzewski / measurable Gram-Schmidt). Scope (scout + possible pen-and-paper decorrelated) BEFORE committing a build tide — if a nested gap makes it a genuine wall, surface; else commission.
- **L=1 at mint**: `_gen` needs `hL2:2≤L`; the unsuffixed headline (L≥1) needs the L=1 case via the separate unconditional path — a mint-time item, not blocking the pre-stage.

## Canonical

HEAD @abdf5fca (0-sorry/0-axiom, clean-three). Tides build in worktrees off origin/expedition/aoyagi-full; controller integrates.
