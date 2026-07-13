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
| **D-A** | (checkpoint pending) | abbbbdb7 | 🔄 checkpoint-first | P-radial blow-up CoV: `∫_P f = ∫_{v,ang} f(commonDivisor(v)·P̂)·∏|v_ℓ|^{jc_ℓ}·w`, `|det P̂|=1`, angular/C absorbed → finite `C_hle<⊤`. Anchor (3,3,3): `commonDivisor=|v₀|`, `jc=[5]`, thr `3=½minAdm(2,3)` |
| **F (U_s frame)** | `RouteMSJHeadSplitFrame.lean` | a19e744c | 🔄 running | `exists_headSplitFrame_impl` = verbatim RouteMSJDeeperFlagCore:492-501 (piecewise `Zf`/`U_sf`, Borel functional calculus m-frame). LOCKED (stub already in Lean) |
| **Base-Cayley** (s≥3) | (checkpoint pending) | a41b29ac | 🔄 checkpoint-first | 3-width `(x,s,z)`, `s≥3`: `∫_box ‖A₀A₁‖_F^{−2c}<⊤`, `c<½minAdm`; via Cayley `|det DΦ|=2^{s(s−1)/2}∏|λᵢ−λⱼ|det(I+K)^{−(s−1)}` → qPeel. Scope: general-s vs anchor(4,3,4) — TBD checkpoint |
| **Base-routeC** (s≤2) | (checkpoint pending) | a0bfe47b | 🔄 checkpoint-first | 3-width `(x,s,z)`, `s≤2`: same box-integral shape as Cayley, via triangular Gram–Schmidt → qPeel. MUST share Cayley's statement shape (compose to full base) |
| **eigen-coord scout** | `eigen-coord-mathlib-recon.md` | a62dc7e4 | 🔄 running | recon-map: Borel-func-calc / Jacobian-CoV / Weyl-density / O(n)-CoV — PRESENT/ABSENT/BANKED. Off critical path |
| **#108 mint pre-stage** | `RouteMSJMint.lean` | controller | (this tick) | `aoyagi_learning_coefficient_gen_of_descent`: conditional wiring `DecoratedDescent → _gen unconditional` |

## D-assembly (the JOIN — NOT parallel; runs after D-A + D-C + F land)

Fills `headSplit_domination` (RouteMSJDeeperFlagCore:513) by consuming D-A (pivot reorg) + D-B (`RouteMSJRankRCodim`, ✅) + D-C corollary (`shell_subset_goodSet`) + F frame + S3 (`shell_corankOffSector_le_unif`, banked) + L1 (`deeperFlag_shell_core_le`, banked). Then `deeperFlag_spineToCore` (:655) closes via `exists_headSplitFrame ∘ headSplit_domination`. Controller-owned (edits the shared module).

## Interface risks tracked

- **D-A ↔ D-assembly**: D-A's standalone statement must yield `commonDivisor(v)²·frobSq(Q̃_p)=decLoss` + monomial `∏|v_ℓ|^{jc_ℓ}` + finite `C_hle`. Checkpoint-locked before grind. Riskiest: angular C_hle finiteness (s1-Chle cert — σ_min(P̂) bounded below on det-1 sphere).
- **Cayley ↔ routeC**: the two base bricks MUST produce the same statement shape (differ only in s-range) so `deeperFlag_waist` = their union. Relay Cayley's locked statement to routeC.
- **F measurability**: Borel-func-calc eigen-frame selector may hit a thin Mathlib primitive → scout pre-maps; F isolates a minimal named gap if genuinely absent.
- **Base↔recursion wiring** (deferred, controller): route-B orientation for ≥4-width + SVD-qPeel 3-width leaf (routeA-waist cert §"Architectural note"). A minAdm-combinatorics adjudication, not analytic.
- **L=1 at mint**: `_gen` needs `hL2:2≤L`; the unsuffixed headline (L≥1) needs the L=1 case via the separate unconditional path — a mint-time item, not blocking the pre-stage.

## Canonical

HEAD @abdf5fca (0-sorry/0-axiom, clean-three). Tides build in worktrees off origin/expedition/aoyagi-full; controller integrates.
