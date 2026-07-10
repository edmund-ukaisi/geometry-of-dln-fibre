# genm-threadedshear — build spec: CLOSE the crux `normalSlice_transfer` → discharge `(□)`

**Route decided (controller, 2026-07-10):** the crux is the sole remaining sorry on the front-peel
carrier. fpcarrier reduced everything else (6 pieces axiom-clean); the residue is the **opaque-width
threaded-shear CoV**. This tide closes it. The math is **FULLY WITNESSED** — you are formalising a
settled result, not searching. **READ FIRST (in full):**
- `threads/genm-vslice/normalslice-cert.md` — the mathematical witness (threaded normal form §2, unit
  Jacobian ±1 §3, additive charge §4, codim reconciliation §5, Lean-friendliness/bricks §6, handoff §8).
- `threads/genm-fpcarrier/codex/normalslice-decomp-answer.md` — the decorrelated Lean **lemma DAG** (the
  `NormalSliceChartData` interface pattern, the entry point, the walls, the restatement flags).
- `stage2-brief.md` (charter: det-inverse compass, escalation bar) + `threads/genm-fpcarrier/spec.md`
  (the W1 carrier context) + `lean/CLAUDE.md` (opaque-width technique).

## GOAL
Close `normalSlice_transfer` — the SOLE `sorry` (line ~226) in
`lean/DLNFibre/DLN/RLCT/Validate/RouteMFrontPeelCarrier.lean` on branch `genm-fpcarrier @ 1cc8db60`.
When it lands, `RouteMFrontPeelCarrier` is **sorry-free** ⇒ `routeMBoxThresholdFinite_frontPeel`
proves `(□) = RouteMBoxThresholdFinite M` ∀M ⇒ `aoyagi_learning_coefficient_gen` goes unconditional.
**This tide IS the finish line for Stage 2.** Standing invariant: **canonical stays 0-sorry/0-axiom —
all gaps live on THIS branch only**; every landed piece force-recompiled `#print axioms` clean-three
(`[propext, Classical.choice, Quot.sound]`); single-writer.

## BRANCH / OWNERSHIP
- Worktree from `origin/genm-fpcarrier @ 1cc8db60`; push to a NEW branch `genm-threadedshear`
  (`git ls-remote --heads origin genm-threadedshear` first; if taken, `-2`).
- You **own** `RouteMFrontPeelCarrier.lean` (fpcarrier is DONE — the single-writer slot is yours now)
  **and** the new file `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJThreadedShear.lean`.

## ROUTE — the `NormalSliceChartData` interface pattern (Codex decomp §4, "cleanest decomposition")
Do NOT define global `α/K/Y` recursion as ordinary Lean functions first. Prove `normalSlice_transfer`
from an **abstract finite chart datum**; then the only hard residue is constructing that datum.

**(A) Define `NormalSliceChartData M q`** (record / structure). Fields (Codex §1.5 + §5 flags):
   - a finite chart index set + the pivot-chart cover of `{rank P ≥ q}` (reuse `pivotLocus_eq_iUnion`);
   - a measure-preserving coordinate equiv on each chart (the threaded shear; abs-Jacobian 1);
   - reduced `Y : Params (redTail M q)` (`redTail M q = fun i => M i.succ - q`) + Morse block `R`;
   - a pointwise loss domination/equality `frobSq(A₀·P) ≃ ‖R‖² + frobSq (prod (redTail M q) Y)`;
   - **domain-domination for `hIH`** (Codex flag 2: chart images may be translated/enlarged — carry a
     bounded-domain domination field, OR prove bounded-domain stability of `RouteMBoxThresholdFinite`).

**(B) Prove `normalSlice_transfer` FROM the interface** [REACHABLE — do this FIRST to structure the file]:
   finite chart sum (`pivotChartCover_matBox_le_sum`) + each chart finite (`morseCore_residual_lt_top`
   [BANKED, fpcarrier] on the disjoint `‖R‖²+‖Z‖²` split, exponent shifted by `shiftedThreshold`
   [BANKED, fpcarrier]) + the reduced-chain finiteness = `hIH` at arity `L−1`. This closes the carrier
   sorry **modulo the interface being inhabited**.

**(C) CONSTRUCT the interface data** — the HARD opaque-width bricks, in `RouteMSJThreadedShear.lean`:
   - **The block-shear identity (THE ONE NEW BRICK)**: `M_i · X_i · M_{i+1}⁻¹ = [[α_i, B_i],[0, Y_i]]`
     block-upper-tri at opaque widths, with `α_i = A_i + B_i K_{i+1}`, `K_i = γ_i α_i⁻¹`, `Y_i = D_i −
     γ_i α_i⁻¹ B_i`, `K_L = 0` (cert §2). **L=2 single-matrix base is BANKED `frobSq_schur_block_split`
     (RouteMSJChartAlgebra:107); lift + thread.** (The `K_{i+1}` threading is LOAD-BEARING — naive
     independent-Schur is FALSE, cert §2 note.)
   - `tailThread_rank_eq`: `rank P = q + rank (prod (redTail M q) Y)` [telescoping §2; on the chart every
     `α_i` invertible ⇒ `α_1···α_{L-1}` unit ⇒ `rank_fromBlocks_zero_offdiag` + rank transport].
   - `tailThread_rank_eq_q_iff`: `rank P = q ↔ prod (redTail M q) Y = 0` [`Matrix.rank_eq_zero_iff`].
   - **MP of the threaded shear** (Codex flag 3 — state the ACTUAL measurable equiv + Jacobian, NOT the
     "α⁻¹ as units" slogan): compose right unit-triangular shears + the Schur shear, each Jacobian 1
     (generalise banked `measurePreserving_shearSub` RouteMSJPivotChart:337).
   - `frontLoss_normalSlice_split`: the `‖R‖²+‖Z‖²` disjoint-block split (R from `X₀`, Z from tail).

## CONFIRMED Mathlib bricks (Codex, v4.29 — do NOT re-search)
`Matrix.rank_mul_eq_left_of_isUnit_det`, `Matrix.rank_mul_eq_right_of_isUnit_det`,
`Matrix.rank_fromBlocks_zero_offdiag`, `Matrix.rank_eq_zero_iff`. Local repo bricks: see cert §6 + the
banked list below.

## BANKED (consume verbatim; do NOT re-derive)
`frobSq_schur_block_split` (L=2 base, RouteMSJChartAlgebra:107) · `mul_three_reassoc` (dependent-dim
reassoc) · `measurePreserving_shearSub` (RouteMSJPivotChart:337) · `pivotLocus_eq_iUnion`
(RouteMSJPivotChart:307) + `pivotChartCover_matBox_le_sum` · `morseCore_residual_lt_top` +
`shiftedThreshold` + `prod_tailChain_rank_le_tailMin` + `outerRankCover` (ALL on the carrier, fpcarrier,
axiom-clean) · `radial_morse_residual_power_le` (RadialResidualPower:157) + `lintegral_eq_polar`
(RouteMSJSphereBlowup:82) · `sumSqND_box_lt_top`.

## RESTATEMENT FLAGS (Codex — heed or the proof will not close)
1. **The `c' = M₀q/2` equality case** — the log endpoint, OUT of scope of both regime bricks. Add a
   lemma for it (Lean WILL hit equality; the cert's regimes only say `≷`).
2. **`hIH` domain translation** — `hIH` is for `paramsBoxM _ 1`; chart images may be translated/enlarged.
   Handle via a domain-domination field in `NormalSliceChartData` OR bounded-domain stability.
3. **"α⁻¹ only as units" is NOT a Lean statement** — state the actual measurable equivalence + its
   Jacobian/domination lemma. `⅟`→`⁻¹` via `invOf_eq_nonsing_inv` after `A.invertibleOfIsUnitDet hA`.

## OPAQUE-WIDTH PATTERNS (Codex walls §3 + lean/CLAUDE.md — the finicky part)
Keep everything in `Matrix (Fin q ⊕ Fin (M i − q)) …`; use `blockSplitEquiv`/`finSplit`, **NOT entrywise
casts**. Reassociate via fully-applied `mul_three_reassoc` (never `rw [Matrix.mul_assoc]`). Per-entry
block identities: `have`s at explicit indices `⟨k, by omega⟩`, close post-`fin_cases` with `exact`
(don't hope `simp` sees dependent-`Fin` defeqs). Work in the `Params`/Pi form, per-entry diff, no
`fin_cases` on opaque rows. ASCII binders (`al_i`, `Yt` — no `α̃`/`φ`). `decide +kernel`, not
`native_decide`. `0·∞=0` positivity guard on any corner product.

## DISCIPLINE
- `lean/scripts/lb` ONLY (never bare `lake`); do NOT `lake exe cache get` in the worktree.
- Green-gate the FULL `lake build DLNFibre` (via `lb`) before calling ANY piece integration-ready
  (catches sibling name clashes); confirm axiom footprints with **force-recompiled** `#print axioms`
  (AxCheck), never a bare build exit-0.
- Incremental push to `genm-threadedshear`; honest partials land continuously. Checkpoint + SendMessage
  the controller (≤180 chars) at: **(B) interface + assembly green** (carrier sorry-free-modulo-data),
  then **each brick in (C)**, then **full carrier sorry-free + AxCheck clean-three**.
- The math is witnessed ⇒ expect pure labour. Fire a decorrelated `local-codex-consult` if a brick's
  Lean route is ambiguous. If a brick resists, **isolate a minimal named sub-sorry, build everything
  above it, and report** (standing decision 7) — do NOT halt, do NOT surface a "wall" unless it is a
  decorrelated-confirmed non-labour obstruction that no native re-expression routes around (the compass:
  a surviving det-inverse in a Jacobian = re-express via unit-triangular shears, cert §3 — NOT a wall).
- Native rank-normal-form linear algebra ONLY; do NOT cite the L&R quiver `addlongest` (per `addlongscope`
  independence — this result stands on Mathlib rank lemmas, not the paper's combinatorics).
