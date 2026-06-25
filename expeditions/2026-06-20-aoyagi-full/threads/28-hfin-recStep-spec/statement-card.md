# Statement card — hfin recursive-cover SPEC (build-ready lemma families for r1-node-bundle)

**Status:** DESIGN spec (no Lean). The build-ready design of the hfin (`cover_le`) recursive coupled
cover, as 3 lemma families with precise Lean-target statements, dependency order, S2/S2-free leaf
classification, and ranked build risks. Math validated S2-only (thread 27, Codex-survived); this is
the formaliser handoff. Date 2026-06-24, seat `pen-and-paper`. Thread `28-hfin-recStep-spec/spec.md`.

## The 3 families (build order)
1. **L1.1 `radial_morse_dominates_lt_top`** (S2-FREE, LOW risk) — the glue/terminal: `∫_{B_P×B_z}
   (‖P‖²+W)^{−c'} ≤ Kbound(n,c')·vol(B_z) < ⊤` for `c' < n/2`, `W ≥ 0`. Generalises `sumSq4_box_lt_top`
   to `Fin n` + `W≥0` domination + Tonelli; rides `radial_ball_iff`. Build FIRST.
2. **L2.1 `radialDelta_abs_det`** (LOW-MED) — `|det| = |a|^{r²−1}` for the radial `Δ=a·R` blow-up
   (the `phi334_abs_det` generalised; verified r=2,3). Reuse `pivotBlowupOnDeriv` det.
3. **L2.2 `schur_rank_stratum`** (MED) — `‖R·S‖² ≃ unit·‖P‖² + ‖B·Q‖²` (Morse block ⊕ strictly-lower
   corank core) on `{rank R = j}`; the matrix-algebra heart, `ring`-provable per the `(3,3,4)`
   `loss_schur_blowup_factor` pattern.
4. **L3.2 recursion carrier** (corank WellFounded) — `recStep` + the `chainRel_wf` pattern on corank.
5. **L3.1 `routeMCore_threshold_lt_top`** (HIGH, the assembly) — `c' < ½·minAdm ⟹ ∫_{routeMBaseNbhd}
   |routeMCore|^{−c'} < ⊤`, the general-M analog of `myF222_threshold_lt_top'`. Discharges `hfin`.
6. wire `hfin := routeMCore_threshold_lt_top` into `routeMLayerCover_of_atoms`; with the closed
   `cover_ge_div` (the `φ_M` lower atom) this closes the full `IsRouteMCover` → `resolution_charts` →
   headline, S2-only.

## Axiom hygiene
The hfin cover adds ZERO new axioms. Leaves: Morse (S2-FREE `radial_ball_iff`), a-divisor 1-D
(`abs_rpow_lintegral_Icc_lt_top`, elementary), Tonelli/dets/Schur (S2-free). S2 (`monomial_rlct`) only
in the leaf-sum MODEL side (the same use the headline already rides). `#print axioms` stays
`[propext, Classical.choice, Quot.sound, monomial_rlct]`.

## Build risks (ranked)
HIGH: the `r²`-chart Δ-blow-up cover up to null at general `r` (mitigate: ship `(4,4,2,2)`/`RouteM4422`
corank-2 instance FIRST, then lift). MED: the Schur LU normal form (mitigate: explicit `ring` identity,
not abstract LU); the WellFounded corank recursion + reduced-core reindex (reuse `ReducedTransport` +
`ParamsReshapeMP`). LOW: generalising `sumSq4_box_lt_top` to `Fin n`.

## Grounding (verified real signatures)
`recStep` (Case222Block:56, general-N), `radial_ball_iff` (S1SmoothBlock:78), `sumSq4_box_lt_top` /
`abs_rpow_lintegral_Icc_lt_top` / `argmaxCellOn_cover` / `coordZero_null` (all exist, checked),
`NodeAchieverChart`/`RouteM4422` (the per-cell top chart), S2 `monomial_rlct` (Skeleton:120).

## What is validated vs the build
Validated S2-only (thread 27, exact + Codex-survived): the resolution terminates monomial(S2)/Morse
(S2-free), depth ≤ corank, `λ_{r,p}=½·minAdm` (10/10). This spec: the Lean targets + order + risks; NOT
built. Honest residual: the depth-`r` cover assembly is the remaining R1 effort — large but BOUNDED,
`(2,2,2)` depth-2 as the worked template, `(4,4,2,2)` as the first L≥3 instance.

**Artefacts:** `spec.md` (full); builds on thread 27 (`Vzero-termination-cert.md`) + thread 26 (`φ_M`).
