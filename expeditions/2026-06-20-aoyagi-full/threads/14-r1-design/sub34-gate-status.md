# cobuild-sub34 gate status — #44c (L2 deepest gauge-chart instance)

Snapshot of what is built vs. gated, for in-repo visibility (not just teammate messages).
Branch: `fm2/deepest-gauge-chart-sub34` @ `0b56ea3`. As of 2026-06-22.

## Built + GREEN (sorry-free; clean-three on the det-bound trio)

- `DeepestGaugeDiffeo.lean` — IFT det-bound bedrock (`clm_det_ne_zero`,
  `continuousAt_abs_fderiv_det`, `boundedUnit_fderiv_det`) + statement card.
- `DeepestGaugeBlocks.lean` — matrix bedrock + `coreShearHomeo` (coreAbsorb packaging, global
  shear det=1) + `regSliceHomeo` (regAbsorb packaging, local-diffeo lift). The two absorption
  STRUCTURES, abstract over the producer's concrete shift/Ψ.
- `DeepestGaugeConstruction.lean` — bundle + assembly matched to the 14-field `(e)`-structure.
- Squeeze math LOCKED + decorrelated: `core_comparability_squeeze` (#54) takes exactly 2 hypotheses
  (`P11=leak+Rcore`, `∑leak²≤t²∑E²`); pp2's cross-term Young-lock confirms no third
  (`codex/pp2-g161-confirm/`).

## The only remaining gate: THREE crux2 code-pushes (none yet on any branch)

Verified by `git grep` across all remote branches (2026-06-22): `fm2/split-reindex` is at @6560997
(#74); the items below are NOT pushed anywhere.

1. **#75 — the IFT→`#72` adapter.** Marked COMPLETED in the task tracker, but NOT in the codebase:
   - no `rlctAtOn_comp_localDiffeo` / `localDiffeo` theorem on any branch;
   - `#72` (`rlctAtOn_boundedUnit_localHomeomorph`) STILL carries the original `hmaps`/`hsymmmaps`
     (the bi-invariant-V requirement that g162 proved INFEASIBLE) — the g162 weakening is not done.
   So `regAbsorb_rlct` cannot be wired yet. (Flagged to team-lead; g162 gives the exact fix.)
2. **`deepestPoint_frame` exposure** — the per-layer CONSTANT frame `(P_s, Q_s)` from
   `block_elimination`/`deepestPoint_exists` (currently buried in `Classical.choice`). Needed for
   `gaugeDecode`'s frame + `regAbsorb`'s Ψ-domain (g164: the deepest point carries B's rank-factors
   `U,V`, so a frame IS required — option (a), frame in `gaugeDecode`, `split` stays MP).
3. **`RegGaugeIdx` per-layer slot-read** — read `(X_s,Y_s,Z_s)` from a `DeepestSplit` point's
   reg+spectator slots (the core `T_s` read is already type-forced = `FlatIdx deepestM`).

## Assembly plan (drops in once 1+2+3 land)

`gaugeDecode = roleRead(3) ∘ frame(2) ∘ (split.symm − deepestFlat)` (continuity+basepoint free) →
concrete `coreAbsorb` (`coreShearHomeo` + Schur shift) + `regAbsorb` (`regSliceHomeo` + Ψ=E∘frame) →
`coreAbsorb_rlct` (via #71, global shear det=1) + `regAbsorb_rlct` (via #75 adapter) →
`loss_squeeze` (via `core_comparability_squeeze` #54 + `frobenius_fromBlocks`) → the instance
`deepest_gauge_construction` (the sole remaining sorry). No open math.
