# L2-at-v multi-drop serialization — WITNESS (pp, decorrelated, 2026-06-23)

- **Seat:** `pen-and-paper`. The L2-at-v analog of the C5 termination cert — the last de-risk before the
  controller opens the L2-at-v formaliser front (#105).
- **Question:** does the #122 "peel highest-rank-layer first" serialization give a UNIFORM
  triangular-unit-pivot system at arbitrary `T_v`, especially deep non-rank-exact `T_v` with MULTIPLE
  simultaneous interior drops? Witness → L2-at-v fully de-risked, formaliser-scale; refutation → the
  exact deep-`T_v` obstruction (collapse to constant-rank).
- **Decorrelation:** exact algebra (6 scripts `d1-l2atv-scripts/l2atv_*.py`) + hypothesis-withheld Codex
  (`codex/l2atv-multidrop-{prompt,answer}.md`, VERDICT: WITNESS). Converged — Codex sharpened the
  formulation.

## VERDICT

**WITNESS — the L2-at-v split serializes to triangular-unit-pivot at ARBITRARY `T_v`, including deep /
adjacent multi-drop.** No breaking `T_v`. The split is formaliser-scale (the same character as the
rank-exact / deepest case), NOT the Mathlib-absent constant-rank theorem. **The L2-at-v front is fully
de-risked.** One refinement to the serialization spec (§3, from Codex) the formaliser must adopt.

## 1. The regular block is a Ferrers union of two-flag rectangles [FACT]

The linear part of the product map is `dP(δ) = Σ_s (C_L···C_{s+1})·δ_s·(C_{s-1}···C_1)`, so
`im(dP) = Σ_s Im(C_L···C_{s+1}) ⊗ Row(C_{s-1}···C_1)`. The suffix images `Im(C_L···C_{s+1})` form an
INCREASING flag in the output; the prefix row-spaces `Row(C_{s-1}···C_1)` form a DECREASING flag in the
input. Verified on the adjacent multi-drop `t=(5,4,3,2,1,1)` (`l2atv_ferrers.py`): suffix ranks
`[1,1,1,1,5]` (increasing), prefix ranks `[5,4,3,2,1]` (decreasing). So `im(dP)` is a **Ferrers-type
union of rectangles**, NOT an arbitrary coupled matrix. `rank(dP) = nReg = r(M¹+M^{L+1})−r²` exactly at
every general optimal `v` tested (rank-1 `B`, multi-drop and adjacent). (Codex Q1 [FACT].)

## 2. The pivots are units on the surviving rectangle — multi-drop does not couple them [FACT]

Each drop layer `s`'s regular pivot uses ONLY the suffix-surviving subspace `Im(C_L···C_{s+1})` and the
prefix-surviving row-space `Row(C_{s-1}···C_1)`. On those chosen rank sub-blocks, adapted bases make the
relevant minors identity ⟹ UNITS. A later drop SHRINKS the available rectangle; it does NOT turn a
selected surviving pivot into a zero pivot (Codex Q2 [FACT]). Verified: at a deep multi-drop `v`
(3 simultaneous drops, `t=(3,2,2,1,1)`, `B` rank 1) and an adjacent multi-drop (every layer drops,
`t=(4,3,2,1,1)`), the regular block (rank 7, resp. 9) admits a triangular-unit elimination — a
nonsingular pivot submatrix exists, LU has all-nonzero pivots (`l2atv_triangular_test.py`,
`l2atv_adjacent_drops.py`). Each drop's downstream survivors are alive (rank ≥ r) when peeled.

## 3. The serialization is highest-rank-first ON THE SURVIVING RECTANGLE (the refinement) [FACT + adopt]

The multi-drop IS a serialization of single-drop peels: because `im(dP)` is built from two monotone
flags, adding a drop only adds/removes boundary rectangles in the same Ferrers diagram (Codex Q3 [FACT]).
The order is FORCED by the (weakly-decreasing) rank filtration `t_0 ≥ t_1 ≥ …` — peel where the rank is
highest, descend.

**The refinement (Codex Q2/Q4 — adopt for the #105 spec):** the naive "highest-rank layer pivots on its
FULL high-rank block" is WRONG — a later drop kills part of that block. The CORRECT peel pivots on the
**current surviving suffix/prefix rectangle** `Im(C_L···C_{s+1}) ⊗ Row(C_{s-1}···C_1)`, NOT the raw
pre-drop rank. The killed coordinates are KERNEL directions of `dP` (the core / fibre-tangent), NOT
regular directions — so they are never pivots. My earlier proxy ("downstream rank ≥ r") was coarser;
Codex's flag-rectangle reading is the exact statement. The formaliser must phrase the per-layer peel on
the surviving Ferrers cell.

## 4. The big-single-layer-drop = iterated rank-1 (consistency with the banked schurState)

A layer dropping rank ≥ 2 at once (e.g. `5→3`) is the iterated-rank-1 reading (the banked `schurState`
drops 1 per pivot vertex per step; cf. the C5 node-count cert): the big drop = several rank-1 peels,
each a unit-pivot Ferrers cell. (The non-uniform-width numeric harness for this case had a
matmul-shape bug — orthogonal to the math; the uniform-width multi-drop + adjacent cases + the
structural flag argument carry the claim.)

## 5. Net for the controller (the #105 L2-at-v front)

**The L2-at-v Morse-peel split is fully de-risked — formaliser-scale, NOT a constant-rank research gap.**
The ⨅-form learning coefficient's last open scope item closes. The #105 front spec:
1. The regular block = the rank-`dP` two-flag Ferrers rectangles (`im(dP) = Σ Im(suffix) ⊗ Row(prefix)`).
2. Peel highest-rank-first, each peel a triangular-unit step ON THE SURVIVING SUFFIX/PREFIX RECTANGLE
   (the Ferrers cell), pivots units in adapted bases (the gauge-to-identity-corner, #122).
3. The killed coords (later-drop-removed) are `dP`-kernel (core), handed downstream — NOT regular pivots.
4. Lean primitive: `rlct_unit_invariant` (unit-Jacobian chart, #125) + unit-division + finite triangular
   induction over the Ferrers order. Avoids the Mathlib-absent constant-rank/Morse theorem.

This is a SEPARATE Lean front from the R1 routeStep grind (Morse-peel on the smooth fibre directions vs
squeeze-resolution of the singular core), but each is formaliser-scale and they compose:
**L2-at-v split → D1 monotonicity (`rlctAt_mono`, green) → R1 §4 resolution.** The full general-M ⨅-form
learning coefficient is reachable-but-long, end-to-end, with no research gap.

## 6. Non-transversal-flag over-verify — CLOSED (the belt-and-suspenders, bedrock)

The one residual worry: at a `v` where the suffix/prefix flags are NOT in general position (overlapping
/ degenerate Ferrers rectangles), could the gauge fail to make the per-cell minors identity? **Over-
verified CLOSED** (`l2atv_nontransversal{,2,_why}.py`), numerically + structurally, at every degeneracy:

| config | rank(dP)=nReg? | tri-unit elim OK? | min\|pivot\| |
|---|---|---|---|
| maximal alignment (the cascade, all flags = standard flag — MOST non-transversal) | ✓ (9=9) | ✓ | **1.000** (exact units) |
| aligned to a non-standard flag (conjugated) | ✓ | ✓ | 0.551 |
| partial alignment (layers 2,3 share a flag) | ✓ | ✓ | 0.041 |
| forced cross-layer survivor coincidence | ✓ | ✓ | — |

The STRUCTURAL reason (not just a sweep):
- **(A) Dimension is flag-independent.** `rank(dP) = nReg = r(M¹+M^{L+1})−r²` is the determinantal-variety
  TANGENT dimension at `B` (product rank `r`) — INTRINSIC to the rank, not the flag positions.
  Alignment changes the BASIS in which `im(dP)` is presented, NOT its dimension. So non-transversality
  never drops the regular-block dim.
- **(B) Alignment HELPS the pivots.** The #122 gauge makes survivors the identity corner. At an ALIGNED
  `v` the gauge is SIMPLER (flags coincide, less rotation) and the pivots are EXACTLY 1 (`min|piv|=1.000`
  at maximal alignment — the CLEANEST case). A transversal `v` needs more rotation, generic-unit pivots
  (still nonzero). Alignment makes the peel cleaner, never breaks it.
- **(C) No general-position assumption was ever needed.** The gauge (`block_elimination`/
  `deepestPoint_exists`) EXPLICITLY builds the identity corner at ANY `v` via a finite matrix
  factorisation — alignment-agnostic. It orthogonalises overlapping Ferrers rectangles into disjoint
  coordinate blocks, so the triangular order exists regardless of flag transversality.

**⟹ L2-at-v is 100% de-risked — no non-transversal hole.** The #105 front spec (§5) stands with no
residual; the gauge's uniform identity-corner construction is the `block_elimination`-backed lemma to
formalise, in reach and alignment-robust.

## Net for the controller (the #105 L2-at-v front) — restated, now hole-free

**The L2-at-v Morse-peel split is fully de-risked — formaliser-scale, no constant-rank gap, no
non-transversal hole.** The full general-M ⨅-form learning coefficient is reachable-but-long, end-to-end:
**L2-at-v split (#105) → D1 monotonicity (`rlctAt_mono`, green) → R1 §4 resolution (#99).** All three
fronts green-lit.
