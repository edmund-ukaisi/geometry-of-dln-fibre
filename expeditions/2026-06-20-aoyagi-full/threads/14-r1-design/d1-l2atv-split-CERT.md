# D1 L2-at-v reg/core split — SEPARATE-BUT-REACHABLE (pp, decorrelated, 2026-06-23)

- **Seat:** `pen-and-paper`. The last gate for the FULL general-M ⨅-over-fibre learning coefficient
  (vs the deepest-point form). The D1 analog of the C5 probe. Independent of the R1 grind.
- **Question:** does the cascade+hnode machinery (which resolves the local chart at every rank pattern
  `T`) ALSO supply D1's L2-at-v reg/core split at a general optimal `v`, or is L2-at-v a SEPARATE step
  the hnode assumes done? If separate — reachable via the #122 unit-pivot revival, or a constant-rank
  research gap?
- **Decorrelation:** exact algebra (5 scripts `d1-l2atv-scripts/`) + hypothesis-withheld Codex
  (`codex/d1-l2atv-split-{prompt,answer}.md`, VERDICT: SEPARATE-BUT-REACHABLE). Converged.

## VERDICT

**SEPARATE-BUT-REACHABLE (unit-pivot, formaliser-scale).** L2-at-v is NOT the cascade/hnode machinery —
it is a logically UPSTREAM Morse/unit-pivot SPLIT that ISOLATES the homogeneous core the hnode then
resolves. But it is REACHABLE via the #122/#125 unit-pivot revival (gauge-to-identity-corner + triangular
unit-pivot elimination), NOT the Mathlib-absent constant-rank theorem. So the FULL general-M ⨅-form
closes by COMPOSING three separate-but-each-formaliser-scale pieces: **L2-at-v split (unit-pivot) → D1
monotonicity on the homogeneous core → R1 §4 cascade/hnode resolution.** The honest general target is the
full ⨅-form, NOT only the deepest-point form — with ONE open scope item (§5).

## 1. The split is logically UPSTREAM of the resolution [FACT]

The cascade tuples `C_s = diag(1^{t_{s+1}}, 0)` have product `= 0` (the CORE's deepest point, `t_L=0`;
verified `d1_split_vs_resolve.py`). So the cascade/hnode INPUT is the homogeneous core at its deepest
point — product `0`, NO linear part. The L2-at-v split is what PRODUCES that core: it takes the full
loss `F = ‖∏C − B‖²` at an optimal `v` and peels the `nReg` regular directions, leaving the homogeneous
core. The hnode's own form `Σreg² + Σ(b·E+SΓ)²` already CONTAINS a separated regular block — it CONSUMES
a split form, it does not PRODUCE the split from an unstructured loss. So the split is upstream; the
resolution is downstream. (Codex Q1/Q2 [FACT], concurs.)

## 2. They are DIFFERENT mechanisms at DIFFERENT stages [INFERENCE, strong]

- **L2-at-v split:** a MORSE/unit-pivot peel. CORRECTION to a loose framing: at the optimal `v`,
  `∏C = B` so `F = 0` is the MINIMUM ⟹ `∇F = 0` (a critical point). `F = ‖dP(δ)‖² + O(δ³)`, where
  `dP` is the linear part of the PRODUCT map (the "nonzero linear part" is `dP`, NOT `∇F`). The regular
  block = the Hessian rank = `rank(dP)`. Lean primitive: `rlct_unit_invariant` (unit-Jacobian chart,
  #125), peeling the Morse directions where the product map is a submersion.
- **R1 §4 hnode:** a two-sided SQUEEZE resolution of the SINGULAR core (`∇=0`, homogeneous). Lean
  primitive: `schur_node_squeeze_unif` — a different lemma, a different stage.

They COMPOSE: the L2-at-v split's residual core (after peeling `rank(dP)` regular dirs) is the
homogeneous core at rank pattern `T_v`, which IS the cascade/hnode's input for `T_v`
(`d1_unitpivot_vs_hnode.py`). Split feeds resolution.

## 3. The regular-block dimension is `rank(dP)`, set by `v`'s bottleneck [FACT, exact]

A subtle confound caught and resolved (`d1_rank_reconcile.py`, `d1_rank_gap.py`): at a FULL-width
optimal `v` (no rank bottleneck, e.g. widths 3, `B` rank 2), the product map is a SUBMERSION
(`rank(dP) = 9` = full), so `F` is MORSE — no singular core, learning coeff `9/2`. The singular core
appears only when a BOTTLENECK forces the product rank below the widths (the reduced-width core
`M = H − r`, where the deepest point forces rank `0`). At a bottleneck `v`, `rank(dP) = 8 = nReg =
r(M¹+M^{L+1})−r²` exactly (the rank-≤r determinantal tangent). So the regular-block dim
**depends on `v`'s rank pattern** — `rank(dP)` at `v` — and the core is the bottleneck-forced singular
directions. The L2-at-v split peels exactly `rank(dP)` Morse directions; their pivots are the up/down
product sub-blocks on the surviving ranks (units). (This corrects any reading of `nReg` as a fixed
constant independent of `v`.)

## 4. Reachable via the unit-pivot revival, NOT constant-rank [INFERENCE; #122/#125 prior verdict]

The #125 cert proved the deepest-point split is explicit triangular unit-pivot (identity corners ⟹
`g_i = u_i·z_i + h_i`, `u_i(0)=1`, solve by division-by-unit — NO constant-rank). The #122 cert
extended it to a general optimal `v` (add the gauge-to-identity-corner via `block_elimination`; the
multilinear chain ⟹ each pivot variable occurs linearly with a unit coefficient ⟹ no non-triangular
case). I re-verified the regular-block pivots are units at a general optimal `v` (`d1_general_v_fixed.py`,
the up/down products invertible on surviving ranks) and at a non-rank-exact interior pattern
`T_v=(3,3,2,2)` (`d1_nonrankexact.py`, `rank(dP)=14` well-defined, per-layer unit pivots). So L2-at-v
avoids the Mathlib-absent constant-rank/Morse theorem.

## 5. The ONE open scope item (Codex's flagged residual — honest)

Codex flagged, and I concur: the minimal obstruction would be **failure to exhibit a UNIFORM triangular
unit-pivot system for ALL fibre points, especially non-rank-exact internal patterns** — if that fails,
the proof collapses back to constant-rank. The #122 argument (multilinearity ⟹ per-rank-drop-layer unit
pivots, peel highest-rank-layer first) covers it structurally, and I verified it does not break at an
interior-drop `T_v`; but the UNIFORM cert (one triangular pivot order valid for every `T_v`) is the
load-bearing lemma to prove. This is **the exact analog of the C5 hnode's per-node chart** — same
character, formaliser-scale, NOT open math. It is the L2-at-v analog of R1's `routeStep` grind.

## 6. Net for the controller (the ⨅-form decision)

**The FULL general-M ⨅-over-fibre learning coefficient closes** — formaliser-long, not a research gap —
by composing:
1. **L2-at-v split** (unit-pivot revival, #122/#125; the open item is the uniform triangular cert §5),
2. **D1 monotonicity** on the homogeneous core (`rlctAt_mono` green; the deepest ≤ every optimal point),
3. **R1 §4** cascade/hnode resolution of the deepest core (the de-risked `routeStep` grind).

It does NOT collapse to the deepest-point-only form. The general-v D1≥ / fibre-inf is reachable. The
caveat to carry: L2-at-v is a SEPARATE Lean front from the R1 grind (different mechanism: Morse-peel vs
squeeze-resolution), so it is its own scoped task, not a byproduct of `routeStep`.

## Most likely thing to break this

The uniform triangular unit-pivot cert (§5) at deep non-rank-exact `T_v` with MULTIPLE simultaneous
interior drops — the L2-at-v analog of the C5 multi-drop. The #122 "peel highest-rank-layer first"
ordering should serialize it (the same way C5 multi-drop serializes into single-layer steps, g138), but
that serialization for the L2-at-v Morse peel is not separately verified. The next decorrelated step
that would fully close it: an exact-algebra cert that the gauge + rank-filtration pivot order is
triangular-unit for an arbitrary `T_v` (the L2-at-v analog of the C5 cert) — formaliser-scale to verify,
the one thing standing between "⨅-form reachable-but-long" and "⨅-form fully de-risked."
