# STEP-0 verify-first verdict (genm-d1asm) — BOUNDED

Canonical: `expedition/aoyagi-full` @ `aca74685` (branch `expedition/genm-d1asm` off it).
Date: 2026-06-30. Decorrelated Codex xhigh consult: `codex/step0-*`.

## Question

Is the L=2 D1 second-peel minor non-degeneracy `hminor₂` — and the general-v first-peel
`jacFlatL2` minor existence — dischargeable WITHOUT the constant-rank gauge-slice split
(BOUNDED), or secretly #44-hard (collapses onto the gauge-slice wall)?

## Verdict: **BOUNDED.** Proceed to build.

Decorrelated (Codex xhigh) + source-grounded + numeric-confirmed. The two minor-existence
facts are *rank-lower-bound + determinantal-engine* arguments, structurally identical to the
already-PROVEN first peel; neither touches `DeepestGaugeChart` / #44 / #120.

## Grounding (sorry-free in canonical)

- **First peel minor at GENERAL optimal v is ALREADY A THEOREM.** `exists_jacFlatL2_minor`
  (`D1HChartRank.lean:634`, file 0-sorries) gives injective `er, ec` with
  `det((jacFlatL2 H v).submatrix er ec) ≠ 0` at any `v` with `prod v = B`, `rank B = r`.
  Mechanism: rank bound `nReg ≤ rank(jacFlatL2)` (`nReg_le_jacFlatL2_rank` ← keystone
  `nReg_le_finrank_range_jointDiffL2`, both sorry-free) + the banked determinantal engine
  `exists_submatrix_det_ne_zero_of_le_rank`. The rank bound itself is a pure **gauge-fixed
  linear injection** `Ψ:(X,Y)↦X·V+U·Y` of `(ker ΛL)×Mat(r×H2)` into `range(jointDiffL2)`
  (`B=U·V` rank factorization), dim `r(H0−r)+r·H2 = nReg`. NO constant-rank geometry, NO
  inter-layer diffeo. So the map's open question "is `dln_hchart_residual`'s `hminor` at a
  general v dischargeable without new geometry?" is **answered YES — already proven**.

- **Second peel chart `secondPeel_hchart_residual` (`D1SecondPeelChart.lean:587`) is FULLY
  PROVEN, network-free, 0-sorries.** It takes `hminor₂` as a hypothesis: an invertible
  `extra × extra` minor of the Jacobian `D h(t0)` of the residual VECTOR `h = q(0,·)` (NOT a
  Hessian of the scalar `‖h‖²`). Its docstring explicitly separates this from the
  `DeepestGaugeChart` #120 wall (which feeds the SEPARATE deepest gate #44).

- **`hDeepest` (#44) and `hInterface` (R1) stay NAMED-OPEN gates**, untouched
  (`D1SecondPeelAssembly.lean:18`).

## The one genuinely-open piece + its decomposition (BOUNDED)

`hminor₂` is consumed as a hypothesis; there is NO second-peel rank lemma yet. To discharge it
as a theorem (the de-risk target), the decomposition is:

1. **Schur/quotient rank step:** `rank(D h(t0)) = rank(Dg(v)) − nReg` (after straightening the
   first-peel `nReg` block to coordinates, the residual `h` is the quotient differential).
2. **Middle-stratum first-order range bound:** `nReg + extraCount m a b ≤ rank(Dg(v))`, the
   SAME gauge-injection as the first peel but with the middle-stratum layer ranks `(r+a, r+b)`
   instead of the deepest `(r, r)`. The image of `(δA0,δA1)↦δA0·A1+A0·δA1` at v has dimension
   `(r+a)·H0 + (r+b)·H2 − (r+a)(r+b)`.
3. **Determinantal engine:** reuse `exists_submatrix_det_ne_zero_of_le_rank` to extract the
   `extra × extra` minor of `D h(t0)` (analog of `exists_minor_of_le_rank`).

### Numeric confirmation of the dimension arithmetic (load-bearing)

Square case `H0=H1=H2 = m+r` (deepest reduced width `m`, deepest rank `r`), middle-stratum
layer ranks `(r+a,r+b)`, `nReg = r(H0+H2−r)`, `extraCount = m(a+b)−ab`:

    (r+a)·H0 + (r+b)·H2 − (r+a)(r+b)  −  nReg  −  extraCount  =  0   (exact, sympy)

The identity closes to zero — the "remaining regular directions form a rank-`extraCount` block"
is a DIRECT quotient-rank consequence of the same first-order range calculation. Confirms
sub-question `(a)` (Codex): NOT dependent on the deepest normal form (#44 geometry).

## Consequence for the brief's build plan

- The de-risk (`hminor₂` + first-peel `hchart` minor-existence at general v) is BOUNDED and
  R1-INDEPENDENT. Build it.
- The first-peel `hchart` minor-existence is **already banked** (`exists_jacFlatL2_minor`); the
  build effort concentrates on the SECOND-peel rank bound (steps 1–3 above) and the L=2
  glue lemma threading the 4 named hyps, leaving `#44`/`hDeepest` (← #149/#153) and
  `hInterface` (← R1-LOWER `cover_ge_div`) as the two NAMED-OPEN gated hypotheses.
- KILL-CONDITION NOT triggered: `hminor₂` does NOT require the constant-rank split; D1≥ IS
  R1-independent (modulo the two tracked gates).
