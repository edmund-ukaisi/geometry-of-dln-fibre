# R1.2 route adjudication — route B (L1-alone) REFUTED; route A-concrete is the path

- **Seat:** `pp`. **Read-only; /tmp scratch; no Lean.** Task #11. The route-before-lines gate for R1.
- **Verdict:** **route B (L1-alone, core = regular sequence of coordinates, k=1, NO blow-up) is FALSE.**
  A genuine blow-up is REQUIRED. pp exact-algebra + decorrelated Codex, independently identical, with
  witnesses. (/tmp/regseq_*.py, /tmp/codex-regseq-answer.md.)

## The decider (the general refutation)

For a residual product of length `q ≥ 2`, `‖∏_{s} C̃⁽ˢ⁾‖²` has **ordinary vanishing order `2q`**, not 2.
**Regular (invertible-analytic) coordinate changes + unit multiplication PRESERVE ordinary order.** L1
(= block-elimination = invertible row/col ops) provides only regular changes. So L1-alone can NEVER
turn a residual product into a smooth coordinate-square block `Σg_a²·unit` (order 2). ⟹ route B
cannot expose `‖∏C‖²` as `Σ(coordinate)²·unit`. **The product structure is a genuine obstruction.**

## Witnesses (both pp + Codex)

- **(1,1,1):** `F = c₁²c₂²` — ALREADY monomial normal-crossing in the original coords (no L1, no
  blow-up). The ONLY easy case. Even here the smooth-block route-B reading gives the WRONG value
  (`2/2=1`); the correct reading is `{c₁,c₂}` as normal-crossing (`rlct 1/2`). So route-B-as-smooth-
  block fails even at (1,1,1).
- **(1,2,1):** `F = (a₁b₁+a₂b₂)²` (Codex's smaller witness) — the singular quadratic cone, the FIRST
  genuine non-monomial singular case at L=2. `rlct = 1/2 = codim/2`, but NOT by a coordinate-square
  model.
- **(2,2,2):** `F = ‖AB‖²`, `ord₀(F) = 4` (all quartic ⟹ Hessian zero; a smooth `z₁²+z₂²+z₃²` block
  would have order 2, Hessian rank 3 — contradiction). `{AB=0}` is codim-3 IRREDUCIBLE (pp cert:
  Jacobian rank 0 at origin ⟹ singular; codim-3 confirmed numerically). `rlct = 3/2` via blow-up
  (`A=tA', B=tB'`: radial `c<2`, angular `c<3/2`, binding `3/2`). First square-matrix witness needing
  resolution.

## Where route B breaks (the boundary)

- `L=1`: route B TRUE (`F = ‖C‖²` is a sum of coordinate squares).
- `L=2 (1,1,1)`: smooth-block route-B fails, but monomial-NC ⟹ no blow-up.
- `L=2 (1,2,1)`: FIRST genuine singular witness (needs resolution-logic).
- `L=2 (2,2,2)`: first square-matrix witness; genuinely needs blow-up at the origin.
Route B "buys only the smooth pivot strata, not the singular residual core."

## Correction to the reconciliation (multiplicity-control is NOT vacuous)

The reconciliation "if (B) holds (regular seq, k=1) ⟹ multiplicity-control VACUOUS, R1 LIGHT" is moot:
(B) does NOT hold. There IS a blow-up; **multiplicity-control (`h_E+1 ≥ k_E·minMval`) is NOT vacuous**
— it's the per-divisor `k=1` on the EXCEPTIONAL divisors AFTER the blow-up (not in original coords).

## The path: ROUTE A-CONCRETE (explicit polynomial charts) — NOT the infra mountain

The blow-up is done with **explicit polynomial charts** (Codex's `A=tA', B=tB'`; my (2,1,2)
`(x,xy,z,zw)`, (2,2,2) pivot maps) — hand-written polynomial maps with vanishing Jacobian on the
exceptional locus, S1.1 carrying the change-of-variables. **NO Mathlib abstract-blow-up primitive
needed.** R1 is MEDIUM: explicit-poly-chart resolution + S1.1 + (non-vacuous) multiplicity-control +
cover. The dichotomy resolves: (B) L1-alone DEAD; (A)-abstract-infra unnecessary; (A)-CONCRETE is the
route — exactly what the validate-small handoff (1,1,1 φ=id; 2,1,2 (x,xy,z,zw)) already uses.

## Consequence for fm

- validate-small handoff STANDS ((1,1,1) is the special monomial-NC case; (2,1,2)/(2,2,2) are
  explicit-poly blow-up charts = route A-concrete).
- R1.2a/b arithmetic STANDS (axisRatio on exceptional-divisor exponents).
- fm must NOT pursue the (B) "core = regular sequence" general build — false from (1,2,1).
- multiplicity-control IS needed (non-vacuous), on the blow-up's exceptional divisors.

---

## GREENLIT: route-A-CONCRETE (controller, post-adjudication) + the S1.1 alignment

**Route:** explicit polynomial BLOW-UP charts (vanishing Jacobian on the exceptional locus) + S1.1 +
non-vacuous multiplicity-control (k=1 on the EXCEPTIONAL divisors via the pos-def-real initial form) +
the cover. NO abstract blow-up infra. R1 = climbable mountain, infra-light.

**Correction banked:** the earlier "L1-pivot charts resolve it" reading is WRONG (L1 = regular changes,
preserve ordinary order, can't reach order-2 from the order-2q product). It's explicit-poly BLOW-UP
charts (non-injective, Jacobian vanishes), NOT L1 regular changes. multiplicity-control NON-vacuous.

**KEY ARCHITECTURAL ALIGNMENT (load-bearing, satisfying):** S1.1's `hsurj` + `hImE` hypotheses are
PRECISELY FOR the blow-up. A blow-up chart is non-injective with Jacobian vanishing on the exceptional
locus — exactly what `hsurj` (surjective onto the neighbourhood) + `hImE` (exceptional image null)
cover. So S1.1 (`weightedThreshold_transport`, the 10th-finding hyps) carries the blow-up
change-of-variables with NO abstract infrastructure. The whole tower composes: S1.1's "awkward"
hypotheses were designed for exactly the blow-up R1 needs.

**R1.1 general design target:** the (2,2,2) witness (ord₀=4, Hessian zero, codim-3 irreducible,
rlct=3/2 via radial/angular blow-up `A=tA',B=tB'`: radial c<2, angular c<3/2, binding 3/2) is the key
general case. Validate-small (φ=id (1,1,1); explicit-poly (2,1,2)/(2,2,2)) + R1.2a/b STAND — those φ's
ARE the route-A-concrete charts. Then R1.3 codim + R1.6 cover (the geometric mountain, after the gate).
