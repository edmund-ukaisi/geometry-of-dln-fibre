# Degenerate-boundary lemma DESIGN cert — `some M_s=0 ⟹ rlctAt(deepest) = nReg/2` (pp-hall, 2026-06-22, #70)

**The headline's non-strict boundary** (paper-faithful `r ≤ min(u,d)`): the rungs (R1/L2/D1) prove the
**non-degenerate bulk** (all `M_s ≥ 1`, the decomposition domain); the headline case-splits, and this lemma
covers the **degenerate boundary** (some `M_s = 0`, i.e. `r = H_s` at a layer). The headline-fidelity audit
VERIFIED the value (`rlctAt(deepest) = nReg/2 = aoyagiLambda`); this cert designs the direct proof. **The
BUILD is gated on L2's smooth-block primitive; the DESIGN (here) runs now.** Reuses L2's Morse-Bott
smooth-block.

## The statement + the ⊤-trap (the mechanism the task names)
`(some M_s = 0) ⟹ rlctAt(deepest) = nReg/2 = r(H_0+H_L−r)/2 = aoyagiLambda` (`lambdaCore = 0` there,
the reduced core empty).

**Do NOT route through `rlctAtOn(dlnLoss M 0) 0`.** At the boundary the reduced core vanishes (`M_s=0`), so
`dlnLoss M 0 ≡ 0` and `rlctAtOn(0) = ⊤` (the team's `sSup` convention: `|0|^{−c}` integrable for all `c`).
The additive decomposition `rlctAt = nReg/2 + rlctAtOn(core)` would then give `nReg/2 + ⊤ = ⊤` — FALSE.
Instead compute `rlctAt(deepest)` **DIRECTLY**.

## The direct computation (the three design pieces)
At the degenerate deepest point (a rank-`r`-exact minimiser), the loss `‖∏C − B‖²` is a **rank-`nReg`
nondegenerate Morse-Bott quadratic + flat complement** ⟹ `rlctAt = nReg/2`. Three pieces:

**(i) Hessian rank = `nReg` EXACTLY** (verified `g198`/`g199`/`g200`/`g201`). The Gauss-Newton Hessian of
`‖∏C − B‖²` at a fibre point is `J^T J`, `J = d(∏C)` the differential of the multiplication map.
`rank(J^T J) = rank(J) = codim of the fibre {∏C = B} at that point`. At the degenerate boundary the rank-`r`
locus is the **whole reachable set** (the chain is rank-bottlenecked by the width-`H_s = r` layer), SMOOTH
of codim `nReg = r(H_0+H_L−r)`. So `J` has rank exactly `nReg` ⟹ Hessian rank `nReg`. The vanished core
(`M_s=0`) contributes NO extra degenerate normal directions — the bulk's singular core (what `M_s≥1` adds)
is EMPTY here, so the loss is pure Morse-Bott.

**(ii) The flat complement = the fibre tangent** (gauge `GL_r` orbits + the vanished core, the latter
vacuous at the boundary). Dimension `= ambient − nReg`. **Genuinely flat** (loss CONSTANT along it, not
merely Hessian-degenerate): verified `g199` — along the `GL_r` gauge orbit `C_s → λ·C_s` / `C_{s+1} →
C_{s+1}/λ` (product invariant), `loss ≡ 0` (the fibre). Morse-Bott valley.

**(iii) `rlctAt(rank-`nReg` Morse-Bott quadratic + flat) = nReg/2`** (the standard fact; reuse L2's
smooth-block primitive). A rank-`k` nondegenerate quadratic `∑_{i<k} x_i²` on `ℝ^n` (`n ≥ k`, rest flat)
has `rlctAt = k/2`: `(∑x_i²)^{−c}` integrable near `0` iff `2c < k` (`k`-dim radial), the flat dims free on
a bounded nbhd. So `rlctAt = nReg/2`.

## Validation (exact, the audit cases + adversarial)
| H | r | M | nReg | Hessian rank | flat | rlctAt | audit |
|---|---|---|---|---|---|---|---|
| (3,1,3) | 1 | (2,0,2) | 5 | **5** | 1 (gauge) | 5/2 | 5/2 ✓ |
| (1,1) | 1 | (0,0) | 1 | **1** | 0 | 1/2 | 1/2 ✓ |
| (2,1,2) | 1 | (1,0,1) | 3 | **3** | 1 | 3/2 | — |
| (2,2) | 2 | (0,0) | 4 | **4** | 0 | 2 | — |
| (3,1,1,3) | 1 | (2,0,0,2) | 5 | **5** | 2 (two gauge) | 5/2 | — (two interior `M_s=0`) |

All Hessian ranks `= nReg` (`g198`/`g199`/`g201`). The interior-`M_s=0` case ((2,1,2), and the two-interior
(3,1,1,3)) confirms the design is not a coincidence of the end-degenerate audit cases.

## Why no `rank ≠ nReg` trap (the green-≠-right guard, adversarial `g201`)
The worry: a degenerate config where the vanished core leaves MORE flat directions (rank `< nReg` ⟹ `rlct <
nReg/2`). Ruled out: **at the degenerate boundary the rank-`r`-exact locus is a SINGLE `GL`-orbit** (all
rank-`r` factorizations through the width-`r` bottleneck are gauge-equivalent), so the Hessian rank is
**orbit-constant `= nReg` at EVERY deepest** — no non-generic-point trap (contrast the bulk `M_s≥1`, which
has multiple strata and a genuine singular core). Tested: 1 vs 2+ interior `M_s=0`, end vs interior, `r=1,2`
— no config with rank `≠ nReg`. The `r=0` edge: `M_s = H_s`, `nReg=0`, degenerate only if some `H_s=0`
(vacuous empty layer), `rlct = 0 = nReg/2` trivially.

## What the formaliser builds (gated on L2)
`rlctAt_deepest_degenerate : (∃ s, M s = 0) → rlctAt (dlnLoss H B) (deepestPoint H r B) = nReg/2`. Via:
- the Gauss-Newton Hessian rank `= nReg` at the deepest (the multiplication map's differential rank = the
  smooth fibre codim; reuse `block_elimination` + the rank-`r`-locus-is-one-orbit fact);
- the Morse-Bott splitting (the loss `= ∑_{nReg} (nondeg quadratic) + flat`, the flat = fibre tangent,
  genuinely flat); reuse **L2's smooth-block primitive** (`schur_recursion_step`'s `nReg/2` regular block,
  the `∑E²` Morse part) — the degenerate boundary is the case where the smooth block is ALL of it (no
  reduced core). So `rlctAt = nReg/2` is L2's smooth-block at the empty-core limit.
- NOT the `rlctAtOn(dlnLoss M 0)` route (the ⊤-trap). The headline case-splits: bulk via the rungs,
  boundary via this lemma.

## Most likely thing to break this
The single-orbit claim (the no-non-generic-trap argument) for the rank-`r` locus at the boundary: it holds
because the width-`H_s=r` bottleneck forces every rank-`r` factorization to factor through the same
`r`-dim image (gauge-equivalent). If a config had TWO independent bottlenecks at different ranks the orbit
structure could differ — but `M_s=0` pins `r = H_s` at that layer, and any other `M_t=0` pins `r = H_t = H_s`
(same `r`), so all degenerate layers share the SAME bottleneck rank `r`; the locus stays a single orbit. The
build's load-bearing Lean fact is the Hessian/Gauss-Newton rank `= nReg`, which the Jacobian-of-multiplication
rank computation gives (reuse the codim-`nReg` fact from the rank-`r` normal form).

## Decorrelation
pp-hall exact algebra: `g198` (audit cases (3,1,3)/(1,1) Hessian rank = nReg), `g199` (deeper (2,1,2)/(2,2)
+ the genuine-flatness of the gauge orbit), `g200` (the dimension count + the Gauss-Newton rank argument),
`g201` (adversarial — no `rank ≠ nReg` config, the single-orbit guard). A decorrelated Codex consult was
fired but did NOT land (CLI flaky — the nested background launch produced no Codex output); the design rests
on the exact-algebra verification (decisive: Hessian rank = nReg on 6+ configs including adversarial) + the
single-orbit structural argument, NOT on the consult. A future decorrelated pass is optional (the argument
is elementary and self-checked). Builds on the headline-fidelity audit (the value verified), L2's
smooth-block primitive (the reuse target), `block_elimination` (the rank-`r` normal form), the
`r(H_0+H_L−r)` codim (the orbit-dim complement).
