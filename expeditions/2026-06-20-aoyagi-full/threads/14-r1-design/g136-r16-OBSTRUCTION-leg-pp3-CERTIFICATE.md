# R1.6 — OBSTRUCTION leg (pp3, decorrelated): confound hunt + C1–C4 scoped conditions (#136)

**Task #17 — independent pen-and-paper OBSTRUCTION seat on R1.6.** Companion to the controller's
landed `g133` (ROUTE-HOLDS via a 9324-chain exact scan). This cert adds the **scoped-condition
checklist (C1–C4)** an implementation must respect, and the **two Codex witnesses** that refute the
over-clean "every divisor `k_E=1`, first-factor blow-up suffices" framing. Decorrelation honored: did
NOT read g129/g132 verdict certs; fresh exact algebra (16 scripts) + own Codex (gpt-5.5, adversarial,
hypothesis-withheld — CONVERGED on verdict, SHARPENED two points).

**Verdict: NO confound breaks the VALUE `rlct(core at 0) = ½·minAdm Mval`.** All three attacks fail to
produce a value-breaking counterexample. But the over-clean PROOF SKETCH is unsound; use C1–C4.

## Confound (i) — missed / spurious stratum
- **Spurious codim-1 center: HARMLESS.** `{rank C^(1) ≤ s}` is generically OFF `{prod=0}` (core a
  positive unit there → `k_E=0`, threshold-irrelevant). Codex witness `M=(2,2,1)`,
  `C^(1)=[[1,0],[0,0]]`, `C^(2)=(1,0)ᵀ`: `rank C^(1)=1`, product `≠0`. Atlas ratios = `{Mval(t)/2}`,
  min `=½·minAdm`, no undershoot.
  - **C1.** Read every exceptional `(k,h)` from the FULL pulled-back density `|core∘φ|^{-c}·|Jac φ|`
    on the strict transform of `{prod=0}` — NOT the raw first-factor codim. (Also covers the
    thin-product `(4,3,2)`: use the geometric codim `=Mval=12`, not the gen-Jac/Hessian rank 8.)
- **Missed later-factor stratum: REAL for a too-literal recursion.** Codex witness `M=(1,2,1)`,
  `C^(1)=(1,0)` FULL rank, yet `C^(1)C^(2)=0` (drop from the LATER factor); stratum `t=(1,0)`,
  `Mval=1`, `f=(x₁y₁+x₂y₂)²`, rlct `½`. A first-factor-rank-defect-ONLY recursion skips this and
  over-estimates.
  - **C2.** Include the FULL-RANK / pass-through Schur chart (descend on a full-rank first factor so a
    later-factor drop is still resolved).

## Confound (ii) — multiplicity-2 divisor: "always `k_E=1`" is FALSE (value holds anyway)
- The matrix-chain core's OWN single-rank-stratum blow-ups are all `k_E=1` (first factor all
  widths/depths, step-2 residual, terminal cone — `core∘φ = u²·(…)`). Composed nodes → SEPARATE `k=1`
  divisors (`u₁²u₂²…`), never one `u⁴`.
- **But `k_E=2` genuinely occurs at INTERSECTION blow-ups.** Codex witness `M=(1,1,1)`, `f=x²y²`, blow
  up origin (`x=u,y=uv`) → `u⁴v²`, `k_E=2`. Formula HOLDS: Jacobian discrepancy adds (`h=1`), ratio
  `2/4=½=minAdm/2`. The `(x²+y²)²` ratio-undershoot is NOT produced by the Schur-reduced chain core
  (residual stays a norm of a matrix product, never a pos-def quadratic squared).
  - **C3.** The lower bound CANNOT rest on `k_E=1` per divisor (false at NC/intersection blow-ups). Use
    the multiplicity-control inequality R1.2b (`axisRatio_ge_of_mult`, `m·k ≤ h+1`), robust to `k_E≥2`.

## Confound (iii) — non-termination / stuck descent: terminates, pinch needs a branch
- `ΣM` strictly drops: a Schur step on a rank-`s` first factor sends `(M¹,M²,M³,…)↦(s,M³,…)`,
  `ΣM−ΣM' = M¹+M²−s > 0`; depth `L` drops by 1; base `L=1` smooth block. No stuck chain (10+ shapes).
- **The width-1 / rank-pinch / `s=0` node SEPARATES** (`‖C^(1)C^(2)‖²=‖C^(1)‖²‖C^(2)‖²` for a rank-1
  bottleneck). `(3,1,3)`: blowing up `{C^(1)=0}` gives `u²·(Σd²)·unit` — residual is a FRESH smooth
  block, not a coupled chain core. Value still `minAdm/2`, mechanism is Fubini (the `(2,1,2)` case).
  - **C4.** BRANCH on layer structure: blow-up for coupled layers, Fubini product-min for separating
    (width-1/pinch/`s=0`) layers. A naive "always blow up first factor" STALLS at an empty Schur
    complement.

## Net
| Confound | Breaks value? | Surfaces |
|---|---|---|
| (i) spurious codim-1 | No (`k_E=0`) | C1 |
| (i) missed later-factor | No *if* C2 | C2 |
| (ii) `k_E≥2` | No (discrepancy compensates) | C3 (lower bound via R1.2b, not `k=1`) |
| (iii) pinch | No (`ΣM↓`) | C4 (Fubini branch) |

**Residual worry (construction, not no-go):** the G5 c-o-v-tree gluing must handle the HETEROGENEOUS
node types (coupled blow-up + Fubini pinch + full-rank pass-through) and carry NC-completion `k_E≥2`
divisors with discrepancies. An audit should confirm the branching logic is exhaustive over layer
structures, not just the all-coupled square case.

Decorrelation: pp3 exact algebra (16 scripts, `g136-scripts/`) + own Codex (CONVERGED + SHARPENED
(i)-missed `(1,2,1)` and (ii)-`k_E=2` `(1,1,1)`). Agrees with the landed g133 verdict; adds C1–C4 + the
two witnesses. Did NOT read g129/g132.
