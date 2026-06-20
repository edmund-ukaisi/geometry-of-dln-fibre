# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): foundations ENCODED + green + merged; spine de-risked general L

Phase shift: from "design" to "execute in Lean". The mathematical skeleton is essentially fully mapped.

**Encoded foundations (merged `a899db4`, green-gated):** `DLNFibre.DLN.RLCT.{Foundations/Loss,Rlct,
Lambda}.lean + Skeleton.lean`. `lake build DLNFibre` GREEN (2658 jobs). Audit: 9 named-sorry rungs
(S1×2, L1, L2, D1, R1, A1×2, A2) + 1 axiom `monomial_rlct` (S2). Defs axiom-clean.
- `aoyagiLambda` = `reg + ½·min over Adm of Mval` (TOTAL; ground truth enforced at build via #eval/#guard).
- `rlctAt` = Aoyagi Def 1 integral-sup (ℝ≥0∞). `Params` measure comes free (Pi instances; no flatten).
- **S2 narrowed (endorsed):** fm + a decorrelated Codex red-team reduced the cited axiom to the BARE
  weighted-monomial-integral threshold fact; cover/change-of-variables/bump-removal are now S1/R1
  PROVEN obligations, and the chart-formula is a DERIVED theorem (R1). Strictly cleaner one-citation line.
- `rlctOrderAt` = honest `opaque` placeholder (θ-seam; Mathlib lacks meromorphic continuation). The λ
  headline does NOT depend on it (λ faithfully grounded); θ is the seamed secondary.

**Spine (thread 03):** `codim S(t) = Mval(t)` PROVEN at general L (3 ways) ⇒ `λ_core = ½·min_strata codim`.
θ = a(ℓ−a)+1 (deepest-point divisor multiplicity; not argmin-count for L≥5). R1 obligation = value-match
via stratum codim; recommended R1 architecture = organize by nested-rank strata, not chart enumeration.

**D1 (thread 04):** light rung; cite Aoyagi 2013 **Thm 2**; depends on L2 (homogeneous core); reuses S1.

## Watched items

- **θ-seam:** `opaque rlctOrderAt` + the A2 statement — must stay an honest named seam, not an overclaim
  (rv auditing). λ is the headline and is grounded.
- **ofReal clamp:** headline RHS `ENNReal.ofReal(aoyagiLambda)` faithful iff `aoyagiLambda ≥ 0` (true:
  codim ≥ 0 + reg ≥ 0) — rv confirming.
- Topology: controller in worktree ⇒ serial editing teammates; pp read-only (parallel ok).

## In flight

- `rv` — Rung 0c fidelity+bedrock audit of the foundations (the gate). Background.
- `pp` — thread 05: S1 scope (RLCT change-of-variables/invariance linchpin). Read-only.
- `fm` — idle (0b done).

## Next tick

On `rv` PASS: the foundations are bedrock → start the Lean rungs. First the **(1,1,1) end-to-end
validation** (trivial: no blow-up, exercises defs + S2 + arithmetic) as the anti-treadmill gate, then
L1/L2 (product reduction → homogeneous core), with S1 (from pp's scope) as the shared analytic build.
On `rv` ISSUE: fix-loop on the foundations before building up (controller holds bedrock precedence).
On `pp` S1 report: scope/queue S1; then R1 (the mountain) with the stratification architecture.
