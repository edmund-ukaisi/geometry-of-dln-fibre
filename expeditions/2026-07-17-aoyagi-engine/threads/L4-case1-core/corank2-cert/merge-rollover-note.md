# Uniform-N1 collapse across MERGE + ROLLOVER → terminal — CONFIRMED

**Elder's final design residual (closed).** The blueprint collapses the old four-case split
(case11 merge / case12 / case2 / rollover) to ONE uniform per-step ideal-identity, with the
case-distinctions living in the FOLD, not the ideal-identity. My `(3,3,4)` `t=(1,0)` certificate
covered a fresh/coupled step; this closes the merge + rollover legs. Script:
`cert_merge_rollover.py` (re-runnable, exit 0, Gröbner-verified).

## The two ideal-level primitives (all steps are subsets of these)
Pinned from the code's step dispatch (`EngineDefs.lean:183-219`):
- **(P1) factor-exceptional-coordinate** — `block∘blowup = u·(strict transform)`, order one per blow-up.
- **(P2) unipotent Schur-clear** — pivot ≡ 1, `Q1·A·Q2 = diag(1, Δ)`, `Q1,Q2` unipotent-**polynomial**.

## What each case IS (verified)
| case | code effect (EngineDefs) | ideal-level operation |
|------|--------------------------|------------------------|
| case2 / case12 | new pivot, `cleared+1` | (P1) then (P2) on a **fresh** pivot |
| **case11 (MERGE)** | `divExp[mergeIdx] += runLen·resCols`; `numDiv`/`cleared` **unchanged** | (P1) on a **shared/existing** `u` (+ (P2)); exponent accumulates onto that divisor |
| **rollover** | `localSub = id`; ledger carries over; `J:=0`, `S` advances | the **identity map** — `⟨A⟩=⟨A⟩`, cofactor `I` |

## Verified (exact, Gröbner)
- **[MERGE, PART A]** The case-1(1) trigger is "d-block = `E`·d'" with `E` an **existing** divisor.
  Factoring the **shared** `E` is EXACT (`E¹ |` block, `E² ∤` pivot — order one *at this blow-up*),
  the strict transform is polynomial, and (P2) is the **identical** unipotent-polynomial Schur-clear as
  the fresh step. Forward cofactors polynomial (`Dmerge = E·(Q1⁻¹·Dclear·Q2⁻¹)`); `⟨Dmerge⟩ = ⟨E⟩` as
  an exact Gröbner ideal-equality. **No special merge object.** The `+= runLen·resCols` is the
  `jac`/`divExp` LEDGER bookkeeping (L8, route-independent), NOT a new ideal-identity.
- **[ROLLOVER, PART B]** `localSub = id` ⇒ the coordinate map is the identity, so `⟨A∘g⟩ = ⟨A⟩` with
  cofactor `I` (Gröbner-confirmed). Rollover needs **no** ideal-identity lemma at all — the strongest
  possible uniformity.
- **[TERMINAL, PART C]** The fold composes (P1)/(P2)/id across fresh + merge + rollover; the terminal
  `⟨diag b⟩ = ⟨b₁⟩` (principal via the divisibility chain, `unit(0)=1`) and its value read-off are the
  SAME as the fresh branch (L8, route-independent).

## Why the collapse holds (the load-bearing reason)
The fold's oracle (`IsEligibleMinimalChoice`, the `runLen`/`mergeIdx` selection) **guards** applicability:
case11 fires only when the block IS divisible by an existing `u` (the merge precondition); otherwise the
oracle picks case12/case2 (fresh). So the single N1 lemma is applied only where its divisibility
precondition holds, and that precondition-check is the **fold's** job. Hence: **N1 stays uniform; the
case labels are FOLD decisions (which divisor the exponent lands on, whether a fresh pivot clears,
whether `S` or `J` advances) — none change the ideal-identity primitive. No thin merge guard is needed
at the ideal level.**

## Honest scope
Verified the merge **geometry** (re-factoring a shared exceptional coordinate) + the code's step-dispatch
structure (case11 = exponent bump, no `numDiv`/`cleared` change; rollover = `localSub = id`), NOT a full
`buildTree` drive of a specific width that fires case11. The uniformity conclusion rests on: (i) the
dispatch structure (asserted from `EngineDefs.lean`), and (ii) the exact-algebra that re-factoring a
shared `u` is the uniform (P1) with polynomial cofactors. The Lean prototype (`proto-corank2`) is the
place a full width-drive gets exercised end-to-end; this note tells it the merge/rollover need no extra
ideal-identity beyond the fresh-step N1.
