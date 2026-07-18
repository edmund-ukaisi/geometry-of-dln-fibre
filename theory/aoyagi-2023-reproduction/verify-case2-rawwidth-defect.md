# Verified transcription defect: the Case-2 head-reset label uses the RAW width (p.20)

**Status: VERIFIED DEFECT (2026-07-18) — same class as the Def-3 typo; corrected form adopted
in the Lean engine; never transcribe p.20's label rule as printed.**

## The defect
Page 20 (Case 2) sets the new divisor's T-label head components as `t^(i) := M^(i+1)` — the RAW
width — while the SAME step's exponent is `(M(S) − J)(M^(S+1) − J)` with `M(S)` the RUNNING-MIN
corank. At non-monotone widths (an interior width increase, so `M^(i+1) > M(i+1)`), the label and
the exponent disagree with the paper's own p.22 formula:

- Instance `M = (2,2,3,2)` (minimal non-monotone, L = 3): the construction reaches a t̃=0 leaf
  divisor labelled `(2,3,0)` with ACCUMULATED exponent 4 — but `Mval(2,3,0) = 6 ≠ 4`, and
  `(2,3,0) ∉ Adm` (weak-decrease fails, 2 < 3). The stratum is the admissible `(2,2,0)`
  (with `Mval(2,2,0) = 4` = the accumulated exponent, correct) MIS-LABELLED.
- Root cause: the label writes the raw `M^(i+1)` where the running-min `M(i+1) =
  min(M^1..M^(i+1))` is meant — the exponent side already uses the running-min.

Evidence: exact-recursion battery `expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/
nonmono-2232-sim.py` (validated on (2,2,2)/(3,3,4)/(2,2,2,2) before the non-monotone run) +
an independent Codex replay agreeing to the number, which independently flagged the same
6-vs-4 conflict. Cert: `threads/08-atlas-probe/cert-nonmono-2232.md`.

## The corrected form (FIX-A, adopted)
Cap the Case-2 head-reset at the running-min: `t^(i) := M(i+1) = min(M^1..M^(i+1))`.
Battery-confirmed: this relabels `(2,3,0) → (2,2,0)`; the (2,2,3,2) t̃=0 atlas becomes exactly
the admissible profile set; label == exponent everywhere; leaf minimum == minAdm.

## Companion fact (independent of the fix)
Leaves CARRY t̃>0 divisors (e.g. `(1,1,1)`, `(2,1,1)`) whose exponents can be `< minAdm` — the
paper's read-off (p.22) restricts the min to `t̃ = 0` divisors. Any Lean predicate quantifying
over ALL leaf divisors (an unrestricted `∀ k`) is STRONGER than the paper and FALSE; the
read-off/exponent-hooks must filter `t̃ = 0`.

## Scope
Invisible at monotone widths and at every L ≤ 2 instance (the running-min = the raw width there);
bites exactly where the depth-≥3 + non-monotone structure lives. Found by the fork-12(b) gate
(elder-gate4) + the pnp-atlas exact recursion at the minimal instance.
