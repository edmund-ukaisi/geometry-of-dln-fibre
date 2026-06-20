# Review - A4 Case 2 Stage-Relabel Domain Audit

## Reviewers

- Source/pen-and-paper reviewer: `Chandrasekhar the 4th`, xhigh.
- Lean/API scout: `Bohr the 4th`, xhigh.

## Findings

No source/math fidelity defect was found in the proposed finite-domain audit.
The source reviewer confirmed the key distinction: Lean's introduced labels
use actual layer width `n(S+1)`, while the Case 2 continuation condition uses
the prefix minimum `M(S+1)`.  Therefore the equality between old `(S,J+1)` and
`(S+1,0)` label domains is valid under the actual-width side condition
`n(S+1)=J+1`, not under the frontier equality alone.

The row-side obstruction is intentional and source-faithful as a Lean-domain
audit: if `J+2 <= n(S+1)`, then `(S,J+2)` is introduced at `(S+1,0)` but not
at `(S,J+1)`.  This should be read as a finite bookkeeping side condition,
not as a claim that Aoyagi's terminal transition is invalid.

The Lean/API scout found the target feasible using the existing
`introducedLabel`, `introducedLabelFinset`, `actualWidthLabel`, and
`prefixMinNat` APIs.  The implemented theorem names avoid claiming an
unconditional terminal advance.

Post-implementation review found no source/math fidelity defect and no
Lean/API defect.  The final wording was hardened from "behind Aoyagi's
terminal Case 2 advance" to "needed for auditing Aoyagi's terminal Case 2
advance" to reduce overclaim risk.

## Verification

- `git diff --check`
- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`

## Residual Risk

This checkpoint does not construct the `S+1` recurrence/exponent state, prove
the terminal `D'''` block shape, construct `C'^(S+1)`, prove chart coverage,
coordinate regularity, Jacobian arithmetic, normal crossings, RLCT extraction,
termination, transition invariance, or repair the printed Case 2 vector
mismatch.
