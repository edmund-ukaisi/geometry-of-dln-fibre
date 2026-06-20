# Review - A4 Case 2 Printed Mismatch Boundary

Pre-Lean reviewers: xhigh source/math scout `Laplace the 3rd`; xhigh Lean/API
scout `Hilbert the 3rd`.

Post-Lean reviewers: xhigh Lean/API reviewer `Goodall the 3rd`; xhigh
source/docs reviewer `Carson the 3rd`.

Status: Lean-proved; pre-Lean and post-Lean reviews passed.

## Findings

No blocking pre-Lean findings.

The source/math scout recommended a formal mismatch-difference/equality
condition theorem rather than another corrected-transition boundary. The
reason is that the corrected Case 2 certificate packages already exist, while
the source-faithful layer still needed the exact condition under which the
PDF's printed vector is compatible with the PDF's printed prefix-minimum
increment.

The Lean/API scout recommended the equality-characterization theorem with the
zero-column-factor case included, plus a continuation-bound non-equality
corollary for the genuine Case 2 continuation branch.

The post-Lean reviewers found no blocking Lean/API or source-fidelity issues.
The Lean/API review requested that the non-equality theorem name expose the
continuation-bound hypothesis; the Lean name was updated to
`terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`.
The source/docs review confirmed that the checkpoint separates the printed
actual-width vector, prefix-minimum increment, and actual-width terminal
formula without claiming an erratum or transition theorem.

## Verdict

Pass. The checkpoint is a narrow arithmetic boundary theorem for the Case 2
printed-vector mismatch.

## Residual Risks

- This is arithmetic/source-gap isolation only.
- A future source convention or reachable-state invariant could force
  `prefixMinNat n S = n S` in every relevant Case 2 continuation branch; that
  would change the transition story, not this arithmetic boundary theorem.
- The corrected prefix-minimum certificate remains a repair layer, not a
  verbatim source vector.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, and `#exit`
