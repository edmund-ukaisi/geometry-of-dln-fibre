# Review - A4 Case 2 source-production obligation row-exhausted Csucc

Status: reviewed and formalised.

Reviewers: xhigh `Herschel`; post-implementation xhigh `Gibbs`.

## Verdict

Pass as a supplied-obligation projection.

## Scope Check

The theorem consumes an existing `SourceProductionObligation`; it does not
construct one from the displayed chart boundary.  It combines:

- the obligation's `rowExhausted_Cterm_eq` field;
- the existing row identity
  `case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor`;
- the obligation's supplied formula equality `Csucc_eq_formula`.

The result is row-exhausted terminal-row notation in terms of the supplied
successor factor `Csucc`.

## Boundary Check

Row `J+1` is original only as a row of `Csucc`; it is not identified with the
old source row of `C`.  The theorem does not derive the row-exhausted branch,
make stopped branches exclusive, produce `Csucc`, produce a suffix, construct
charts, prove coverage or transition regularity, derive post-data from
coordinates, compute Jacobians, prove normal crossings, pole order,
termination, RLCT, or repair the printed Case 2 vector mismatch.

## Checks

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit`, `0 native_decide`, and `0 axiom`.
- `git diff --check` passed.
