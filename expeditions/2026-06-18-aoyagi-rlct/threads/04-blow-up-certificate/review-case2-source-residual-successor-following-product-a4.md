# Review - A4 Case 2 source residual successor following product

Status: reviewed and formalised.

Reviewer: xhigh `Sagan`.

## Verdict

Pass.  The bare adapter is useful and not already present.

## Scope Check

The theorem combines the earlier source-residual/source-following product with
the successor-following restriction equality.  It supplies the source-pair
notation

```text
source residual block * source following factor of Csucc
```

for the lower rows of `D''' * C'`.

## Boundary Check

The result is formula-level only.  It does not prove source/chart production of
the residual representative or `Csucc`, a weighted source-chart handoff, a
pivot-row product, old-top rows, suffix product, full successor `C'^(S+1)`,
next-center nonemptiness, chart coverage, arbitrary-pivot coverage, transition
invariance, Jacobian arithmetic, normal crossings, pole order, termination,
RLCT, or repair of the printed Case 2 vector mismatch.

## Checks

- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` passed.
- `cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic` passed.
- `cd lean && lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- `cd lean && scripts/sorries` reported
  `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.

No quiver/Lehalleur-Rimanyi source was used.
