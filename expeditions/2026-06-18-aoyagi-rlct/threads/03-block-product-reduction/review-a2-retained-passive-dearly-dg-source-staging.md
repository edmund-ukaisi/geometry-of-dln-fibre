# Review - A2 retained-passive dEarly dG source staging

Date: 2026-06-27.

Reviewers: xhigh `Halley` and xhigh `Nietzsche`.

Verdict: PASS.

## Scope

Reviewed the proposed `dG_p` source-staging theorem pair in

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

against the reproduction and statement card:

```text
reproduction-a2-retained-passive-dearly-dg-source-staging.md
statement-card-a2-retained-passive-dearly-dg-source-staging.md
```

## Findings

No blocking issue.

The theorem
`fderiv_retainedPassiveA3WithoutLast_castSucc_apply` proves that for
`q : Fin M`, the derivative of the zeroed retained-passive lower-left family
at `q.castSucc` is the passive source tangent `v.2.2.1 q`.

The theorem
`fderiv_retainedPassiveA3WithoutLast_last_apply` proves that the derivative at
`Fin.last M` is zero.  This terminal case is the zeroed retained-passive
branch, not the solved terminal lower-left block.

The proof route is the expected one: simplify the nonterminal branch to the
raw tuple projection `y.2.2.1 q`, and simplify the terminal branch to a
constant-zero map.  The focused build of
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` passed before this
review record was written.

## Post-review verification

After the review, `scripts/sorries` reported zero `sorry`, `#exit`,
`native_decide`, and `axiom`; `git diff --check` was clean; the full
`DLNFibre` build succeeded; and the theorem axiom audit reported only the
standard `[propext, Classical.choice, Quot.sound]` footprint for both new
theorems.
