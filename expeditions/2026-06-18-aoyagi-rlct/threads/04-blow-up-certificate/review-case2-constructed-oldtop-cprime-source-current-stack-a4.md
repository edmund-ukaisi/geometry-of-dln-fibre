# Review - Case 2 constructed old-top `Cprime` source-current stack

Date: 2026-06-24.

Reviewer: xhigh subagent Gibbs the 2nd.

## Verdict

Sound, with statement-shape caveats.  No mathematical blocker.

The specialization is valid: instantiate
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily`
with

```text
C = case2DisplayedConstructedSourceFollowingFactorWithOldTopFromCprime
      ... residual Cold Cprime
```

and rewrite the two source-row submatrices using the constructed current and
successor row-block lemmas.

## Boundary Corrections

- The current lower block is not `[Cold; Cprime]`; it is
  `[Cold; case2DisplayedPaperConstructedFollowingFactor ... Cprime]`, i.e.
  the displayed pivot-first old residual block `Q*Cprime`.
- The successor lower block is `[Cold; Cprime]`, using the whole recovery
  theorem `paperCprime(C)=Cprime`.
- The row-operation witness `q` should remain existential after specializing
  to the supplied `Cold` and `Cprime`.
- The theorem should say the suffix matrices are supplied inputs, not
  produced.

These corrections have been incorporated into the reproduction and Lean target
shape.

## Nonclaims

The target remains a finite stack specialization.  It does not construct
source production, suffix production, a chart family, coverage, transition
regularity, analytic data, normal crossings, pole order, or RLCT extraction.
