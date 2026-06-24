# Review - A2 suffix-state step coordinate adapter

Reviewer: Dewey the 4th, xhigh-effort subagent.

## Verdict

Pass.  No blocking findings.

## Findings

The Lean adapter is source-faithful.  The raw coordinates take `A1`, `A2`,
`A3`, and `A4` from the transformed edge
`transformedEdge E p S`, not from the raw edge `E p`.  The prior product
theorem uses

```text
T = P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj),
```

and recovers the p. 13 prior product shape through the factorisation

```text
E p = [I -S.B; 0 I] * transformedEdge E p S.
```

The signs match the p. 13 coordinate change:

```text
F2 = -A1^(-1) A2,
F3 = F3prev - D A3 (Ctop A1)^(-1).
```

The next suffix-state field has `B = A1^(-1) A2`, so the right multiplier
uses `F2 = -B`.  The product-difference block keeps the lower-right correction
`D*C - F3*F2`.  No inverse of `D` is introduced.

The determinant hypotheses are limited to the previous `S.Ctop` determinant
and the transformed-edge top-left determinant.  The residual block remains the
transformed Schur residual, not a product of raw lower-right edge blocks.

## Verification

The controller ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```

The reviewer ran `git diff --check` and checked Aoyagi PDF pp. 12-13 through
local text extraction.

## Residual Risk

The reviewer did not run Lean because read-only instructions ruled out
build-cache writes.  The controller build covers Lean elaboration.
