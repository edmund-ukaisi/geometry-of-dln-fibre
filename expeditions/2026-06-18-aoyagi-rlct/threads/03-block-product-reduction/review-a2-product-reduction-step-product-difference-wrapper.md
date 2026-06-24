# Review - A2 product-reduction step product-difference wrapper

Reviewer: Meitner the 4th, xhigh-effort subagent.

## Verdict

Pass.  No blocking findings.

## Findings

The two Lean theorems match the finite p. 13 block algebra:

```text
F2 = -A1^(-1) A2,
F3 = F3old - D A3 (C1 A1)^(-1),
C  = A4 - A3 A1^(-1) A2,
```

and the product-difference correction is

```text
D C - F3 F2.
```

The reviewer explicitly checked that `F3*F2` has shape `pi x nu`, matching
`D*C`, and that the order `F2*F3` would be ill-typed in the general indexed
statement.

No hidden inverse of `D` was found.  The only inverses in the coordinate
package are `A1^(-1)`, `(C1*A1)^(-1)`, and `Ctop^(-1)` in the inverse
coordinate map.  The new statements remain algebraic over a commutative ring
and do not assert analytic coverage, ideal transport, normal crossings, pole
order, or RLCT.

## Verification

The controller ran the focused build:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```

The reviewer also checked the file by direct Lean elaboration and ran
`git diff --check` on the Lean diff.

## Residual Risk

The source check used PDF text extraction, whose typography is imperfect, but
the relevant signs, multiplication order, and dimensions were preserved.
