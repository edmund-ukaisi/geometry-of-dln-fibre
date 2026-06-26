# Review - A2 retained-passive active endpoint package

Date: 2026-06-26.

Reviewer: xhigh read-only agent `Faraday the 3rd`.

## Verdict

Pass after documentation status fix.

## Findings

Low issue fixed: the reproduction status originally said this was a
pen-and-paper package for the next finite Lean theorem.  That was stale after
the Lean theorem landed.  The line now says it is the pen-and-paper package for
the finite Lean endpoint theorem.

No Lean correctness issues were found.

## Audit Notes

The theorem preserves the existing `A1_0` order convention.  The full top
product is `Tail * A1_0`, the endpoint solve is

```text
A1_0 = Tail^-1 * Ctop,
```

and the package applies the prior `Ctop` endpoint theorem directly.

The `A3_last` sign and order are unchanged.  The package hypothesis is exactly

```text
A3_last = -(F3 - EarlyTail) * CtopLast,
```

and the proof applies the prior lower-left endpoint solve directly.

The active upper-right readback

```text
-S_0.B = F2_0
```

matches the suffix-state convention: the underlying suffix-state theorem gives
`S_i.B = -F2_i`, and the package only negates at `i=0`.

The final `CtopLast` determinant-unit hypothesis used for the `A3_last` solve
is legitimately derived from the full `A1` unit family.  The full family
includes `A1_0` through the solved-`A1_0` determinant-unit theorem, so the
single-edge case is covered.

The transformed-edge conclusion uses the correct suffix state:

```text
transformedEdge E p (suffixState E last p.succ _) =
  retainedPassiveTransformedEdge A1 F2 A3 C p.
```

It does not assert a source inverse.

## Residual Risk

The reviewer was read-only and did not run Lean.  The controller ran the
focused build for `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates`.

The next open theorem remains the bundled coordinate-domain/two-sided local
inverse layer, not source coverage, source/image equality, or measure
transport.
