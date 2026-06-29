# Review: A2 Case 2 adapted product-difference finite-integral bridge

Reviewer: xhigh `Planck the 3rd`.

Verdict: PASS.

## Findings

No concrete findings.

## Fidelity Check

The Lean theorem matches the statement card and reproduction.  It concludes
only finite integrability for the adapted p.13 product-difference square-sum
over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

with `0 < R`, `R <= Rmax`, `0 <= C`, and open `U` containing `base`.

The adapted-product-difference loss is specialised directly.  The lower
comparison is derived from the self-base product-coordinate theorem rather
than supplied as a hypothesis.  The call to the existing Case 2 source-stratum
socket is the expected dependency and does not rewrite away `sourceStratum` or
claim source support.

## Radius Check

The radius bookkeeping is correct:

- density bounds are produced at `Rden`;
- the adapted lower-bound theorem is applied with `Rmax := Rden`;
- density bounds are restricted to the final `R`;
- the final `R <= Rmax` follows by transitivity.

## Nonclaim Check

No original-loss identification, source-prior/Jacobian transport, source-rank
support rewrite, normal-crossing theorem, pole-order computation, or RLCT claim
appears in the Lean statement.

The reviewer did not rerun the focused Lean build.  The controller's focused
build and hygiene gates are recorded in the thread ledger.
