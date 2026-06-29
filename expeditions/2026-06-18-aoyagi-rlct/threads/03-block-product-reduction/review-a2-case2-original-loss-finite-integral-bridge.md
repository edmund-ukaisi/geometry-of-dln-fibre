# Review: A2 Case 2 original-loss finite-integral bridge

Reviewer: xhigh `Wegener the 3rd`.

Verdict: PASS after stale-card fix.

## Findings

- Low: the statement card initially had a stale proof-status line after the
  Lean theorem had been proved.  The status line has been corrected.

## Fidelity Check

The Lean theorem concludes only finite integrability of endpoint-basis
original square-Frobenius `lossDLN` over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

where `mu` is the selected-entry chart-produced pushforward measure.  It does
not remove the source-stratum restriction or identify an external source
prior.

The lower-bound proof composes the self-base adapted product-difference lower
bound with `EndpointLossComparison`, rewrites adapted Frobenius loss to the
adapted square-sum, and uses the positive product constant `c0 * cprod` in the
generic Case 2 finite-integral socket.

## Radius Check

The radius bookkeeping matches the adapted bridge:

- density bounds are produced at `Rden <= Rmax`;
- the adapted lower-bound theorem is called with `Rmax := Rden`;
- density bounds are restricted to the final `R`;
- the final `R <= Rmax` follows by transitivity.

## Nonclaim Check

No overclaim was found about external source-prior transport, Jacobian
transport, selected-entry source/image equality, normal crossings, pole order,
or RLCT.

The reviewer did not rerun the focused Lean build.  The controller's focused
build and hygiene gates are recorded in the thread ledger.
