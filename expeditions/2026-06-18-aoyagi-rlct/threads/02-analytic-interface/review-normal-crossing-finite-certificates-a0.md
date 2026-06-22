# Review - A0 normal-crossing finite certificates

Date: 2026-06-22.

Reviewer: xhigh reviewer `Kierkegaard the 2nd`.

## Verdict

Pass.

## Findings

No findings.

## Scope Check

The added Lean lemmas are finite `Finset.min'` and `Finset.max'` certificate
wrappers.  The minimum lemmas require active-ratio membership or an active
coordinate witness plus lower bounds.  The order lemmas require chart-count
membership or a realizing chart plus upper bounds.

The docs keep analytic extraction as cited-only and explicitly exclude chart
production, normal crossings, pole-order proof, and RLCT extraction.

## Checks

Reviewer check:

```text
lake env lean DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean
```

Controller closeout additionally ran focused module, aggregator, full-library,
sorry, and diff checks.
