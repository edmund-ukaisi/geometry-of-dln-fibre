# Review - A2 regular-variable rank-width shift

Reviewer: xhigh `Ramanujan the 3rd`.

Status: passed, with scope correction incorporated.

## Verdict

The reduction is legitimate.  The finite regular-variable shift needs only
the endpoint inequalities

```text
r <= H 1,
r <= H (L+1).
```

These are exactly projected from the source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

The reviewer noted that endpoint projections are sufficient for the finite
shift itself, but not for the final Definition 3 handoff, because the final
handoff also returns selected-width side facts and therefore needs full
source-range `hr` at all selected cutpoints.

## Implemented Correction

Lean keeps the final bridge at the full `hr` level.  The finite constructors
project endpoints internally, and the final bridge passes the same `hr` to
both Definition 3 source-data provenance and the finite regular-variable
shift constructor.

## Nonclaims

This does not construct regular-suspension charts, prove analytic ideal
transport, prove Aoyagi Lemma 1, produce normal-crossing data, prove
active-ratio/chart-count facts, or extract pole order/RLCT.
