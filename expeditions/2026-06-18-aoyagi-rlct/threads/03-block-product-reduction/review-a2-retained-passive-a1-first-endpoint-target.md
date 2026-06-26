# Review - A2 retained-passive `A1_0` endpoint target

Date: 2026-06-26.

Reviewer: xhigh read-only agent `Huygens the 3rd`.

## Verdict

Pass.

## Findings

No issues found.

## Audit Notes

The reviewer checked the product orientation against the suffix-state
convention `Ctop_p = Ctop_{p+1} * A1_p` and the `residualFactorProduct`
unfold.  The split

```text
residualFactorProduct A1 last 0 = Tail * A1_0
```

has the correct order.

The endpoint solve

```text
A1_0 = Tail^-1 * Ctop
```

has the correct noncommutative order.  The proof cancels on the left:

```text
Tail * (Tail^-1 * Ctop) = (Tail * Tail^-1) * Ctop.
```

The determinant-unit hypotheses are explicit.  The lower-level cancellation
lemma still assumes `det(Tail)` is a unit.  The packaged full-family and
suffix-state endpoint theorems derive `det(Tail)` unit from the passive
pointwise hypotheses.

The follow-up delta review checked the added
`retainedPassiveA1TailAfterFirst_det_isUnit_of_passive` induction.  Its motive
is guarded by `1 <= m`; the step constructs the current passive factor with
value `m`, proves that factor is not `0`, and applies the passive hypothesis
only to that factor.  The induction is instantiated at `m = 1`, so it never
requires a unit hypothesis for `A1_0`.

The Lean theorem proves only the active top-left endpoint statement

```text
(suffixState E last 0).Ctop = Ctop.
```

It does not claim source coverage, source/image equality, measure pushforward,
density/Jacobian accounting, normal crossings, pole order, or RLCT.

## Residual Risk

The reviewer was read-only and did not run Lean.  The controller ran the
focused build for `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates`.

The next open theorem is the retained-passive source-map/readback packaging:
combine this `A1_0` endpoint with `A3_last`/`F3`, `F2` readback, transformed
edge reconstruction, and determinant-unit hypotheses, still without asserting
coverage or measure transport.
