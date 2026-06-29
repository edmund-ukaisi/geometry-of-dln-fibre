# Review - A2 open-source-stratum signed-box two-sided loss-density iff

Date: 2026-06-29.

Status: PASS.

## Object Reviewed

Lean theorem:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_iff_residual_power_lt_top_of_openSourceStratum_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

Documentation:

```text
reproduction-a2-open-source-stratum-signed-box-two-sided-loss-density-iff.md
statement-card-a2-open-source-stratum-signed-box-two-sided-loss-density-iff.md
```

## Controller Review

Pass with boundary.

The theorem is deliberately not a one-sided local-source coverage wrapper.  For
signed-box residual data, the pushforward identity is attached to the source
measure being restricted.  The statement therefore assumes the pushforward for
the exact local piece `Ulocal inter sourceStratum`.

The proof only uses:

```text
nhdsWithin x0 (Ulocal inter sourceStratum) = nhdsWithin x0 sourceStratum
```

for open `Ulocal` containing `x0`, the local-source signed-box two-sided iff,
and intersection rewriting.  It does not assume signed-box critical
inequalities, source-density nonnegativity, or source-density upper bounds.
Residual local boundedness remains explicit.

## Xhigh Review

Volta passed the theorem shape.  The review confirmed that the key boundary is
correct: the wrapper must use `source := Ulocal inter sourceStratum` and
require the weighted signed-box pushforward for that exact source, since a
pushforward for the whole stratum or for a larger local source does not
formally restrict without extra chart-preimage or support data.

The review also confirmed that the hypotheses are sufficient: no separate
residual positivity, residual a.e. measurability, source-density a.e.
measurability, source-density upper bound, critical inequality, or positive
signed-box radius hypothesis is needed for this iff wrapper.  Possible vacuity
from zero local measure remains external and should not be folded into this
socket.

## Hygiene

Passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Passed:

```text
scripts/sorries
git diff --check
```

The touched Lean-file forbidden-marker scan passed.  Direct axiom probe for
the new theorem returned `[propext, Classical.choice, Quot.sound]`.
