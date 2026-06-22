# Review - A0 normal-crossing exponent interface

Review inputs:

- Aoyagi PDF pp. 5-6.
- `interface-draft.md`.
- `interface-repair-a2.md`.
- xhigh source review from `Hubble`.
- xhigh Lean/API review from `Boole`.

## Verdict

Pass, with scope limited to finite exponent arithmetic and an explicit cited
extraction hypothesis.

## Checks

- Active coordinates are filtered by `0 < lossExp` before ratios are collected.
- The ratio set is nonempty because the data requires an active coordinate.
- The finite minimum is taken over active ratios only.
- Chart counts are computed before imaging into `chartMinCounts`, so coordinate
  multiplicity is not lost by `Finset.image`.
- `exponentOrder` is the maximum chartwise count of coordinates attaining the
  global minimum, not a sum over charts.
- Non-minimum charts contribute count `0`, which is harmless when taking the
  maximum.
- The extraction object is named `AoyagiNormalCrossingExtractionHypothesis`,
  not an RLCT theorem.

## Remaining boundary

The analytic chart certificate is still absent: finite analytic cover,
normal-crossing unit factors, Jacobian/prior hypotheses, and the actual
identification with RLCT and pole order remain in the single allowed cited
normal-crossing extraction theorem.  Aoyagi Lemma 1, regular-coordinate
additivity, and Theorem 4 remain outside this interface.
