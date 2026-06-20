# Statement card - A5 Lemma 4 free-count bridge

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.highCount_castSucc_add_last_eq_total`
- `DLNFibre.DLN.Aoyagi.highCount_castSucc_int_eq_or_eq_pred_of_total`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min`

## Statement

Lean now proves the finite bridge from Aoyagi's Lemma 4 count to the equality
cases in the isolated Lemma 3 numerator.  If exactly `a` of the `ell`
increments are equal to `M`, then the number `b` of high increments among the
first `ell-1` increments is, over integers,

```text
b = a  or  b = a-1.
```

Therefore the already-proved Lemma 3 equality theorem gives the isolated
lower-bound value

```text
A(b) = a*ell*(ell-a).
```

## Proved

- A generic finite split of a count on `Fin (n+1)` into the `Fin n` initial
  part plus the last-coordinate indicator.
- The integer alternative `b=a or b=a-1` for the free high-count.
- The isolated Lemma 3 lower-bound value at this free high-count.
- A source-shaped wrapper using the terminal-`H` Lemma 4 sum bridge and the
  two-value increment hypothesis.

## Assumed

- The all-increment high count is `a`, or in the source wrapper:
  terminal-`H` sum bridge hypotheses, Definition 3's selected-width sum, and
  the two-value increment hypothesis.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- The two-value hypothesis from source vector inequalities.
- Vector admissibility and correspondence to `lambda`.
- The terminal exponent rewrite into the Lemma 3 quadratic.
- Lemma 5 chart-family admissibility, coverage, and order count.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma4-free-count-bridge-a5.md`.
- Review artifact:
  `review-lemma4-free-count-bridge-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
