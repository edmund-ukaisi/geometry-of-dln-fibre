# Pen-and-paper reproduction - Lemma 5 equation (5) width-bound counterexample

Status: checked guardrail counterexample.

This note records a closed obstruction to deriving the equation `(5)` block
width bound from Aoyagi Definition 3-shaped selected-width hypotheses alone.
It complements the conditional block-width bridge: the bridge is valid, but
the required actual-width dominance is additional data.

## Source

Aoyagi Definition 3 selects cutpoints and the selected width values

```text
M = {M(S_j) : j=1,...,ell+1}.
```

Its non-selected width condition is value-level: it applies when an actual
width value is not in this selected value set.  Lemma 5 equation `(5)` uses a
source index `s` lying in a selected block and needs the own selected width
`W_p` to be a legal actual source label at layer `s+1`.  In Lean this width
legality is the bound

```text
W_p <= n(S+1).
```

## Counterexample

Take

```text
ell = 3,  M = 3,  a = 1,
selected cutpoints = 1, 3, 5, 7,
selected widths    = 1, 2, 2, 2.
```

The selected sum is

```text
1+2+2+2 = 7 = 3*(3-1)+1,
```

and the strict selected inequalities hold:

```text
3*1 < 7,
3*2 < 7.
```

Define actual widths so that they match the selected widths at the selected
cutpoints,

```text
n(1)=1, n(3)=2, n(5)=2, n(7)=2,
```

but put

```text
n(6)=1.
```

Let `p=2` and `S=5`.  The selected block condition holds:

```text
C.point 2 - 1 = 4 <= 5 < 6 = C.point 3 - 1.
```

Thus the source layer used by the label is `S+1=6`.  The selected width for
block `p=2` is

```text
W_p = 2,
```

while the actual width at this source layer is

```text
n(S+1)=n(6)=1.
```

Therefore the required Eq5 width bound fails:

```text
not (2 <= 1).
```

## Why This Does Not Violate Definition 3

The bad unselected layer has width value `1`.  That value is already selected
at the first cutpoint.  Hence a Definition 3 condition of the form

```text
if n(t) is not one of the selected width values, then n(t) dominates
the selected widths
```

does not apply to `t=6`.  This is the point of the example: value-level
non-selected dominance is weaker than the index-level off-selected dominance
used by the Lean bridge.

## Lean Target

```text
aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example
```

The Lean theorem includes selected cutpoint compatibility and the value-level
non-selected condition, and concludes the failure of
`aoyagiSelectedWidthNat 3 m p <= n(S+1)`.

## Nonclaims

- No failure of the conditional block-local width bridge.
- No failure of the index-level off-selected dominance bridge.
- No construction of equation `(5)`'s displayed vector.
- No chart sequence, admissibility, pole order, normal crossings, or RLCT
  extraction.
