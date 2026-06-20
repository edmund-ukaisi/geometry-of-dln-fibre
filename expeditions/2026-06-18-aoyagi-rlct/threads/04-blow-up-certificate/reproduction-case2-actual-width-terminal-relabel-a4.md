# A4 Case 2 Actual-Width Terminal Relabel

Status: reproduced the elementary relabel of supplied recurrence and exponent
data from old `(S,J+1)` to stage `(S+1,0)` under actual next-width exhaustion.
This is not chart production and not a construction of Aoyagi's full next
following matrix.

## Source Anchor

Aoyagi's displayed Case 2 terminal paragraph on PDF pp. 20-22 stops after the
displayed pivot and moves to the next stage in the inductive notation.  In the
Lean bookkeeping, that move is only literally a relabel of the introduced
actual-width label domain under

```text
n(S+1) = J+1.
```

The previous terminal source-model checkpoint isolated this actual-width
exhausted branch.

## Pen-And-Paper Reproduction

The old post-pivot introduced labels at `(S,J+1)` are exactly

```text
s < S, plus layer S labels k <= J+1.
```

The stage-relabelled labels at `(S+1,0)` are exactly

```text
s < S+1.
```

Since labels use actual layer widths, the second set includes all layer `S`
labels

```text
1 <= k <= n(S+1).
```

Therefore, under `n(S+1)=J+1`, the two introduced-label domains are equal:

```text
introducedLabelFinset L n S (J+1)
  = introducedLabelFinset L n (S+1) 0.
```

Now a recurrence state is only a pair of total maps

```text
level : Nat -> Nat -> Nat,
var   : Nat -> Nat -> R.
```

So a relabelled state at `(S+1,0)` can copy the old post-state maps.  Its
finite-product recurrence factor is a product over the same finite label set
with the same level and variable functions, hence

```text
terminalRelabelPost.step = post.step.
```

The row weights are `monomialRec step`, hence they agree pointwise:

```text
terminalRelabelPost.weight i = post.weight i.
```

The level/least-value bridge also transports.  If

```text
leastValue'(s,k) = post.level(s,k)
```

for labels introduced at `(S,J+1)`, then the same equality holds for labels
introduced at `(S+1,0)`, because those are the same labels.

Finally, the exponent certificate package transports.  A one-label
`LabelExponentCertificate` mentions the state only through the proof that the
label is introduced.  The terminal exponent and least-value assertions depend
on the vector and scalar data, not on whether the domain is called `(S,J+1)` or
`(S+1,0)`.  Thus the introduced-label equivalence lets the same maps certify
the relabelled domain.

## Boundaries

- This copies supplied recurrence and exponent maps; it does not prove a chart
  produces them.
- It does not transport `Case2CorrectedExponentPostData` itself as new
  `(S+1,0)` post-data; it transports the resulting all-label certificate
  package.
- It does not transport Case 2 gap or flat-tail packages automatically, since
  those statements mention thresholds such as `S`, `J`, or
  `prefixMinNat n S`.
- It does not identify `[Ctop;C0]` with source-produced `C'^(S+1)`.
- It does not prove chart coverage, transition regularity, Jacobian arithmetic,
  normal crossings, RLCT extraction, termination, or printed-vector repair.

## Kill Conditions

- Do not use prefix-width exhaustion in place of `n(S+1)=J+1`.
- Do not rename the label `(S,J+1)` to `(S+1,0)`; labels remain actual source
  labels `(s,k)`.  The state name changes, not the label identity.
- Do not infer any chart-produced source following matrix or recurrence data
  from this relabel.
- Do not use this relabel to prove gap/tail invariants without separately
  checking the changed thresholds.
