# A4 Case 1(1) Selected-Old Same-Domain Boundary

Status: reproduced a narrow supplied boundary tying together two already
separate elementary pieces.

## Source Situation

On Aoyagi PDF p. 16, Case 1(1) chooses the old exceptional variable
`u_(s,k)` itself as the chart denominator.  The row strip

```text
J+1 <= i <= J+J1,     J+1 <= j <= M^(S+1)
```

is divided by this selected old variable.  The same branch lowers the selected
old label from level `J+J1` to level `J` and adds

```text
J1 * (M^(S+1)-J)
```

to its numerator.  All non-selected introduced labels stay in the same
introduced-label domain `(S,J)`.

This checkpoint is only a supplied boundary for that branch.  It does not
construct the chart or prove that source coordinates produce the supplied
post-data.

## Boundary Data

Assume:

```text
hcert  : exponent certificates over the introduced labels at (S,J),
hfirst : Case 1 first-jump data selecting the old label (s0,k0),
hinv   : level/least-value and flat-tail invariants for introduced labels,
2 <= S <= L,
hpost  : supplied selected-old lower-tail exponent post-data.
```

The supplied post-data says:

```text
t'_(s0,k0)        = lowerTailVector(t_(s0,k0), S, J),
numerator'_(s0,k0)
  = numerator_(s0,k0) + J1 * (M^(S+1)-J),
leastValue'_(s0,k0) = J,
```

and for every other introduced label `(s,k) != (s0,k0)`,

```text
t'_(s,k)          = t_(s,k),
numerator'_(s,k)  = numerator_(s,k),
leastValue'_(s,k) = leastValue_(s,k).
```

The lower-tail certificate theorem then proves an
`IntroducedLabelExponentCertificates` package over the same domain `(S,J)`.
There is no domain extension and no new label `(S,J+1)`.

## Source-Coordinate Projection

Separately, for source residual data, let `u_old = u_(s0,k0)` and set

```text
D_source(i,j) = u_old * D_post(i,j)    on the selected old row strip,
D_source(i,j) = D_post(i,j)            below the strip,
```

with post row weights

```text
b_post(i) = u_old * b_pre(i)           on the selected old row strip,
b_post(i) = b_pre(i)                   below the strip.
```

Entrywise,

```text
b_pre(i) * D_source(i,j) = b_post(i) * D_post(i,j).
```

Thus

```text
diag(b_pre) * D_source = diag(b_post) * D_post.
```

This is a parallel projection from the same Case 1(1) boundary, not a proof
that the matrix identity produces the exponent post-data.

## Caveats

- The boundary stays at `(S,J)` and does not introduce `(S,J+1)`.
- The scalar is the selected old denominator `u_(s,k)`, not the displayed
  Case 1(2) pivot `u_(S,J+1)`.
- No displayed-pivot normalization `residual(J+1,J+1)=1` is used.
- No `Q/P` identity is asserted.
- No chart construction, atlas coverage, regularity, transition regularity,
  Jacobian, normal crossings, RLCT extraction, or full transition invariant is
  proved.
