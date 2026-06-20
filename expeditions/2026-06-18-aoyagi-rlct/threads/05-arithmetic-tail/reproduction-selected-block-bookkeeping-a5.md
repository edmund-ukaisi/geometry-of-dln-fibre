# Pen-and-paper reproduction - selected-block bookkeeping

Status: checked finite source-interval bookkeeping.

This note records the half-open selected-block arithmetic used by Aoyagi Lemma
5 equations `(3)` and `(4)`.  It is only bookkeeping for supplied selected
cutpoints; it does not construct a displayed vector.

## Source Normalisation

Definition 3 supplies selected indices

```text
S_1 < ... < S_(ell+1).
```

The Lean structure `AoyagiSelectedCutpoints` stores these as

```text
point C b = S_(b+1)
```

for `0<=b<=ell`.  The selected block with zero-based index `b` is

```text
block C b S
  iff b < ell and point C b - 1 <= S < point C (b+1) - 1.
```

Thus `block C b` is source

```text
S_(b+1)-1 <= S < S_(b+2)-1.
```

## Monotonicity

The adjacent strict source inequalities imply strict monotonicity of the
finite cutpoint map:

```text
b < c <= ell  =>  point C b < point C c.
```

Because `point` is total and returns `0` outside range, Lean states this only
with an in-range guard on the right endpoint.

## Disjoint Blocks

Suppose one source index `S` lies in two blocks `b` and `c`.  If `b<c`, then

```text
point C (b+1) <= point C c,
```

so the upper bound from block `b`,

```text
S < point C (b+1)-1,
```

contradicts the lower bound from block `c`,

```text
point C c - 1 <= S.
```

The case `c<b` is symmetric.  Therefore `b=c`.

## Own Left Endpoint

For `b<ell`, the left endpoint

```text
point C b - 1
```

belongs to `block C b`.  By block uniqueness, it belongs to no other selected
block:

```text
block C c (point C b - 1) iff c=b.
```

This is the branch-disambiguation needed for equation `(4)`'s own coordinate
`s=S_(p+1)-1`.

## Lean Targets

```text
AoyagiSelectedCutpoints.cut_strictMono
AoyagiSelectedCutpoints.point_strict_of_lt
AoyagiSelectedCutpoints.point_le_of_le
AoyagiSelectedCutpoints.block_index_unique
AoyagiSelectedCutpoints.block_leftEndpoint_iff
```

## Nonclaims

- No global monotonicity claim for the total accessor `point` outside its
  selected range.
- No claim that the last selected cutpoint `S_(ell+1)-1` lies in a selected
  block.
- No construction or existence proof for a displayed vector.
- No total source-layer coverage, terminal `tilde t=0`, vector admissibility,
  Case 1(2) chart sequence, Lemma 5 order count, pole order, normal crossings,
  or RLCT extraction.
