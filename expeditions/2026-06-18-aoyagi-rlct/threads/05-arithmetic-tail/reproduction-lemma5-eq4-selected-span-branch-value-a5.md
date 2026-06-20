# Pen-and-paper reproduction - Lemma 5 equation (4) selected-span branch values

Status: checked conditional selected-span branch bookkeeping.

This note records only the finite branch-domain bookkeeping for Aoyagi Lemma 5
equation `(4)`.  It assumes a supplied piecewise branch certificate for a
function `T`; it does not construct that function.

## Source Normalisation

Write

```text
c = ell-a,
r = p+c+1,
q = S_(p+c+2)-1.
```

In Lean's zero-based selected-cutpoint convention,

```text
point C b = S_(b+1),
block C b S iff S_(b+1)-1 <= S < S_(b+2)-1.
```

Thus the special boundary in equation `(4)` is

```text
q = point C r - 1.
```

The selected span is the half-open interval

```text
S_1-1 <= S < S_(ell+1)-1.
```

## Branch Split

For a selected block `block C b S`, equation `(4)` splits as follows.

```text
b = 0:
  T(S) = M(S+1).

1 <= b <= p:
  T(S) = U_b - b.

p < b <= p+c:
  T(S) = U_b - p.

S = q:
  T(S) = U_(p+c) - p + 1.

r <= b and q < S:
  T(S) = U_b.
```

Here `U_b` denotes the upper displayed chain value
`aoyagiHtildeUpperNat ell a M m b`.

The boundary `q` is the right endpoint of block `p+c`, so it is excluded from
the middle branch by the half-open block convention.  If `r<ell`, it is the
left endpoint of block `r`; if `r=ell`, it is the terminal selected endpoint
`S_(ell+1)-1` and does not lie in the selected span.

The strict guard `q<S` in the tail branch is therefore necessary.  Without it,
the left endpoint of block `r` would be incorrectly included in the tail branch
when `r<ell`.

## Span Coverage

The already-proved selected-span coverage theorem supplies a block for every

```text
point C 0 - 1 <= S < point C ell - 1.
```

The branch classifier applies to that block.  Therefore a supplied equation
`(4)` piecewise certificate gives one of the advertised branch values for every
source index in the selected span.

## Lean Targets

```text
AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne
AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block
AoyagiLemma5Eq4SelectedSpanBranchValue
aoyagiLemma5Eq4_branchValue_of_block
aoyagiLemma5Eq4_selectedSpan_branchValue
```

## Nonclaims

- No construction or existence theorem for the displayed equation `(4)` vector.
- No total source-layer coverage.
- No claim at the terminal endpoint `S_(ell+1)-1`.
- No terminal `tilde t=0`, vector admissibility, source vector-to-chain
  correspondence, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, or RLCT extraction.
- The repaired selected-index guard `p+1<=a` remains necessary when connecting
  the displayed source formula to Definition 3's selected list, even though the
  pure conditional classifier uses the total `point` accessor.
