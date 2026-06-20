# Pen-and-paper reproduction - Lemma 5 equation (3) boundary split

Status: checked finite boundary bookkeeping.

This note records the exact position of the special boundary in Aoyagi Lemma 5
equation `(3)`. It complements the existing `a=1` terminal obstruction by
separating the ordinary selected-span case `2<=a`.

## Source

Aoyagi PDF p. 27, equation `(3)`, has the special boundary assignment

```text
T(S_(ell-a+2)-1) = Htilde'_(ell-a+1)+1.
```

In Lean's zero-based selected-cutpoint notation this boundary point is

```text
C.point (ell-a+1)-1.
```

The supplied equation `(3)` certificate carries `1<=a` and `a<=ell`.

## Boundary Index

Since `1<=a`, the boundary index is in range:

```text
ell-a+1 <= ell.
```

Under `a<=ell` and `1<=a`, it is strictly before the terminal selected index
exactly when

```text
ell-a+1 < ell  iff  2<=a.
```

Thus:

- if `2<=a`, the special boundary is the left endpoint of selected block
  `ell-a+1`;
- if `a=1`, the special boundary is the terminal selected endpoint
  `S_(ell+1)-1`.

## Consequences

For `2<=a`, the boundary lies in the half-open selected span

```text
S_1-1 <= S < S_(ell+1)-1.
```

For `a=1`, it is outside every half-open selected block. The earlier terminal
obstruction proves that, under the selected-sum identity, the supplied equation
`(3)` branch value there is `1`. Therefore an additional terminal endpoint zero
assignment is incompatible with the supplied equation `(3)` certificate.

## Lean Targets

```text
aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector
aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff
aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le
aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le
aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le
aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one
aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one
aoyagiLemma5Eq3_no_terminalEndpointZero_of_one
```

## Nonclaims

- This does not construct equation `(3)`'s displayed vector.
- This does not prove terminal `tilde t=0`.
- This does not prove introduced-label status, a Case 1(2) chart sequence,
  vector admissibility, Lemma 5 order count, normal crossings, or RLCT
  extraction.
