# Pen-and-paper reproduction - Lemma 5 equation (4) boundary split

Status: checked finite source-boundary bookkeeping.

This note records only the strict-versus-terminal split for Aoyagi Lemma 5
equation `(4)`'s special boundary.  It assumes supplied selected cutpoints and
does not construct the displayed vector.

## Source Normalisation

Aoyagi equation `(4)` uses the special boundary

```text
S_(p+ell-a+2)-1.
```

In Lean's zero-based selected-cutpoint notation this is

```text
point C (p + (ell-a) + 1) - 1.
```

Write

```text
r = p + (ell-a) + 1.
```

The repaired source-index guard is `p+1<=a`, under `a<=ell`, because

```text
r <= ell  iff  p+1 <= a.
```

This is the source-index repair for the printed guard `p<=a`.

## Strict Boundary Case

Under `a<=ell`,

```text
r < ell  iff  p+1 < a.
```

So if `p+1<a`, the boundary point is the left endpoint of selected block `r`:

```text
block C r (point C r - 1).
```

Consequently it lies in the half-open selected span

```text
point C 0 - 1 <= point C r - 1 < point C ell - 1.
```

This is the case where the singleton boundary point is inside the selected
span, even though it is still separated from the strict tail branch.

## Terminal Boundary Case

Under `a<=ell`,

```text
r = ell  iff  p+1 = a.
```

So if `p+1=a`, the special boundary is the terminal selected endpoint:

```text
point C r - 1 = point C ell - 1.
```

The terminal selected endpoint is not in any half-open selected block.  This is
why the selected-span classifier must not be used at that point.

## Lean Targets

```text
aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff
aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff
aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard
aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard
aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary
aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary
```

## Nonclaims

- No construction or existence proof for equation `(4)`'s displayed vector.
- No terminal `tilde t=0`.
- No selected-span classification at the terminal endpoint.
- No vector admissibility, source vector-to-chain correspondence, Case 1(2)
  chart sequence, chart coverage, Lemma 5 order count, pole order, normal
  crossings, or RLCT extraction.
