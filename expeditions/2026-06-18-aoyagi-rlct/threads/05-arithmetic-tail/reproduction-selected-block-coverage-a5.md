# Pen-and-paper reproduction - selected-block coverage

Status: checked finite selected-span bookkeeping.

This note extends the selected-block bookkeeping for Aoyagi Lemma 5 equations
`(3)` and `(4)`.  It proves only that the half-open selected blocks cover the
selected span from `S_1-1` to `S_(ell+1)-1`.  It does not cover source layers
outside that selected span.

## Source Normalisation

With zero-based Lean indexing,

```text
point C b = S_(b+1).
```

The selected block `b` is

```text
block C b S
  iff b < ell and point C b - 1 <= S < point C (b+1) - 1.
```

The selected span is

```text
point C 0 - 1 <= S < point C ell - 1,
```

that is

```text
S_1 - 1 <= S < S_(ell+1) - 1.
```

## Block Implies Span

If `S` lies in `block C b`, then `b<ell`.  Since the selected cutpoints are
increasing,

```text
point C 0 <= point C b,
point C (b+1) <= point C ell.
```

Together with the block inequalities, this gives

```text
point C 0 - 1 <= S < point C ell - 1.
```

## Span Implies Block

Assume

```text
point C 0 - 1 <= S < point C ell - 1.
```

Let `j` be the first index with

```text
S < point C j - 1.
```

Such an index exists because `j=ell` works.  The lower span bound prevents
`j=0`, so `0<j`.  By minimality of `j`, the predecessor `j-1` satisfies

```text
point C (j-1) - 1 <= S.
```

Thus

```text
point C (j-1) - 1 <= S < point C j - 1,
```

and since `j<=ell` and `0<j`, the index `b=j-1` satisfies `b<ell`.  Hence
`S` lies in `block C (j-1)`.

## Lean Targets

```text
AoyagiSelectedCutpoints.block_mem_selectedSpan
AoyagiSelectedCutpoints.exists_block_of_mem_selectedSpan
AoyagiSelectedCutpoints.exists_block_iff_mem_selectedSpan
```

## Nonclaims

- No claim that selected blocks cover `S < S_1-1`.
- No claim that selected blocks cover `S >= S_(ell+1)-1`.
- No claim that `S_(ell+1)-1` lies in a selected block.
- No displayed-vector construction, terminal `tilde t=0`, vector
  admissibility, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, or RLCT extraction.
