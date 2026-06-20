# A4 Source Suffix Raw Chain Split

Status: reproduced the raw paper-order matrix-chain split used by later
source suffix utilities.

## Source Anchor

Aoyagi's stopped Case 2 terminal display on PDF pp. 21-22 contains the
remaining right product

```text
prod_{s=S+2}^L C^(s).
```

Lean names this raw paper-order suffix as `sourceSuffixProduct`, backed by the
more general chain `paperMatrixChain`.

## Pen-And-Paper Reproduction

The raw chain is ordered by increasing paper edge index and extends its upper
endpoint by right multiplication:

```text
chain(i,p+1) = chain(i,p) * C(p).
```

Therefore, for `i <= m <= j`,

```text
chain(i,j) = chain(i,m) * chain(m,j).
```

The proof is induction on the upper endpoint `j`.

- If `j=m`, then `chain(m,m)=1` and the equality is
  `chain(i,m)=chain(i,m)*1`.
- If `j=p+1` and `m<p+1`, then both sides extend by the same right edge:

```text
chain(i,p+1)
  = chain(i,p) * C(p)
  = (chain(i,m) * chain(m,p)) * C(p)
  = chain(i,m) * (chain(m,p) * C(p))
  = chain(i,m) * chain(m,p+1).
```

This proves the split without changing endpoints by casts.  Source-suffix
empty and peel statements are still separate dependent-endpoint wrappers around
this raw theorem.

## Lean Shape

The proved theorem is:

```text
paperMatrixChain_trans
```

with statement:

```text
paperMatrixChain κ C i j (him.trans hmj)
  =
paperMatrixChain κ C i m him * paperMatrixChain κ C m j hmj.
```

## Boundaries

- This is raw matrix-chain algebra only.
- It does not prove any source chart is produced by a blow-up coordinate map.
- It does not yet state the cast-heavy empty or one-edge source-suffix
  wrappers.
- It does not prove chart coverage, Jacobian arithmetic, normal crossings,
  RLCT extraction, termination, transition invariance, or printed-vector
  repair.
