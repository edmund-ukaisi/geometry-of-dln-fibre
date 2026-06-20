# A4 Case 2 Arbitrary-Suffix Terminal Wrapper

Status: reproduced the arbitrary supplied-suffix version of the stopped Case 2
source-row terminal wrappers.

## Source Anchor

Aoyagi's stopped Case 2 terminal display on PDF pp. 21-22 has a remaining
right product

```text
prod_{s=S+2}^L C^(s).
```

Previous Lean wrappers specialized the following product to
`sourceSuffixProduct`.  The algebraic stopped-terminal identity, however, only
uses the fact that this object is a matrix multiplying on the right.  We can
therefore keep the following product as an arbitrary supplied matrix `F`.

## Pen-And-Paper Reproduction

Let `F : Matrix τ υ R` be any composable following matrix: its row/input type
`τ` matches the column/output type of the terminal `C'` factor, while its
output column type `υ` is arbitrary.  The stopped displayed Case 2 calculation
has the form

```text
ideal(((oldTop + transformedResidual) * followingRows) * F)
  =
ideal(paperTerminalCandidate * F).
```

The source-row terminal candidate is just a reindexing of the same paper
terminal candidate:

```text
ideal(sourceRowTerminalProduct(F))
  =
ideal(paperTerminalCandidate * F).
```

Therefore

```text
ideal(((oldTop + transformedResidual) * followingRows) * F)
  =
ideal(sourceRowTerminalProduct(F)).
```

If a supplied terminal bridge identifies the source-row terminal candidate
with a matrix `Cterm`, then the right hand side rewrites as

```text
ideal((terminalWeight * Cterm) * F).
```

In the actual-width branch `n(S+1)=J+1`, the stopped condition follows because
the prefix minimum at `S+1` is at most the actual width `J+1`.  The relabelled
post-state has the same surviving pivot weight as the displayed post-state,
and actual-width column exhaustion supplies the original-row bridge

```text
Cterm = rows 1..J+1 of C.
```

Thus the actual-width arbitrary-suffix theorem rewrites the stopped terminal
right hand side as

```text
ideal((terminalWeight(relabelled post) * originalRows(1..J+1)) * F).
```

## Lean Shape

The proved names are:

```text
exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont
exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont
exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth
exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth
```

They are the arbitrary-`F` companions of the existing
`sourceSuffixProduct`-specialized wrappers.

## Boundaries

- `F` is supplied.  No theorem here proves that `F` is the raw
  `sourceSuffixProduct`, an empty suffix, or a chart-produced following
  product.
- The supplied terminal bridge is consumed, not produced.
- The actual-width original-row specialization uses exactly
  `n(S+1)=J+1`; it does not apply to the row-exhausted wide-next branch.
- No source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
  Jacobian arithmetic, normal crossings, RLCT extraction, termination,
  transition invariance, or printed-vector repair is proved.
