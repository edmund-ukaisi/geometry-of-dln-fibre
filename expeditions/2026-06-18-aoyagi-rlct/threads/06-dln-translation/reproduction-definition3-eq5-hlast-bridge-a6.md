# Reproduction - Definition 3 Eq5 hlast bridge

Date: 2026-06-24.

Status: reproduced; Lean bridge landed.

Independent review:
Darwin the 2nd, xhigh read-only slice review.

## Question

The Definition 3 Eq5 terminal-order bridge still carries the explicit endpoint
source-range hypothesis

```text
hlast : C.point (N+1) <= L+1.
```

But `AoyagiDefinition3SourceData L ell H r C` already stores the source-range
bound

```text
cut_le : forall j : Fin(ell+1), C.cut j <= L+1.
```

For `ell = N+1`, the endpoint `C.point (N+1)` is exactly the last finite
cutpoint `C.cut (Fin.last (N+1))`.  Therefore `hlast` should be derived from
the Definition 3 source data rather than supplied again.

## Source Anchor

Aoyagi Definition 3 selects indices

```text
1 <= S_1 < ... < S_(ell+1) <= L+1.
```

The Lean structure `AoyagiDefinition3SourceData` records the upper endpoint
part as `cut_le`.

## Pen-and-paper Calculation

Assume

```text
Ssrc : AoyagiDefinition3SourceData L (N+1) H r C.
```

The last selected index is represented in Lean by

```text
Fin.last (N+1) : Fin ((N+1)+1).
```

By `Ssrc.cut_le`:

```text
C.cut (Fin.last (N+1)) <= L+1.
```

By the definition of `AoyagiSelectedCutpoints.point`, since
`N+1 < (N+1)+1`,

```text
C.point (N+1) = C.cut (Fin.last (N+1)).
```

Thus:

```text
C.point (N+1) <= L+1.
```

This is exactly the `hlast` argument consumed by the existing Eq5 terminal
cardinal-squeeze theorem.

## Lean Shape

Add the source-data extractor:

```text
AoyagiDefinition3SourceData.lastPoint_le
```

Then update the Definition 3 Eq5 terminal-order wrapper so that `hlast` is no
longer an explicit hypothesis; it should pass `Ssrc.lastPoint_le`.

## Nonclaims

This does not construct selected cutpoints or Definition 3 source data.

It does not prove any Eq5 endpoint-family construction, actual-width/block
dominance, injectivity, branch synchronisation, terminal exactness, chart
production, normal crossings, pole order, or RLCT.

## Verification

Focused Lean build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
```
