# A2 paper-order bridge notes

These notes record the source-to-Lean direction bridge for Aoyagi Theorem 3.
They are not a proof of the theorem.

## Direction convention

Aoyagi's paper order has maps

```text
A^(s) : W_(s+1) -> W_s
```

and total product

```text
A^(1) ... A^(L) : W_(L+1) -> W_1
```

on PDF pp. 8 and 11. The Lean chain in `ThroughLayerBasis.lean` uses
source-to-target edges

```text
A j : V j.castSucc -> V j.succ
```

so the direct translation is the reversal

```text
V_j = W_(L+1-j),    Lean edge j = paper layer s = L-j.
```

Lean prefixes are therefore Aoyagi paper suffixes. A Lean statement about
`chainMap V A 0 j` should not be read as a statement about the paper prefix
`A^(1) ... A^(S)` without this reversal. More explicitly, after reversal:

```text
Lean chainMap 0 -> k       = paper suffix A^(L-k+1) ... A^(L),
paper prefix A^(1) ... A^(S) = Lean suffix from vertex L-S to L.
```

The formal object `paperChainMap` records Aoyagi's descending product direction
directly, so paper prefixes and suffixes can be discussed without this mental
translation.

## Chart hypotheses

On PDF p. 11 Aoyagi assumes each layer matrix is near its base value, has rank
`r^(s)`, and satisfies `r^(s) >= r`, where `r` is the product rank. These are
rank-stratum hypotheses, not open-chart hypotheses. The proof also works
inside determinant charts:

- at the base step, the selected `r x r` block `A_1^(1)` is invertible;
- at the induction step, for `A'^(S+1) = (Q'_2)^(-1) A^(S+1)`, the selected
  `r x r` block `A'_1` is invertible;
- since `C'_1` is already invertible, the regularity of `C'_1 A'_1` is the
  same open-chart condition on `A'_1`.

The Lean through-basis construction justifies these determinant charts at the
base point after reversing to paper order: each true layer has adapted matrix
form `[I B; 0 D]`, and the transformed next layer stays `[I B-FD; 0 D]`.
In Lean's algebraic layer, determinant-chart membership should stay as an
explicit `IsUnit det` or invertible-corner hypothesis unless a real/complex
topology layer is introduced. The topological statement that determinant
nonvanishing at the base point gives a local open chart is separate.

## Needed elementary bridge statements

1. A paper-order chain/reindexing lemma: `paperChainMap` has the expected
   identity, one-edge, transitivity, and prefix/suffix split laws; then relate
   the reversed Lean chain to `paperChainMap`.
2. A finite chart-data-to-paper-block lemma: after reindexing, the concrete
   finite chart data gives paper-layer adapted bases with true layer matrices
   `[I B; 0 D]`, and the endpoint product matrix `[I 0; 0 0]`.
3. A transformed-next-layer chart lemma: `[I -F; 0 I] [I B; 0 D] =
   [I B-FD; 0 D]`, so the next selected determinant chart contains the base
   point. The block algebra is already Lean-proved; the paper-order wrapper is
   still pending.
4. A paper-order induction assembly using the chart-local block identity:
   recursively prove
   `Q_1^S (A^(1) ... A^(S)) Q_2^S =
   [C_1^S 0; 0 C^(1) ... C^(S)]`, with the moving right multiplier at the
   `W_(S+1)` cut. Preserve Aoyagi's order
   `A'^(S+1) = (Q'_2)^(-1) A^(S+1)`: the old right multiplier is absorbed
   into the next layer variables, and the new right multiplier lies at the
   `W_(S+2)` cut.
5. Optional rank corollaries: invertible multipliers preserve rank, and Lemma 2
   gives `rank C^(s) = r^(s) - r` under the source rank hypotheses.

## Nonclaims

This does not prove Aoyagi Theorem 3. It does not make product-rank
normalization an elementary step. Rank-`r` matrix normal form is elementary
linear algebra, but replacing the RLCT problem by the normalized target is
where PDF p. 11 invokes Aoyagi Lemma 1, which is outside the current Lean
citation boundary. It does not say product rank alone makes fixed top-left
charts invertible. It does not justify the RLCT shift on PDF p. 13; that
remains analytic/certificate work, including regular variables and pole-order
preservation.
