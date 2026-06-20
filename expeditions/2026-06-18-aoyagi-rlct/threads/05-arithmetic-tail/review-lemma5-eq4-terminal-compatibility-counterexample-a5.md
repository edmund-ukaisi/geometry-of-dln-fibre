# Review - Lemma 5 equation (4) terminal compatibility counterexample

Reviewer: xhigh `Boole`.

Scope:

- `aoyagiLemma5Eq4_lastWidthCompatibility_not_forced_by_selectedWidthHypotheses_example`;
- reproduction, statement card, and ledger updates.

## Findings

None blocking.

## Verdict

Pass.

For `ell=3`, `a=2`, `p=1`, `M=3`, and all four selected widths equal to `2`,
the range guards hold:

```text
1<=ell,  a<=ell,  1<=p,  p<=ell-a,  p+1=a.
```

The equation `(4)` boundary is terminal:

```text
p+(ell-a)+1 = ell.
```

The selected-sum identity holds:

```text
sum W_i = 8 = 3*(3-1)+2 = ell*(M-1)+a.
```

The strict selected-width inequalities hold since `ell*W_i=6<8` for every
selected width.  The last-width compatibility fails because

```text
W_(ell+1)=2,    M-p+1=3.
```

So the equation `(4)` terminal branch value is `1`, not `0`.

This is source-faithful evidence that Definition 3's selected-width arithmetic
does not force the equation `(4)` terminal-extension compatibility.  It is not
a disproof of Lemma 5 or of Aoyagi's full chart construction.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
