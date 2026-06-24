# Statement card - A6 Definition 3 ell=1 nonselected obstruction

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9.

## Lean Statement

`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

```text
AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
```

## Claim

If `S : AoyagiDefinition3SourceData L 1 H r C` and source-range rank-width
nonnegativity holds, then every source-range reduced-width value belongs to
the selected value set:

```text
aoyagiReducedWidthInt H r s in
  Finset.univ.image
    (fun j : Fin (1+1) => aoyagiReducedWidthInt H r (C.cut j)).
```

Equivalently, under these hypotheses there is no genuinely nonselected
reduced-width value when `ell=1`.

## Proof Idea

Assume a source-range value is not selected.  Definition 3's nonselected upper
inequality gives the selected sum `T <= (1-1)*width = 0`.  Rank-width
nonnegativity at the two selected cutpoints gives `0 <= T`, hence `T=0`.
The strict selected inequality gives `m_0 < T = 0`, contradicting
nonnegativity of `m_0`.

## Nonclaims

- No selected-cutpoint construction.
- No classification for `ell > 1`.
- No correction of Aoyagi's printed Definition 3.
- No claim without rank-width nonnegativity.
- No Eq5 endpoint-family construction, Lemma 5 exactness, chart production,
  pole order, or RLCT.

## Verification

Focused build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

