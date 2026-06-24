# Statement card - A6 Definition 3 selected/nonselected redundancy

Status: Lean bridge landed.

Reproduction:
`reproduction-definition3-selected-lt-from-nonselected-a6.md`.

Independent review:
`review-definition3-selected-lt-from-nonselected-a6.md`.

## Target

Show that Definition 3's `selected_lt_nonselected` condition follows from:

```text
ell * selected < selectedSum
selectedSum <= (ell - 1) * nonselected
0 <= selected.
```

Then provide a constructor for `AoyagiDefinition3SourceData` which takes
rank-width, strict selected inequalities, and nonselected upper inequalities,
but not a separate `selected_lt_nonselected` field.

## Intended Lean Names

```text
aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe
AoyagiDefinition3SourceData.of_selectedStrict_nonselectedLe_rankWidth
```

## Boundary

Selected cutpoints, cutpoint bounds, rank-width, strict selected inequalities,
and nonselected upper inequalities remain supplied.

No selected-cutpoint existence, no matrix-rank theorem, no Lemma 5 family
realisation, no chart production, no normal crossings, no pole order, and no
RLCT.

## Verification

Focused verification:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

passed on 2026-06-24.
