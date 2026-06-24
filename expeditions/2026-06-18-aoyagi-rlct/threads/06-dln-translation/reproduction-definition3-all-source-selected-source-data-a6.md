# Reproduction - Definition 3 all-source selected source data

Status: xhigh checked; formalisation-ready.

## Source Shape

This is a restricted Definition 3 source-data constructor.  It chooses all
source layers as selected cutpoints:

```text
ell = L,
S_j = j        for j = 1, ..., L+1.
```

In Lean's zero-based indexing this is:

```text
C.cut j = j.val + 1    for j : Fin (L+1).
```

## Hypothesis

Assume `0 < L` and the strict selected inequality for every source layer,
stated against the consecutive all-source sum:

```text
L * M^(s) < sum_{j : Fin (L+1)} M^(j.val+1)
```

for all `s` with `1 <= s <= L+1`, where

```text
M^(s) = aoyagiReducedWidthInt H r s.
```

No nonselected inequality, rank-width hypothesis, positivity hypothesis, or
constant-width hypothesis is needed, because every source layer is selected.

## Cutpoint Checks

Define:

```text
C.cut j = j.val + 1.
```

Then:

- positivity: `1 <= j.val + 1`;
- strictness: if `j : Fin L`, then
  `j.castSucc.val + 1 < j.succ.val + 1`;
- source upper bound: for `j : Fin (L+1)`, `j.val + 1 <= L+1`.

Thus `C : AoyagiSelectedCutpoints L` and `C.cut j <= L+1`.

## Selected Strict Inequality

For `i : Fin (L+1)`, `C.cut i = i.val + 1`.  The selected sum is definitionally
the sum over all source layers:

```text
sum_j M^(C.cut j) = sum_j M^(j.val+1).
```

The supplied all-layer strict inequality at `s = i.val+1` gives

```text
L * M^(C.cut i) < sum_j M^(C.cut j).
```

This is the `selected_strict` field of `AoyagiDefinition3SourceData`.

## Nonselected Fields

Let `s` satisfy `1 <= s <= L+1`.  Set

```text
j = s - 1 : Fin (L+1).
```

Then

```text
C.cut j = (s-1)+1 = s.
```

Therefore `M^(s)` belongs to the selected value set

```text
Finset.univ.image (fun j => M^(C.cut j)).
```

So any hypothesis saying that `M^(s)` is not in the selected value set is a
contradiction.  Both the `selected_lt_nonselected` and `nonselected_le` fields
are discharged by contradiction.

## Nonclaims

- This does not prove arbitrary selected-cutpoint existence.
- This does not classify the printed Definition 3 inequalities.
- This does not supply rank-width nonnegativity or any ceiling datum by itself.
- This does not construct Eq5 payloads, prove Lemma 5 exactness, produce
  charts, identify pole order, or extract RLCT.

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict
```

It should return consecutive selected cutpoints and
`AoyagiDefinition3SourceData L L H r C`.
