# Reproduction - Definition 3 equal-width source data

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

Aoyagi's Definition 3 source data has mostly been treated as supplied, and the
recent obstruction results show that arbitrary selected-cutpoint existence is
false under the printed inequalities.  This slice asks for the narrow
equal-width case printed by Aoyagi: if all reduced source widths are equal,
can we construct the selected cutpoints and the Definition 3 source-data
fields directly?

## Source Anchors

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9.  The source
statement is the special case where

```text
M^(1) = M^(2) = ... = M^(L+1).
```

In this case Aoyagi records the choice `ell = L`.  The Lean construction
chooses every source layer as a selected cutpoint:

```text
S_1 = 1, S_2 = 2, ..., S_(L+1) = L+1.
```

This is independent of the quiver-based paper.

## Pen-and-paper Calculation

Assume a positive integer width `w` and, for every source layer
`1 <= s <= L+1`,

```text
M^(s) = w.
```

Assume also `0 < L`, since Definition 3 requires `ell > 0`.  Choose
`ell = L` and consecutive selected cutpoints

```text
S_(j+1) = j+1       for j = 0,...,L.
```

The cutpoints are strictly increasing, positive, and bounded by `L+1`.

The selected-width sum is

```text
sum_{j=0}^L M^(S_(j+1)) = (L+1)w.
```

For every selected cutpoint `i`,

```text
ell * M^(S_i) = Lw < (L+1)w,
```

because `w > 0`.  This proves Definition 3's strict selected inequality.

The nonselected clauses in the current Lean source-data structure are
value-level clauses: they apply only to a source width value not belonging to
the selected value set.  In the equal-width profile, every source-range width
is `w`, and `w` belongs to the selected value set, for instance through
`S_1=1`.  Therefore the hypotheses of both nonselected fields are
contradictory:

```text
M^(s) notin { M^(S_i) : i = 1,...,L+1 }
```

is impossible for `1 <= s <= L+1`.

Thus the consecutive cutpoints satisfy all fields of
`AoyagiDefinition3SourceData L L H r C`.

## Lean Shape

Add to `Definition3Bridge.lean`, in namespace
`AoyagiDefinition3SourceData`:

```text
AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos
```

Target statement:

```text
theorem AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos
    {L : Nat} {H : Nat -> Nat} {r w : Nat}
    (hL : 0 < L) (hw : 0 < w)
    (hconst :
      forall s : Nat, 1 <= s -> s <= L + 1 ->
        aoyagiReducedWidthInt H r s = (w : Int)) :
    exists C : AoyagiSelectedCutpoints L,
      (forall j : Fin (L + 1), C.cut j = j.val + 1) /\
        AoyagiDefinition3SourceData L L H r C
```

The theorem uses `w : Nat` to record that the common reduced width is a
positive width, while the equality is with the integer-valued reduced-width
function.

## Nonclaims

- No arbitrary selected-cutpoint existence theorem.
- No repair of Definition 3's printed inequalities.
- No classification beyond the equal-width example.
- No Eq5 construction or Lemma 5 exactness.
- No chart production, normal crossings, pole order, or RLCT extraction.
