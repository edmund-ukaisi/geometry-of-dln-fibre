# Statement card - A5 Lemma 5 Printed Increment Obstructions

## Lean Names

```text
aoyagiLemma5Eq3_specialNextIncrement_eq_succ
aoyagiLemma5Eq3_specialNextIncrement_not_twoValue
aoyagiLemma5Eq4_specialIncrement_eq_selectedWidth_sub_one
aoyagiLemma5Eq4_specialIncrement_lt_pred_of_sourceSelected
aoyagiLemma5Eq4_specialIncrement_not_twoValue_of_sourceSelected
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

## Claims

Equation `(3)`: if `a>=2`, and supplied adjacent chain values set

```text
H_(ell-a+1) = Htilde'_(ell-a+1)+1
H_(ell-a+2) = Htilde'_(ell-a+2),
```

then the next Lemma 4 increment is `M+1`, hence neither `M-1` nor `M`.

Equation `(4)`: if supplied adjacent chain values set

```text
H_(p+ell-a)   = Htilde'_(p+ell-a)-p
H_(p+ell-a+1) = Htilde'_(p+ell-a)-p+1,
```

then the corresponding Lemma 4 increment is the next selected width minus
one.  Under Definition 3's strict selected-width inequalities, this is
strictly below `M-1`, hence neither `M-1` nor `M`.

## Inputs

- Supplied adjacent `H`-chain values matching the printed special branches.
- For Eq `(4)`'s strict-below theorem: Definition 3's selected-width sum and
  strict selected-width inequality.

## Boundaries

- No construction of the printed displayed vectors.
- No source-label legality theorem.
- No chart-production theorem.
- No all-branch Lemma 5 order-count theorem.
- No normal-crossing or RLCT extraction theorem.

## Source

Aoyagi Lemma 5 equations `(3)` and `(4)`, PDF p. 27, and Lemma 4's two-value
increment requirement, PDF p. 25.
