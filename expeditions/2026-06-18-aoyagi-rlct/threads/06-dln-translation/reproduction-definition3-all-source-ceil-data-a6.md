# Reproduction - Definition 3 all-source selected ceiling data

Status: xhigh checked; formalised.

## Source Shape

This is the downstream ceiling-data package for the all-source selected
Definition 3 constructor.

The previous all-source constructor chooses

```text
ell = L,
C.cut j = j.val + 1      for j : Fin (L+1),
```

and proves `AoyagiDefinition3SourceData L L H r C` from the strict all-source
selected inequality

```text
(L : Int) * M^(s) < sum_j M^(j.val+1)
```

for every source-range `s`, where `M^(s)=aoyagiReducedWidthInt H r s`.

To move from source data to the selected-width/ceiling package already used by
the A6 final sockets, add the explicit source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

This is exactly the hypothesis consumed by
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`.

## Derivation

Assume:

- `0 < L`;
- the strict all-source selected inequality for all source-range `s`;
- source-range rank-width, `r <= H s`, for all source-range `s`.

Apply

```text
AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict
```

to obtain a selected-cutpoint datum `C` such that

```text
C.cut j = j.val + 1
```

and

```text
S : AoyagiDefinition3SourceData L L H r C.
```

Now apply

```text
S.exists_selectedReducedWidthCeilData_of_rankWidth
```

with the same source-range rank-width hypothesis.  This produces

```text
m : Fin (L+1) -> Int,
data : AoyagiDefinition3CeilData L m,
```

together with:

```text
m = aoyagiSelectedReducedWidths H r C,
forall j, m j = ((H (C.cut j) - r : Nat) : Int),
forall j, 0 <= m j,
forall i, (L : Int) * m i < sum_j m j,
forall i, m i <= data.ceilWidth - 1,
forall i : Nat, 0 <= aoyagiSelectedWidthNat L m i.
```

The cutpoint equality can be returned unchanged.  No closed form for
`data.ceilWidth` or `data.aParam` follows from these hypotheses alone: the
general ceiling datum is obtained by Euclidean division of the selected-width
sum by `L`.

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
```

with statement:

```text
theorem exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth
    {L : Nat} {H : Nat -> Nat} {r : Nat}
    (hL : 0 < L)
    (hr : forall s : Nat, 1 <= s -> s <= L + 1 -> r <= H s)
    (hstrict :
      forall s : Nat, 1 <= s -> s <= L + 1 ->
        (L : Int) * aoyagiReducedWidthInt H r s <
          sum j : Fin (L + 1), aoyagiReducedWidthInt H r (j.val + 1)) :
    exists (C : AoyagiSelectedCutpoints L)
        (m : Fin (L + 1) -> Int)
        (data : AoyagiDefinition3CeilData L m),
      (forall j : Fin (L + 1), C.cut j = j.val + 1) /\
      AoyagiDefinition3SourceData L L H r C /\
      m = aoyagiSelectedReducedWidths H r C /\
      (forall j : Fin (L + 1), m j = ((H (C.cut j) - r : Nat) : Int)) /\
      (forall j : Fin (L + 1), 0 <= m j) /\
      (forall i : Fin (L + 1), (L : Int) * m i < sum j : Fin (L + 1), m j) /\
      (forall i : Fin (L + 1), m i <= data.ceilWidth - 1) /\
      (forall i : Nat, 0 <= aoyagiSelectedWidthNat L m i)
```

## Nonclaims

- This does not prove arbitrary selected-cutpoint existence.
- This does not classify Definition 3 source-data existence.
- This does not compute `ceilWidth` or `aParam` in closed form.
- This does not construct Eq5 payloads, prove Lemma 5 exactness, produce
  charts, identify pole order, or extract RLCT.

## Check

xhigh reviewer `Anscombe the 3rd` approved the theorem as valid and
non-redundant: it combines a produced all-source `C,S` with the existing
rank-width ceiling-data package, and it is not covered by the equal-width lane
because the all-source strict hypothesis allows nonconstant reduced-width
profiles.
