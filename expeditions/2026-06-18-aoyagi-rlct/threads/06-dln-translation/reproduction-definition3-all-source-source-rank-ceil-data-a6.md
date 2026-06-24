# Reproduction - Definition 3 all-source source-rank ceiling data

Status: xhigh checked; formalised.

## Source Shape

This is the A2/A6 version of the all-source selected ceiling-data package.  It
replaces the explicit source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= N+1 -> r <= H s
```

by the existing source-rank-stratum bridge:

```text
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

together with Aoyagi's dimension convention

```text
H(k.val + 1) = finrank K (W k).
```

No quiver input is involved.  The rank-width bound comes from elementary
linear algebra already formalised in `Definition3RankWidthBridge.lean`: the
total product rank is bounded by every layer dimension.

## Derivation

Assume:

- `0 < N`;
- strict all-source selected inequalities for every source-range `s`:

  ```text
  (N : Int) * aoyagiReducedWidthInt H r s
    < sum_j aoyagiReducedWidthInt H r (j.val+1);
  ```

- source-rank-stratum membership `hx`;
- the displayed width convention `hH`.

First apply the all-source source-data constructor:

```text
AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict
```

to obtain consecutive cutpoints `C` and

```text
S : AoyagiDefinition3SourceData N N H r C.
```

The existing source-rank bridge gives source-range rank-width:

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth W B hx hH
```

or equivalently the already packaged theorem

```text
S.exists_selectedReducedWidthCeilData_of_sourceRankStratum W B hx hH.
```

Applying that package produces:

```text
m : Fin (N+1) -> Int,
data : AoyagiDefinition3CeilData N m,
```

with the usual selected reduced-width identity, Nat-width rewrites,
nonnegativity, strict selected inequalities, selected upper bounds, and Nat
selected-width nonnegativity.

## Lean Target

Add to `lean/DLNFibre/DLN/Aoyagi/Definition3RankWidthBridge.lean`:

```text
AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum
```

under the existing `RankWidth` section variables.  The intended statement is:

```text
theorem exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum
    {alpha : Type*}
    {Cedge : alpha -> forall p : Fin N,
      reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ}
    {r : Nat} {rEdge : Fin N -> Nat} {x : alpha}
    {H : Nat -> Nat}
    (hN : 0 < N)
    (hstrict :
      forall s : Nat, 1 <= s -> s <= N + 1 ->
        (N : Int) * aoyagiReducedWidthInt H r s <
          sum j : Fin (N + 1), aoyagiReducedWidthInt H r (j.val + 1))
    (hx : x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge)
    (hH : forall k : Fin (N + 1),
      H (k.val + 1) = Module.finrank K (W k)) :
    exists (C : AoyagiSelectedCutpoints N)
        (m : Fin (N + 1) -> Int)
        (data : AoyagiDefinition3CeilData N m),
      (forall j : Fin (N + 1), C.cut j = j.val + 1) /\
      AoyagiDefinition3SourceData N N H r C /\
      m = aoyagiSelectedReducedWidths H r C /\
      (forall j : Fin (N + 1), m j = ((H (C.cut j) - r : Nat) : Int)) /\
      (forall j : Fin (N + 1), 0 <= m j) /\
      (forall i : Fin (N + 1), (N : Int) * m i < sum j : Fin (N + 1), m j) /\
      (forall i : Fin (N + 1), m i <= data.ceilWidth - 1) /\
      (forall i : Nat, 0 <= aoyagiSelectedWidthNat N m i)
```

The proof should compose the all-source constructor with
`S.exists_selectedReducedWidthCeilData_of_sourceRankStratum W B hx hH`.

## Nonclaims

- This does not construct source-rank-stratum membership.
- This does not prove exact-rank openness or chart coverage.
- This does not prove arbitrary selected-cutpoint existence or classify
  Definition 3.
- This does not compute `ceilWidth` or `aParam`.
- This does not construct Eq5 payloads, prove finite exponent formulas,
  produce normal-crossing charts, identify pole order, or extract RLCT.

## Check

xhigh reviewer `Popper the 3rd` approved the theorem as mathematically valid,
with the warning that it is only an API wrapper.  We formalise exactly this
one source-rank version because it removes the repeated explicit rank-width
hypothesis for the all-source lane; do not clone it into final-socket variants
without a concrete downstream consumer.
