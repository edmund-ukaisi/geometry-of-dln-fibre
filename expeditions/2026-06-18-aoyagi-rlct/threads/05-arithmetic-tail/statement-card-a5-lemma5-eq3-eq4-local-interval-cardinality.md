# Statement card - A5 Lemma 5 Eq3/Eq4 local interval cardinality

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_intervalSize`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_offsetCard_add_two`

## Claim

For one rising-region coordinate, the local Eq3-shaped upper component, local
Eq4 lower endpoint, and strict Eq5 offset set have cardinality equal to the
same-coordinate interval size.  Equivalently, in the rising region the two
local endpoints add two values to the strict Eq5 offset set.

## Proved

Lean reuses the existing source-legality-free set equality

```text
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat
```

and then applies the existing cardinality formulas for
`aoyagiHtildeIntervalValueSetNat` and `aoyagiLemma5Eq5OffsetValueSet`.

## Assumed

The local Eq3-shaped piecewise certificate, the local Eq4 piecewise
certificate, `1 <= p`, and the Eq4 rising-side guard `p <= ell-a`.  The Eq4
certificate supplies the remaining `p <= a` guard through its index guard.

## Deferred

Displayed-vector construction, source-label legality, all-coordinate branch
coverage, classifier and back-to-label coverage, Lemma 5 order count, pole
order, normal crossings, and RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```
