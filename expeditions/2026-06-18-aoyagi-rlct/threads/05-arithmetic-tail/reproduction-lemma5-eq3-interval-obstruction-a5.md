# Pen-and-paper reproduction - Lemma 5 equation (3) interval obstruction

Status: checked finite interval bookkeeping.

This note records a finite consequence of Aoyagi Lemma 5 equation `(3)`: the
special boundary value is one unit above the same-coordinate interval already
counted between the two displayed `Htilde` chains.

## Source

Aoyagi PDF p. 27, equation `(3)`, assigns the special boundary

```text
S_(ell-a+2)-1
```

the value

```text
Htilde'_(ell-a+1)+1.
```

In Lean's zero-based selected-cutpoint notation this is

```text
T(C.point (ell-a+1)-1) = Htilde'_(ell-a+1)+1.
```

## Same-Coordinate Interval

The already-formalised same-coordinate interval at coordinate `j` is the set
of integer values

```text
Htilde_j <= H <= Htilde'_j.
```

Thus at

```text
j = ell-a+1,
```

the displayed equation `(3)` boundary value satisfies

```text
T(C.point j - 1) = Htilde'_j + 1 > Htilde'_j.
```

It therefore cannot lie in the same-coordinate interval value set at
coordinate `j`.

## Strict Boundary Case

The previous boundary split proves that when `2<=a`, the same special
boundary lies in the half-open selected span as the left endpoint of selected
block `ell-a+1`.  The new obstruction says that even in this strict selected
span case, the boundary singleton is not counted by the same-coordinate
interval family.

## Lean Targets

```text
aoyagiLemma5Eq3_boundaryValue_gt_upperNat
aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat
aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le
```

## Nonclaims

- This does not construct equation `(3)`'s displayed vector.
- This does not prove terminal `tilde t=0`.
- This does not prove introduced-label status, a Case 1(2) chart sequence,
  vector admissibility, Lemma 5 order count, normal crossings, or RLCT
  extraction.
- This does not disprove Aoyagi's Lemma 5.  It records that the special
  singleton is outside the same-coordinate interval count.
