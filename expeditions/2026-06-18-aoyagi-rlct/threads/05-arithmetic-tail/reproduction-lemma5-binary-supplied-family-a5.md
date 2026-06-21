# Reproduction - binary supplied family admissibility

Date: 2026-06-21.

Scope: conditional finite assembly inside the Aoyagi-only expedition.  This
does not construct Aoyagi's displayed source vectors, prove that source
vectors have binary prefix deltas, prove the Lemma 5 upper-bound classifier,
prove pole order, normal crossings, or perform RLCT extraction.

## Existing supplied boundary

`AoyagiLemma5SuppliedAdmissibleNonbaseFamily` extends the supplied nonbase
branch-value count with four per-branch `H`-chain obligations:

```text
H_0 = m_0,
Htilde <= H <= Htilde',
F_r in {M-1,M},
value = H_j at the counted coordinate.
```

The full admissible family adds the same kind of data for the base branch.

The previous binary-prefix slice proved that the two middle obligations can be
derived from a smaller finite interface:

```text
H_0 = m_0,
H_ell = 0,
Delta_r = D_(r+1)-D_r in {0,1},
sum selected widths = ell*(M-1)+a,
a <= ell.
```

Here

```text
D_j = P(j) - H_j - j*(M-1).
```

## Derivation

For one supplied branch `b`, assume:

```text
H_b(0) = m_0,
H_b(ell) = 0,
Delta_b(r) in {0,1} for every r : Fin ell.
```

Together with the selected-width sum, the endpoint lemmas give

```text
D_b(0) = 0,
D_b(ell) = a.
```

The binary-prefix theorem gives the prefix bounds

```text
min(a, j-(ell-a)) <= D_b(j) <= min(j,a)
```

for every `j`.  Feeding these bounds into the previously proved translation
from prefix-delta bounds to chain bounds gives

```text
Htilde <= H_b <= Htilde'.
```

The increment identity

```text
F_r = (M-1) + Delta_r
```

then turns `Delta_r in {0,1}` into

```text
F_r in {M-1,M}.
```

Thus a supplied nonbase family with `H_0`, terminal `H_ell=0`, binary deltas,
and the existing coordinate-value equality can be converted into an
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily`.

The base branch is identical: supplied `baseH_0=m_0`, `baseH_ell=0`, and
binary deltas imply the base `Htilde` bounds and base two-value increment
field, so the same conversion produces an `AoyagiLemma5SuppliedAdmissibleFamily`.

## Formalisation plan

Add two narrower supplied structures:

```text
AoyagiLemma5SuppliedBinaryNonbaseFamily
AoyagiLemma5SuppliedBinaryFamily
```

and conversion theorems:

```text
AoyagiLemma5SuppliedBinaryNonbaseFamily.toAdmissibleNonbaseFamily
AoyagiLemma5SuppliedBinaryFamily.toAdmissibleFamily
```

The structures should still extend the existing supplied value-family
boundary.  They only reduce the per-branch admissibility obligations from
explicit `Htilde` bounds and two-value increments to terminal binary
prefix-delta data.  They must not be described as source-backed construction
of Aoyagi's displayed branch family.
