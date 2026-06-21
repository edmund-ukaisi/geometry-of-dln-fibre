# Reproduction - Lemma 5 Supplied Chart-Family Count Boundary

Status: supplied-data boundary; ready for a narrow Lean count theorem.

This note records the honest aggregate theorem available after the printed
equation obstruction checkpoint.  The theorem is not a reconstruction of
Aoyagi's displayed equations `(3)`, `(4)`, and `(5)`.  It says that if the
missing chart-family realisation is supplied as finite branch data with
explicit admissibility and coverage fields, then the already-proved interval
arithmetic gives the count `a(ell-a)+1`.

## Source Boundary

Aoyagi Lemma 5, PDF pp. 25-27, proves the interval-size arithmetic

```text
1 + sum_{j=1}^{ell-1} (|{H : Htilde_j <= H <= Htilde'_j}| - 1)
  = a(ell-a)+1.
```

The text then says that the displayed vectors `T_{s,k}` in equations `(3)` and
`(4)` construct the Case 1(2) blow-up process.  The preceding obstruction note
shows that the printed equations cannot be used as complete Lemma 4 witnesses
as written.  Therefore the next Lean theorem must keep the chart-family
realisation supplied.

## Supplied Family Model

For each interior coordinate

```text
j in {1,...,ell-1},
```

the supplied data should include a finite set of nonbase branches `B_j`, a
same-coordinate value map

```text
value : B_j -> Z,
```

and a supplied base value `base_j` in the interval

```text
I_j = {H : Htilde_j <= H <= Htilde'_j}.
```

The coverage field is:

```text
value(B_j) = I_j \ {base_j},
```

with `value` injective on `B_j`.  This is the exact nonduplication/coverage
boundary at one coordinate.  For a literal branch-union count, the supplied
data must also say that the finite branch sets for distinct interior
coordinates are disjoint.  These fields are stronger than the PDF sentence and
must not be treated as proved from equations `(3)`, `(4)`, and `(5)`.

The admissible extension of the same supplied data should also carry, for each
branch, the Lemma 4 witness obligations:

```text
H_0 = M(S_1),
Htilde <= H <= Htilde',
H_{r-1} - H_r + M(S_{r+1}) is M-1 or M for every r,
value(branch) = H_j at the counted coordinate.
```

These are exactly the obligations identified in the source chart-family gap.
The aggregate count theorem below only needs coverage and injectivity; the
admissibility fields are included so the supplied object is not confused with
a bare cardinality assumption.

## Pen-And-Paper Count

Fix `j` in `{1,...,ell-1}`.  By supplied coverage and injectivity,

```text
|B_j| = |value(B_j)|
      = |I_j \ {base_j}|.
```

Since `base_j` is supplied as an element of `I_j`,

```text
|I_j \ {base_j}| = |I_j| - 1.
```

Therefore

```text
1 + sum_j |B_j|
  = 1 + sum_j (|I_j|-1).
```

The existing interval-value-set theorem proves the right-hand side is

```text
a(ell-a)+1.
```

Thus the supplied branch family has the desired aggregate count.

If the branch sets for distinct `j` are also supplied disjoint, the same
calculation counts the finite union:

```text
1 + |union_j B_j| = a(ell-a)+1.
```

## Lean Targets

Planned Lean names:

```text
AoyagiLemma5SuppliedNonbaseFamily
AoyagiLemma5SuppliedAdmissibleNonbaseFamily
aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one
aoyagiLemma5SuppliedNonbaseFamily_count
aoyagiLemma5SuppliedNonbaseFamily_biUnion_count
AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_twoValueCount
```

## Kill Conditions

- Do not infer the supplied coverage field from Aoyagi's printed equations.
- Do not call this a source-backed Lemma 5 order-count theorem.
- Do not omit the base-value membership field; without it the `-1` is not
  justified.
- Do not omit injectivity or replace it by cardinality equality unless a later
  theorem proves nonduplication separately.
- Do not count a union of branches unless cross-coordinate disjointness is
  supplied.
- Do not use the theorem as a normal-crossing or RLCT result.

## Nonclaims

- No displayed vector is constructed.
- No source-label legality is proved.
- No Case 1(2) chart sequence is reconstructed.
- No terminal `tilde t=0`, pole-order interpretation, normal-crossing
  resolution, or RLCT extraction is proved.
