# Reproduction - Definition 3 `ell=1` source-data formula

Date: 2026-06-24.

Status: xhigh reviewed; formalised.

## Question

The landed general `ell=1` selected-pair formula theorem works for arbitrary
depth `L`, but it asks callers to resupply the ingredients already present in

```text
S : AoyagiDefinition3SourceData L 1 H r C.
```

This slice checks that `S` itself supplies the selected-value cover, cutpoint
bounds, and positivity needed by that theorem.

## Source Anchors

Aoyagi Definition 3 on PDF pp. 8-9 defines selected cutpoints and selected
value set data.  For `ell=1`, there are exactly two selected reduced widths,
say

```text
m_0 = M^(S_0),        m_1 = M^(S_1).
```

Definition 3 gives the two strict selected inequalities

```text
m_0 < m_0 + m_1,
m_1 < m_0 + m_1,
```

and the nonselected inequalities.  The already-landed theorem
`reducedWidth_mem_selectedValueSet_of_ell_eq_one` proves from these clauses
that every source-range reduced-width value lies in the selected value set.

## Pen-and-paper Derivation

Let `S : AoyagiDefinition3SourceData L 1 H r C`.

The source-range cutpoint bounds are exactly the `cut_le` field of `S`.

The selected-value cover is exactly

```text
S.reducedWidth_mem_selectedValueSet_of_ell_eq_one.
```

For positivity, use the selected strict inequalities:

```text
m_1 < m_0 + m_1    implies    0 < m_0,
m_0 < m_0 + m_1    implies    0 < m_1.
```

With source-range rank-width

```text
forall s, 1 <= s -> s <= L+1 -> r <= H(s),
```

the selected integer reduced widths are the natural subtractions

```text
m_0 = H(C.cut 0) - r,
m_1 = H(C.cut 1) - r.
```

Set

```text
u = H(C.cut 0) - r,
v = H(C.cut 1) - r.
```

The positivity above gives `0<u` and `0<v`, so the existing general selected
pair formula theorem applies and returns:

```text
ceilWidth = u+v,
aParam = 1,
theorem2OrderFormula = 1,
pairSum = u*v,
lambda = regularTerm + u*v/2.
```

## Lean Shape

Add a source-data wrapper in namespace `AoyagiDefinition3SourceData`:

```text
exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general
```

It should take only `S` and source-range rank-width, expose the natural widths
`u` and `v`, and return the same formula/provenance fields as the landed
general selected-pair package.

## Nonclaims

- No theorem infers `ell=1`; it is supplied in the type of `S`.
- No canonical selected pair is chosen.
- No branch-independent payload is asserted for arbitrary Definition 3 data.
- No source-rank/final-socket wrapper, Eq5 construction, chart production,
  normal crossings, pole order, or RLCT extraction.
