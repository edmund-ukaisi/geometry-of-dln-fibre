# Reproduction - Definition 3 ell=1 nonselected obstruction

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The example `1,2,100` showed that Aoyagi Definition 3 cannot be promoted to
arbitrary selected-cutpoint existence under the printed inequalities.  The
`ell=1` branch of that example has a general form:

```text
ell = 1
```

selects two cutpoints.  If any source-range reduced width has a value not in
the selected value set, the printed nonselected inequality has coefficient
`ell-1=0`, and this is incompatible with nonnegative selected reduced widths
and the strict selected inequality.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, defines reduced widths

```text
M^(s) = H^(s) - r,        s = 1,...,L+1,
```

selects cutpoints `S_j`, `j=1,...,ell+1`, and applies:

```text
sum_j M^(S_j) > ell * M^(S_i)
```

for selected indices, and

```text
sum_j M^(S_j) <= (ell-1) * M^(s)
```

for source-range widths whose value is not in the selected value set.  Lean
records these as value-level fields of `AoyagiDefinition3SourceData`.  The
argument below uses only these two displayed inequalities.  Definition 3 also
has the nonselected lower comparison saying selected values are below genuinely
nonselected values, but that comparison is not needed for this obstruction.

## Pen-and-paper Calculation

Assume source data

```text
S : AoyagiDefinition3SourceData L 1 H r C
```

and a source-range rank-width hypothesis

```text
hr : forall s, 1 <= s -> s <= L+1 -> r <= H(s).
```

Let

```text
m_i = H(C_i) - r,       i = 0,1
T   = m_0 + m_1.
```

Because each selected cutpoint lies in the source range and `hr` holds there,
both selected reduced widths are nonnegative:

```text
0 <= m_0,      0 <= m_1.
```

Now suppose there is a source index `s` with

```text
1 <= s <= L+1
```

whose reduced-width value is not in the selected value set:

```text
H(s)-r notin {m_0,m_1}.
```

Definition 3's nonselected upper inequality gives

```text
T <= (1-1) * (H(s)-r) = 0.
```

On the other hand, nonnegativity gives

```text
0 <= T.
```

So `T = 0`.  The strict selected inequality for either selected index, say
`i=0`, is

```text
1 * m_0 < T = 0.
```

This contradicts `0 <= m_0`.

Thus, under the source-range rank-width hypothesis, `ell=1` source data has no
genuinely nonselected reduced-width value.  Equivalently, every source-range
reduced-width value must belong to the selected value set if
`AoyagiDefinition3SourceData L 1 H r C` holds.

## Lean Shape

Add to `Definition3Bridge.lean`, under `AoyagiDefinition3SourceData`:

```text
theorem no_nonselected_value_of_ell_eq_one_rankWidth
```

or the positive membership form:

```text
theorem reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth
```

The positive form should consume:

```text
S : AoyagiDefinition3SourceData L 1 H r C
hr : forall s, 1 <= s -> s <= L+1 -> r <= H s
hs1 : 1 <= s
hsL : s <= L+1
```

and prove:

```text
aoyagiReducedWidthInt H r s ∈
  Finset.univ.image
    (fun j : Fin (1+1) => aoyagiReducedWidthInt H r (C.cut j)).
```

The contradiction proof is more convenient in Lean:

1. Assume nonmembership.
2. Use `S.nonselected_le s hs1 hsL hnot` to get the selected sum `<= 0`.
3. Use rank-width nonnegativity at the two selected cutpoints to get the
   selected sum `>= 0`.
4. Conclude the selected sum is `0`.
5. Use `S.selected_strict 0` and selected nonnegativity to contradict
   `m_0 < 0`.

## Nonclaims

- No selected-cutpoint construction.
- No classification for `ell > 1`.
- No correction of Aoyagi's printed Definition 3.
- No claim that the theorem applies when reduced widths can be negative.
- No Lemma 5 exactness, Eq5 endpoint-family construction, active-ratio bound,
  chart production, normal crossings, pole order, or RLCT.
