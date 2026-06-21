# Reproduction - Lemma 5 Eq3 tail upper endpoint and Eq5 coverage

Date: 2026-06-21.

Scope: one-coordinate component-value endpoint realisation for the ordinary
Eq3 tail region, followed by finite Eq5 non-rising interval coverage.  This
does not construct
Aoyagi's displayed vectors, prove source-label legality, terminal `tilde t=0`,
chart coverage, all-coordinate branch-family coverage, pole order, normal
crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF p. 27, equation `(3)` has a special boundary value

```text
T(S_(ell-a+2)-1) = Htilde'_(ell-a+1)+1,
```

and after that boundary it returns to the upper-chain value on ordinary
selected blocks:

```text
T(S) = Htilde'_j
```

for the corresponding later block.  In Lean's zero-based selected-cutpoint
notation, the special boundary is `C.point (ell-a+1)-1`.

## Tail Component Value

Fix a coordinate `p` satisfying

```text
ell-a+1 < p < ell.
```

Then the selected-block left endpoint for coordinate `p` lies in block `p`:

```text
C.block p (C.point p - 1).
```

Since `ell-a+1 < p`, strict monotonicity of selected cutpoints gives

```text
C.point (ell-a+1) < C.point p,
```

hence

```text
C.point (ell-a+1)-1 < C.point p - 1.
```

Therefore the Eq3 tail clause, not the special boundary clause, applies to
this component and gives the upper endpoint value

```text
T3(C.point p - 1) = Htilde'_p.
```

This is only a component-value consequence of the supplied Eq3 piecewise
certificate.  It is not a theorem that this component is the vector's own
source label, and it is not a source-label legality theorem for
`Htilde'_p+1`.

## Eq5 Non-Rising Coverage

The same inequality `ell-a+1 < p` implies `not (p<=ell-a)`, so the coordinate
is outside the rising region `p<=a and p<=ell-a`.  For positive `p`, the
previous endpoint-deficit arithmetic gives

```text
aoyagiLemma5IntervalExcess ell a p <= p-1.
```

Thus the Eq5 strict offset set is the same-coordinate interval with only the
upper endpoint erased.  Inserting the Eq3 tail upper endpoint fills the
interval:

```text
insert (T3(C.point p - 1)) Eq5Offsets_p
  = IntervalValueSet_p.
```

## Lean Targets

```text
aoyagiLemma5Eq3_piecewise_tail_upperEndpoint_of_boundary_lt
aoyagiLemma5_suppliedEq3TailUpper_Eq5_offsets_eq_intervalValueSetNat_of_boundary_lt
```

## Kill Conditions

- Keep the Eq3 piecewise certificate supplied.
- Keep the ordinary-tail guards `ell-a+1 < p` and `p < ell` explicit.
- Do not apply this theorem at the special boundary `p=ell-a+1`.
- Do not apply this theorem at the terminal endpoint `p=ell`.
- Do not infer own-source-label status, source-label legality,
  introduced-label status, terminality, all-coordinate coverage,
  branch-family coverage, Lemma 5 order count, normal crossings, or RLCT
  extraction.
