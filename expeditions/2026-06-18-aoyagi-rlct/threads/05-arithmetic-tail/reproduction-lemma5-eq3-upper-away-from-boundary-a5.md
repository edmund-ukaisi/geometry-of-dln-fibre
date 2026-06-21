# Reproduction - Lemma 5 Eq3 upper component away from the special boundary

Date: 2026-06-21.

Scope: one-coordinate Eq3 component-value inventory, followed by Eq5
non-rising coverage away from Eq3's special boundary and terminal endpoint.
This does not construct Aoyagi's displayed vectors, prove source-label
legality, terminal `tilde t=0`, chart coverage, all-coordinate branch-family
coverage, pole order, normal crossings, or RLCT extraction.

## Source Inventory

Aoyagi Lemma 5, PDF pp. 26-27, displays several piecewise vectors.  For the
upper endpoint `Htilde'_p`, the source-facing status is:

| Display | Printed/component region | Component value at selected-block left endpoint `C.point p-1` | Status |
| --- | --- | --- | --- |
| Eq3 upper clause | `1 <= p <= ell-a` | `Htilde'_p` | Component value supplied by `AoyagiLemma5Eq3PiecewiseSourceVector.upper`. |
| Eq3 special boundary | `p = ell-a+1` | `Htilde'_(ell-a+1)+1` | Not the same-coordinate upper endpoint; already recorded as an obstruction. |
| Eq3 tail clause | `ell-a+1 < p < ell` | `Htilde'_p` | Component value supplied by `AoyagiLemma5Eq3PiecewiseSourceVector.tail`. |
| Terminal endpoint | `p = ell` | outside half-open selected blocks | Not covered by this component theorem. |

This inventory is about component values of the supplied Eq3-shaped piecewise
certificate.  It is not a source-label legality or back-to-label coverage
statement.

## Component Case Split

Assume

```text
1 <= p,    p < ell,    p != ell-a+1.
```

There are two cases.

If `p <= ell-a`, the existing Eq3 upper-component theorem applies directly:

```text
T3(C.point p - 1) = Htilde'_p.
```

If not `p <= ell-a`, then `ell-a < p`.  Since `p != ell-a+1`, arithmetic gives

```text
ell-a+1 < p.
```

Together with `p < ell`, the existing Eq3 tail theorem applies and again gives

```text
T3(C.point p - 1) = Htilde'_p.
```

Thus away from the special boundary and terminal endpoint, the supplied Eq3
piecewise certificate gives the upper endpoint as a component value.

## Eq5 Non-Rising Coverage

Add the non-rising hypothesis

```text
not (p <= a and p <= ell-a).
```

Then the endpoint-deficit arithmetic gives

```text
aoyagiLemma5IntervalExcess ell a p <= p-1.
```

So the strict Eq5 offset set is the same-coordinate interval with only the
upper endpoint erased.  Inserting the Eq3 component value fills the interval:

```text
insert (T3(C.point p - 1)) Eq5Offsets_p
  = IntervalValueSet_p.
```

## Lean Targets

```text
aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_ne_boundary
aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_nonrising_ne_boundary
```

## Kill Conditions

- Keep the Eq3 piecewise certificate supplied.
- Keep `p != ell-a+1` and `p < ell` explicit.
- Keep non-rising explicit for the Eq5 coverage theorem.
- Do not apply this theorem at the special boundary `p=ell-a+1`.
- Do not apply this theorem at the terminal endpoint `p=ell`.
- Do not infer own-source-label status, source-label legality,
  introduced-label status, all-coordinate endpoint realisation, injection,
  back-to-label coverage, Lemma 5 order count, normal crossings, or RLCT
  extraction.
