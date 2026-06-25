# Reproduction - Definition 3 exact ceiling data

Date: 2026-06-25.

Status: controller pen-and-paper reproduction before Lean.  This is finite
integer arithmetic for the supplied selected-width formula layer.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, chooses selected widths

```text
M^(S_1), ..., M^(S_(ell+1))
```

and then chooses the integer denoted `M` in the paper by

```text
M - 1 < (sum selected widths) / ell <= M.
```

It defines

```text
a = sum selected widths - (M - 1) ell.
```

Lean calls the paper's ceiling integer `ceilWidth`, and the source residue
`aParam`.

## Pen-And-Paper Check

Let

```text
T = sum_{j=0}^{ell} m_j,
e = ell,
```

with `0 < e`.  To avoid a separate zero-remainder case, divide `T - 1` by
`e`:

```text
T - 1 = rho + e q,       0 <= rho < e.
```

Set

```text
ceilWidth = q + 1,
a = rho + 1.
```

Since `0 <= rho < e`, we have

```text
1 <= a <= e.
```

Also

```text
T = (T - 1) + 1 = rho + e q + 1 = e(ceilWidth - 1) + a.
```

Finally, this `ceilWidth` is the usual ceiling expression used by Definition
3.  Because

```text
T + e - 1 = rho + e(q + 1),
```

with `0 <= rho < e`, Euclidean uniqueness gives

```text
(T + e - 1) / e = q + 1 = ceilWidth.
```

Thus the exact data attached to the selected family is

```text
ceilWidth = (T + ell - 1) / ell,
aParam    = ((T - 1) % ell + 1).toNat.
```

## Lean Target

Add a constructor in `FinalFormula.lean`:

```text
AoyagiDefinition3CeilData.ofSelectedSumCeil
```

It should take

```text
ell : Nat,
m : Fin (ell+1) -> Int,
hell : 0 < ell
```

and return `AoyagiDefinition3CeilData ell m` with the exact `ceilWidth` and
positive residue above.

The older existential theorem

```text
AoyagiDefinition3CeilData.nonempty_of_ell_pos
```

can then be proved by packaging this exact constructor.

## Nonclaims

- No selected-cutpoint construction.
- No branch-selection rule.
- No correction of Aoyagi's printed inactive inequality.
- No rank-width conversion for `H^(s)-r`; this theorem starts from an
  already supplied integer selected-width family.
- No normal-crossing, pole-order, RLCT, or Core/quiver codimension statement.

