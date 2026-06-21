# Reproduction - Lemma 5 Full Supplied Family Free-Count Minimum

Status: supplied-data boundary; ready for a narrow Lean wrapper.

This note records the finite arithmetic bridge from the full supplied Lemma 5
branch family to Aoyagi Lemma 3's isolated numerator minimum.

## Setup

Write the total number of Lemma 4 increments as `n+1`.  For a tagged supplied
branch `x in fullBranches`, let

```text
v_r = F_r(fullH x),    r = 1,...,n+1.
```

In Lean this is

```text
v : Fin (n+1) -> Z,
v r = aoyagiLemma4F (n+1) m (fullH x) r.
```

The free Lemma 3 parameter counts only the first `n` increments:

```text
b = #{j : Fin n | v(j.castSucc)=M}.
```

The final increment `v(Fin.last n)` is not part of this free count.

## Count Split

The already-proved full supplied branch theorem gives the total high count

```text
#{r : Fin (n+1) | v_r=M} = a.
```

The elementary split is

```text
#{j : Fin n | v(j.castSucc)=M}
  + indicator(v(Fin.last n)=M)
= #{r : Fin (n+1) | v_r=M}.
```

Therefore the free count `b` is either

```text
b = a
```

or

```text
b = a-1.
```

The two endpoint cases are included in this disjunction: if `a=0`, the final
indicator cannot force a negative natural count; if `a=n+1`, the free count is
`n` exactly when the last increment is high.

## Lemma 3 Numerator

Aoyagi Lemma 3's isolated numerator is

```text
A(ell,a,b)
  = b(ell-a)^2 + (ell-1-b)a^2
      + (b(ell-a) - (ell-1-b)a)^2.
```

The existing Lean theorem proves, for `ell != 0`,

```text
A(ell,a,b) = a*ell*(ell-a)
  iff b=a or b=a-1.
```

Here `ell=n+1`, so `ell != 0`.  Combining this equality-case theorem with the
free-count split gives

```text
A(n+1,a,b) = a*(n+1)*((n+1)-a).
```

## Lean Targets

```text
AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCount_lemma3A_eq_min
```

## Kill Conditions

- Do not identify this numerator with Aoyagi's terminal exponent expression.
- Do not replace terminal `tilde t=0` by `H_ell=0`.
- Do not infer source labels, displayed vectors, chart coverage, pole order,
  normal crossings, or RLCT extraction from this finite count.

## Nonclaims

- No branch family is constructed from equations `(3)`, `(4)`, or `(5)`.
- No source-label legality or terminal vector condition is proved.
- No `lambda` or pole-order theorem is proved.
