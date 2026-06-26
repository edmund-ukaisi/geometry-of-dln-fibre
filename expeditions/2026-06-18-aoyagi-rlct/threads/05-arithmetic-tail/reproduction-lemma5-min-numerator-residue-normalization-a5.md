# Reproduction - Lemma 5 minimum numerator residue normalization

Date: 2026-06-26.

Status: finite rational arithmetic; ready for a narrow Lean theorem.

## Source Position

Aoyagi Theorem 2, PDF pp. 8-9, displays the finite lambda formula with the
residue term

```text
a(ell-a)/(4 ell)
```

beside the selected-width average and pair-sum terms.  The Lemma 3/Lemma 5
arithmetic reproduced earlier in this thread isolates the minimum numerator

```text
a ell (ell-a)
```

for the terminal branch calculation, with total selected increment length
`ell = n+1`.  The normal-crossing ratio uses this numerator with denominator
`4 ell^2`.  This note checks only the elementary normalization from the
Lemma 5 numerator to the Theorem 2 residue term.

## Calculation

Let

```text
ell = n+1.
```

Then `ell` is nonzero.  Lean defines

```text
aoyagiLemma5MinNumerator n a = a * ell * (ell - a)
```

as an integer.  Casting to rationals and dividing by the normalizing denominator
gives

```text
(a ell (ell-a))/(4 ell^2)
  = a(ell-a)/(4 ell),
```

because one factor of `ell` cancels and `ell != 0`.

No inequality on `a` is needed for this algebraic identity.  In the source
application, Definition 3 supplies `0 < a <= ell`, but the cancellation itself
is valid for every natural `a`.

## Lean Target

```text
aoyagiLemma5MinNumerator_div_four_sq_eq_theorem2ResidueTerm
```

in

```text
lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean
```

## Proved / Assumed / Cited / Deferred

Proved: the rational identity

```text
((aoyagiLemma5MinNumerator n a : Q) / (4 * (n+1)^2))
  = a * ((n+1)-a) / (4 * (n+1)).
```

Assumed: none beyond `n a : Nat`; `n+1 != 0` is proved internally.

Cited: none.  This is finite arithmetic over existing source-facing
definitions.

Deferred: identification of source terminal exponents with
`aoyagiLemma5MinNumerator`, source-backed active-ratio minimality, chart-count
or terminal-label exactness, pole order, normal crossings, and RLCT extraction.

## Kill Conditions

- If the source terminal ratio is not normalized by `4 ell^2`, this theorem is
  still true but is not the needed source application.
- If a later theorem uses this identity to infer active-ratio minimality or
  pole order without the separate A0/A5 hypotheses, the downstream theorem is
  overclaiming.
- If the Lean statement adds `a <= n+1` as a hypothesis, it is not wrong, but it
  obscures that the normalization is pure cancellation rather than a bounded
  residue fact.

## Nonclaims

This is not Aoyagi Lemma 5, not a classifier or no-extra coverage theorem, not
a normal-crossing certificate, not a pole-order theorem, and not an RLCT
statement.
