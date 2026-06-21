# Reproduction - Lemma 5 Terminal Minimum Numerator Bridge

Status: supplied-data boundary; ready for a narrow Lean wrapper.

This note records the finite bridge from a supplied terminal-exponent
certificate to the Lemma 3 minimum numerator for a supplied Lemma 5 branch.

## Source Position

Aoyagi's terminal candidate expression on PDF p. 22 is restricted to variables
with

```text
tilde t_{s,k}=0.
```

The quadratic calculation on PDF pp. 22-24 rewrites the terminal exponent
`M_{s,k}` through a free count `b` among the first `ell-1` increments.  The
previous Lean slice proved only that a supplied Lemma 5 branch has the Lemma 3
minimum value for this free count.  It did not prove that this free-count
numerator is the same as a source terminal exponent.

Therefore the next honest bridge keeps that identification supplied.

## Setup

Let total increment length be `ell = n+1`.  For a tagged branch
`x in fullBranches`, define

```text
b_x = #{j : Fin n | F_j(fullH x)=M}.
```

Lean names this count as

```text
aoyagiLemma4FreeHighCount n M m (F.fullH x).
```

The full supplied-family theorem gives

```text
A(n+1,a,b_x) = a*(n+1)*((n+1)-a).
```

Now suppose we also have a generic introduced-label exponent certificate

```text
certs : IntroducedLabelExponentCertificates L width S J t numerator leastValue
```

and a source label `(s,k)` introduced at state `(S,J)`.  The certificate gives

```text
terminalExponent L (widthZ width) (t s k) = numerator s k.
```

The supplied terminal-exponent normalisation is

```text
numerator s k = A(n+1,a,b_x).
```

Combining the three displayed equalities gives

```text
terminalExponent L (widthZ width) (t s k)
  = a*(n+1)*((n+1)-a).
```

## Lean Targets

```text
aoyagiLemma4FreeHighCount
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin
IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator
```

## Kill Conditions

- Do not derive `numerator s k = A(n+1,a,b_x)` from the PDF unless the
  terminal-exponent quadratic rewrite has been independently reproduced.
- Do not treat `H_ell=0` as terminal `tilde t_{s,k}=0`.
- Do not infer source labels, displayed-vector construction, chart coverage,
  pole order, normal crossings, or RLCT extraction.

## Nonclaims

- No source-backed terminal branch is constructed.
- No `lambda` equality is proved.
- No pole-order or RLCT statement is proved.
