# Pen-and-paper reproduction - Lemma 4 same-coordinate binary-delta free count

Status: checked conditional finite bridge.

This note combines existing A5 arithmetic interfaces.  It does not prove
Aoyagi's source map from a vector `T` to the sequence `(H_j),(S_j)`, does not
prove that source vectors have binary prefix deltas, and does not prove Lemma
5's chart-family/order-count construction.

## Inputs

Use zero-based Lean indexing with

```text
m : Fin(n+2) -> Z,
H : Fin(n+2) -> Z,
F_j = H_j - H_(j+1) + m_(j+1),          j : Fin(n+1).
```

Let `ell=n+1`.  The selected-width sum is

```text
sum_i m_i = ell*(M-1)+a.
```

Assume the source range bound

```text
a <= ell.
```

The source convention is

```text
H_0 = m_0.
```

Assume a supplied same-coordinate map

```text
coord : Fin(n+2) -> iota
```

relating componentwise vector bounds to the chain:

```text
Tlo(coord j) = Htilde_j,
T(coord j)   = H_j,
Thi(coord j) = Htilde'_j,
Tlo <= T <= Thi.
```

Also assume the named prefix deltas are binary:

```text
Delta_j = D_(j+1)-D_j in {0,1},
```

where

```text
D_j = P(j)-H_j-j*(M-1).
```

## Derivation

The same-coordinate hypotheses give the chain bounds entrywise:

```text
Htilde_j <= H_j <= Htilde'_j.
```

The already-proved `Htilde` endpoint calculation then gives

```text
H_ell = 0.
```

The named prefix-delta identity gives

```text
F_j = (M-1)+Delta_j.
```

Since `Delta_j` is `0` or `1`,

```text
F_j in {M-1,M}.
```

Now the existing Lemma 4 count bridge applies.  Exactly `a` of the `ell`
increments are high.  Therefore the high count among the first `n=ell-1`
free positions is either `a` or `a-1`, depending on the last increment.  By
the endpoint-corrected Lemma 3 equality cases, that free count attains the
isolated Lemma 3 lower-bound numerator:

```text
A(b) = a*ell*(ell-a).
```

## Lean target

Add:

```text
aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta
aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min
```

The first theorem is only the named-delta version of the existing binary
bridge.  The second theorem packages same-coordinate vector bounds and binary
deltas into the existing free-count Lemma 3 bridge.

## Kill conditions

- Keep `coord` supplied; do not claim Aoyagi's `T -> (H_j),(S_j)`
  correspondence.
- Keep binary prefix deltas supplied; do not claim they follow from source
  vectors or chain bounds.
- Do not claim vector admissibility, terminal exponent rewriting,
  correspondence to `lambda`, Lemma 5, pole order, normal crossings, or RLCT
  extraction.
