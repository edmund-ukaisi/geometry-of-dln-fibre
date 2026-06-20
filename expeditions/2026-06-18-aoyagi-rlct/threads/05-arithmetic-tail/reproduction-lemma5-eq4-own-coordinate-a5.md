# Pen-and-paper reproduction - Lemma 5 equation (4) own coordinate

Status: checked conditional arithmetic sanity lemma.

This note isolates one narrow calculation from Aoyagi Lemma 5, equation `(4)`.
It does not prove that the displayed vector is legal, terminal, admissible, or
part of a chart-family construction.

## Source

Aoyagi PDF p. 27, equation `(4)`, has label

```text
s = S_(j0+1)-1,
k = Htilde_j0 + 1.
```

At the own coordinate `S=s=S_(j0+1)-1`, the displayed branch gives

```text
t^(s) = Htilde'_j0 - j0.
```

For this to match the source label convention `t^(s)=k-1`, we need

```text
Htilde'_j0 - j0 = Htilde_j0.
```

## Derivation

The already-formalised displayed-chain gap is

```text
Htilde'_p - Htilde_p = e_p,
e_p = min(p, ell-p, a, ell-a).
```

If

```text
p <= a,
p <= ell-a,
```

then also `p <= ell-p`, because `p<=a` and `p<=ell-a` imply
`2p <= ell`.  Therefore

```text
e_p = p.
```

Hence

```text
Htilde'_p - Htilde_p = p,
Htilde'_p - p = Htilde_p.
```

## Lean target

Add generic chain lemmas:

```text
aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min
aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min
```

The Nat-indexed theorem is the source-facing form for equation `(4)`.

## Nonclaims

- This does not prove the displayed equation `(4)` vector is a legal source
  variable.
- This does not prove `tilde t_{s,k}=0`.
- This does not prove same-coordinate bounds for all branches.
- This does not prove source vector-to-chain correspondence, vector
  admissibility, Lemma 5, pole order, normal crossings, or RLCT extraction.
