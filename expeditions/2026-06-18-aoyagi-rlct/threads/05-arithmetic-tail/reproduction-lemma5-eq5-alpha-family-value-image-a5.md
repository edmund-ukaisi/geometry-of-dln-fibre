# Pen-and-paper reproduction - Lemma 5 equation (5) alpha-family value image

Status: reproduced; xhigh reviewed.

## Source

Aoyagi PDF p. 27, equation `(5)`, uses the strict offset parameter `alpha`
with

```text
alpha = Htilde'_(j0) + 1 - k,
Htilde_(j0)+1 <= k < Htilde'_(j0)+1,
j0 > alpha.
```

On the own block `j=j0+1`, the displayed branch value specializes to

```text
Htilde'_(j0) - alpha.
```

In Lean's zero-based selected-coordinate convention, paper `j0` is coordinate
`p`.  The own-block strict-offset family is therefore

```text
alpha |-> Htilde'_p - alpha.
```

## Reproduction

The previous Eq5 own-coordinate offset slice used the finite strict-offset
domain

```text
1 <= alpha <= min(excess(ell,a,p), p-1),
```

where `excess(ell,a,p)=Htilde'_p-Htilde_p` and the `p-1` term encodes
`alpha<p`.

Thus the finite image of the strict alpha family is

```text
image
  (alpha |-> Htilde'_p - alpha)
  {alpha | 1 <= alpha <= min(excess(ell,a,p), p-1)}.
```

Lean now names this strict domain as

```text
aoyagiLemma5Eq5AlphaDomain ell a p.
```

The alpha-family image over this named domain is exactly the already-defined
finite set

```text
aoyagiLemma5Eq5OffsetValueSet ell a p M m.
```

The Lean theorem is consequently definitional after unfolding the named domain:
it names this equality so later classifier code can rewrite through the
alpha-family image without unfolding the set definition at every use.

## Lean Target

```text
aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet
```

## Nonclaims

- No construction or existence of equation `(5)`'s displayed vector.
- No source-label legality for `k`.
- No full equation `(5)` selected-span classifier or chart sequence.
- No terminal `tilde t=0`.
- No vector admissibility or source-vector-to-chain correspondence.
- No Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

The theorem becomes misleading if the "alpha family" is given any domain other
than the strict-offset domain above, or if the value map is not exactly
`Htilde'_p-alpha`.
