# Reproduction - A2 residual-factor product rank obstruction

Date: 2026-06-25.

Status: controller pen-and-paper reproduction before Lean.  This is finite
matrix algebra for the residual-factor product boundary.

## Source/Boundary Anchor

The previous residual-factor product checkpoint made explicit that the p.13
suffix residual object is an ordered product of intermediate residual factors.
This note records the elementary obstruction that follows from that product
shape: a final residual matrix cannot be arbitrary unless it is compatible with
all intermediate residual dimensions.

This is not a new Aoyagi source theorem.  It is a Lean guardrail around the
fixed-base residual-product API.

## Pen-And-Paper Check

Let

```text
C_p : Matrix(kappa_{p+1}, kappa_p)
```

be residual factors, and let

```text
R(j,i) = residualFactorProduct(C,j,i)
```

be their ordered product from endpoint `j` down to `i`.

For `i <= q <= j`, split the product at the intermediate index `q`:

```text
R(j,i) = R(j,q) R(q,i).
```

This follows by descending induction on `i`.  The base case `i=q` is
`R(j,q)=R(j,q) I`.  The step uses the recursive formula

```text
R(j,p) = R(j,p+1) C_p
```

and associativity:

```text
R(j,p)
  = R(j,p+1) C_p
  = (R(j,q) R(q,p+1)) C_p
  = R(j,q) (R(q,p+1) C_p)
  = R(j,q) R(q,p).
```

Thus the final matrix `R(j,i)` factors through the intermediate residual type
`kappa_q`.

Over a nontrivial commutative ring, matrix rank satisfies

```text
rank(A B) <= rank(A) <= card(kappa_q)
```

for `A : Matrix(kappa_j,kappa_q)`.  Hence

```text
rank R(j,i) <= card(kappa_q)
```

for every intermediate `q`.

Consequently, in a two-edge chain with `card(kappa_1)=1` and
`card(kappa_0)=card(kappa_2)=2`, no factor product can equal a rank-two
identity matrix from `kappa_2` to `kappa_0`.

## Lean Target

Add in `ProductReduction.lean`:

```text
ChartLocalSuffixState.residualFactorProduct_trans
ChartLocalSuffixState.rank_residualFactorProduct_le_card_intermediate
```

## Boundary

- This proves a finite rank obstruction for explicit residual-factor products.
- It does not prove that Aoyagi's displayed selected-entry residual matrix has
  or lacks a factorization.
- It does not construct source factors, source charts, source coverage,
  residual-index equivalence, source-measure transport, normal crossings,
  pole order, or RLCT.
