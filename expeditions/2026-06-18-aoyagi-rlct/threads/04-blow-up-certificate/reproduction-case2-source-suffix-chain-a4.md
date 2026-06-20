# A4 Case 2 Source Suffix Chain

Status: reproduced the source suffix-product convention needed after the
stopped displayed Case 2 terminal block.  This is a matrix-chain checkpoint
only: it names the remaining right product that was previously represented by
a supplied suffix matrix.

## Source Anchor

On PDF pp. 14-15 Aoyagi defines, for `s = 1,...,L`,

```text
C^(s) = (c_ij^(s)),    1 <= i <= M^(s), 1 <= j <= M^(s+1),
```

and studies the paper-order product

```text
C^(1) C^(2) ... C^(L).
```

On PDF pp. 21-22, in the stopped Case 2 terminal display, the product is
written in the form

```text
diag(b_1,...,b_J,b'_(J+1),...) C'^(S+1) prod_{s=S+2}^L C^(s).
```

The factor following `C'^(S+1)` is therefore the right suffix

```text
C^(S+2) C^(S+3) ... C^(L).
```

## Pen-And-Paper Reproduction

Let the paper layer index set for layer `s` be `I_s = {1,...,M^(s)}`.  Aoyagi's
matrix `C^(s)` has rows in `I_s` and columns in `I_(s+1)`, so it is composed
in increasing paper order.

Define the chain product by

```text
Chain(i,i) = Id_{I_i},
Chain(i,j+1) = Chain(i,j) C^(j).
```

Then

```text
Chain(S+2,L+1) = C^(S+2) C^(S+3) ... C^(L),
```

with the empty-product convention

```text
Chain(L+1,L+1) = Id_{I_(L+1)}
```

when `S+1 = L`.

This is exactly the suffix needed to instantiate the already proved stopped
terminal theorem whose suffix parameter was a supplied matrix `F`.

## Lean Shape

The new matrix-chain API should use a right-multiplication recursion:

```text
product(i,p.succ) = product(i,p.castSucc) * C(p).
```

For compatibility with matrix multiplication, the raw chain can use
zero-based finite indices `Fin (n s)`.  A later source-coordinate bridge can
relate those to the one-based labels used elsewhere in the blow-up arithmetic.

The first source-facing suffix wrapper should be guarded by `S+1 <= L` and
should return the identity suffix in the boundary case `S+1 = L`.

## Boundaries

- This constructs only the remaining suffix product.
- It does not prove that `[Ctop; C0]` is Aoyagi's source-produced
  `C'^(S+1)`.
- It does not prove chart production, chart coverage, coordinate regularity,
  Jacobian arithmetic, normal crossings, RLCT extraction, termination, a full
  transition invariant, automatic Case 2 gap/tail transport, or repair of the
  printed-vector mismatch.

## Kill Conditions

- Do not multiply new following factors on the left; Aoyagi's paper-order
  product appends following layers on the right.
- Do not create a fake `C'^(L+1)`.  When `S+1=L`, the suffix after
  `C'^(S+1)` is the identity on the final actual layer.
- Do not confuse actual widths `M^(s)` with prefix minima `M(S)`.
