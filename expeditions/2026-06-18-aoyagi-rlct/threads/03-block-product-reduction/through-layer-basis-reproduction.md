# A2 through-layer basis/open-chart reproduction

Status: pen-and-paper reproduction from xhigh scout `Gibbs`; independent
checker `Hooke` passed the statement and counterexamples.
Source: Aoyagi 2023 PDF pp. 11-13, Theorem 3 proof only.

## Question

Aoyagi normalizes the true total product to

```text
[ I_r  0
  0    0 ]
```

and then uses top-left `r x r` chart blocks in the product-reduction induction.
The missing elementary question is whether the true layer maps can be put in
bases that make those charts contain the base point.

Use Aoyagi's matrix convention:

```text
A^(s) : K^(H^(s+1)) -> K^(H^(s)).
```

Thus the total product is

```text
P = A^(1) o A^(2) o ... o A^(L).
```

## Decision

The condition `rank P = r` is enough to choose good bases existentially. It is
not enough for an already fixed coordinate chart.

Therefore the A2 bridge should either construct through-layer bases or carry an
explicit through-layer chart hypothesis. It must not claim that endpoint product
normalization alone makes Aoyagi's induction chart blocks invertible.

## Reproduced statement

Let `K` be a field. Let `V_s` be finite-dimensional `K`-vector spaces and let

```text
A_s : V_(s+1) -> V_s,  s = 1,...,L.
```

Let

```text
P = A_1 o A_2 o ... o A_L
```

and suppose `rank P = r`. Then there are decompositions

```text
V_s = U_s direct_sum W_s,     dim U_s = r,
```

with:

- `U_1 = range P`;
- `W_(L+1) = ker P`;
- each restriction `A_s : U_(s+1) -> U_s` is a linear isomorphism.

Choosing a basis of `U_(L+1)`, transporting it forward, and extending by bases
of the complements gives true layer matrices of the form

```text
A_s* = [ I_r  B_s
         0    D_s ],
```

for each `s`, and the total true product is

```text
P* = [ I_r  0
      0    0 ].
```

Moreover, these bases put the Aoyagi induction charts through the base point. If
the current prefix right multiplier at the true point has unitriangular form

```text
Q_2 = [ I_r  F
        0    I ],
```

then

```text
Q_2^(-1) A_(S+1)*
  = [ I_r  B_(S+1) - F D_(S+1)
      0    D_(S+1) ],
```

so the transformed next-layer top-left block is `I_r`. The prefix corner `C_1'`
also remains `I_r` by induction.

## Proof sketch

Choose `U_(L+1)` complementary to `ker P`. Since `rank P = r`, the restriction
of `P` to `U_(L+1)` is injective and has image `range P` of dimension `r`.

For each `s`, define

```text
U_s = A_s A_(s+1) ... A_L (U_(L+1)).
```

If a suffix map kills a vector in `U_(L+1)`, then the total product kills that
vector, hence the vector is zero because `U_(L+1)` intersects `ker P`
trivially. Therefore every suffix is injective on `U_(L+1)`, each `U_s` has
dimension `r`, and each `A_s : U_(s+1) -> U_s` is an isomorphism.

Pick a basis of `U_(L+1)` and transport it forward through these isomorphisms.
Extend each transported basis to a basis of `V_s`; at the last space choose the
complement `W_(L+1) = ker P`. In these bases, the `U_(s+1) -> U_s` block of
`A_s` is the identity and the lower-left block is zero. Since `W_(L+1) = ker P`,
the total product has zero top-right and lower-right blocks.

The unitriangular chart-stability calculation is block multiplication:

```text
[ I  -F ] [ I  B ] = [ I  B - F D ]
[ 0   I ] [ 0  D ]   [ 0      D   ].
```

Thus transformed top-left chart blocks stay equal to `I_r` at the base point.

## Fixed-chart obstructions

Product rank alone does not make a preselected coordinate chart work. Over any
field, take

```text
A_1 = [0 1; 0 0],
A_2 = [0 0; 1 0].
```

Then

```text
A_1 A_2 = [1 0; 0 0]
```

has rank `1`, and both layers have rank at least `1`, but the selected top-left
`1 x 1` block of each layer is zero.

Even invertible original top-left blocks do not guarantee transformed induction
charts unless the bases are through-aligned. With

```text
A_1 = [1 1; 0 1],
A_2 = [1 0; -1 1],
A_3 = [1 0; 1 0],
```

the total product is

```text
[1 0; 0 0],
```

but after the first Aoyagi right multiplier, `Q_2^(-1) A_2` has top-left entry
`0`.

## Boundary cases

- If `r = 0`, then each `U_s = 0`, the `0 x 0` determinant condition is
  vacuous, and rank-zero means the total product is zero.
- If some `H^(s) = r`, then `W_s = 0`; adjacent residual blocks have zero rows
  or zero columns. The statement still works with empty matrices.

## Kill conditions

- Any theorem saying fixed product normalization alone implies Aoyagi's
  top-left layer blocks are invertible is false.
- Adding only `rank A_s* >= r` is still too weak in fixed bases.
- Assuming original layer corners are invertible is still too weak for
  transformed induction charts unless the bases are through-aligned or chart
  hypotheses are explicit.
- This lemma is elementary constant-basis/block-chart algebra only. It must not
  claim RLCT equality, analytic ideal-germ invariance, or Aoyagi Lemma 1
  consequences.

## Lean target suggested by the reproduction

Lean now formalizes the field-linear through-subspace layer in
`DLNFibre.DLN.Aoyagi.exists_chain_throughSubspaces`.

The Lean statement uses source-to-target indexing

```text
A i : V i.castSucc -> V i.succ
```

so it is Aoyagi's chain after reversing the paper-order maps
`A^(s) : V_(s+1) -> V_s`. The theorem chooses `U0` complementary to the kernel
of the total composite, defines each `U j` as a prefix image, proves adjacent
edge transport and restricted-edge equivalences, proves suffix-kernel
disjointness, proves constant `finrank` equal to the total range `finrank`, and
identifies the last through-subspace with the total range.

The first matrix chart corollary now exists in Lean as
`DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`:
in transported `Module.Basis.sumQuot` bases, each through-subspace edge is
`fromBlocks 1 B 0 D`. The complement/direct-sum version also exists as
`DLNFibre.DLN.Aoyagi.exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`:
with supplied complements and complement bases, the same block form holds for
ambient bases built using `basisOfIsCompl`.

Next prove the chain packaging matching the current `fromBlocks` APIs: choose
simultaneous compatible bases, show the total product is
`fromBlocks 1 0 0 0`, and then connect the Aoyagi transformed next-layer
top-left corner to the already-proved unitriangular chart-stability identity.

## Checker verdict

Xhigh checker `Hooke` found no blocking mathematical error. The theorem is true
with finite-dimensional field-vector-space hypotheses, but it is an auxiliary
repair rather than a source-stated Aoyagi lemma. The fixed-chart counterexamples
work, the block form `[I B; 0 D]` is sufficient, and the formal Lean statement
should state rank as `finrank K (LinearMap.range P) = r` or an equivalent
finite-dimensional rank assertion.

Formalisation-ready now:

- simultaneous chain-basis and total-product block-form corollaries.

Still not formalisation-ready:

- full Aoyagi Theorem 3;
- any RLCT, analytic ideal-germ, or Aoyagi Lemma 1 consequence.
