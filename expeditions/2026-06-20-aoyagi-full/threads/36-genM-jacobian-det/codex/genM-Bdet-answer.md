**Q1**

**FACT:** The extracted active pattern is correct for the two anchors. The active residual normals are exactly:

```text
(⊔ interior bottom-right E-blocks Rmat_k[r_k x c_k]) ⊔ Rfin_L[Text_L x Wext_L]
```

with cardinality

```text
minAdm = Σ_{k=1}^{L-1} r_k c_k + Text_L * Wext_L.
```

It specializes to:

```text
222:  Rmat_1 E has 1 entry, Rfin_2 has 2 entries => 3.
3333: Rmat_1 E has 1, Rmat_2 E has 2, Rfin_3 has 3 => 6.
```

**INFERENCE:** The pivot location need not be free per `M`. A canonical uniform choice should work, provided it is chosen from a nonempty active residual block and is wired as the fixed `1` residual entry. The cleanest canonical rule is probably:

```text
choose the first nonempty active E-block in chain order; use its top-left entry as FIXED 1.
```

That reproduces the 3333 style directly. Alternatively, “always use `Rfin_L(0,0)`” also looks valid whenever the leaf block is nonempty, and it reproduces the 222 style directly.

The anchors use different pivot locations, but that difference is not mathematically essential. It reflects a chart choice, not a determinant exponent choice.

**DET:** The determinant exponent is invariant under the pivot location:

```text
|det D phi| = |u|^(active.card - 1) * spectator
            = |u|^(minAdm - 1) * spectator.
```

The pivot removes one radial/angular degeneracy; the remaining `minAdm - 1` active residual coordinates contribute the `u` powers. Which active coordinate is fixed to `1` should only change the nonzero spectator factor/sign/permutation, not the exponent.

**Q2**

Yes. `minAdm <= flatDim = N` is automatic here.

Reason: the active set is not an abstract set of new coordinates. It is a selected subset of residual coordinates inside the decoder’s flat coordinate space, and those residual coordinates are themselves a subset of all flattened layer/chart coordinates.

So:

```text
active ⊆ residualCoords ⊆ Fin N
```

hence:

```text
active.card = minAdm <= N.
```

This is a construction-level fact, not an additional admissibility hypothesis.

**Q3**

This is the only delicate piece, but I would not call it a research wall.

Uniform proof strategy:

Pick one explicit parameter point:

```text
u arbitrary/nonzero,
Bmat_k = canonical full-rank Schur/K-frame values,
Nblk_k, Wblk_k = convenient chaining values, often zero where allowed,
all non-pivot angular active residuals = 0,
fixed pivot residual = 1.
```

At that point, the telescoped quotient `H` should be nonzero because the live residual pivot injects a nonzero component through the chain instead of being killed by a dead leaf. Therefore:

```text
VvalGen = ||H||^2
```

evaluates to a positive value at that point. Since `VvalGen` is polynomial in the coordinates, one nonzero evaluation proves:

```text
VvalGen ≠ 0
```

as a polynomial. Then zero-set-nullity gives positivity a.e. for `VvalGen`, and boundedness/measurability are the existing `Ubound/Umeas` style obligations.

**Sharp caveat:** formalizing this uniformly still requires a dependent-width telescoping lemma saying the chosen canonical pivot survives to `H != 0`. If that lemma is not already banked, it is real engineering. But it should be a uniform lemma, not one witness point per `M`.

**Q4**

No genuine research wall.

Verdict by piece:

```text
parametric B_det M:        substantial dependent-width engineering, not research.
active Finset:            routine once residual coordinate indexing is organized.
minAdm <= N:              immediate subset/cardinality argument.
nonzero VvalGen witness:  the main remaining proof burden, but likely uniform.
```

The only thing I would flag as a serious residual is the uniform `H != 0` witness lemma for `VvalGen`. If that pivot-survival argument fails under some admissible width pattern, then it becomes per-`M`. But from the stated construction and anchors, the expected answer is: uniform proof available, no research wall.