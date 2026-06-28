**Verdict:** under the stated algebra, the radial-separability claim holds. The reason is stronger than triangularity: after flattening all output matrices, the chart has the form

```text
Phi(u, h, z) = P(z) + u r0 + u * sum_a h_a r_a,
```

where `z` denotes all non-radial coordinates, `h_a` are the free radial/angular directions, and the `r_a` are fixed output directions supported in whatever layers the corresponding `R_k` or `Rfin` touches. Hence

```text
D_z Phi   = D_z P(z)              u-free
D_{h_a} Phi = u r_a
D_u Phi   = r0 + sum_a h_a r_a    u-free
```

So every angular radial column has a common factor `u`, and after factoring those columns the whole remaining Jacobian matrix is independent of `u`. Therefore, for any square active coordinate chart of this form,

```text
det J = u^q * G(z,h),    with partial_u G = 0,
```

where `q` is the number of non-pivot radial/angular coordinates. In the usual pivot blow-up of an active center of size `minAdm`, `q = minAdm - 1`.

The layer mechanism is the unipotent `chainA` shear. For each boundary,

```text
A_k = [ C_{k+1} - N_k W_k
        W_k              ]
```

is obtained from `[C_{k+1}; W_k]` by the block row operation

```text
[ I  -N_k ]
[ 0   I   ],
```

columnwise in the target. This has determinant `1`. The `-N_k W_k` terms are therefore determinant-preserving shears; they introduce only `z`-dependent Jacobian entries. The additive `u R_{k+1}` term in `C_{k+1}` is not multiplied by this shear into any new `u`-dependent coefficient: it contributes only to the `du` column, or, if its coefficient is a free angular coordinate `h_a`, to a column equal to `u r_a`.

So fixed interior `R_k` of any rank, including a rank-2 or multi-entry coupling in an interior `t >= 2` core, cannot leak `u` into the cofactor. Rank-one pivots are not special for separability. Multiple free radial directions simply give multiple columns `u r_a`; they may make the cofactor vanish if the chart directions are dependent, but they do not make it depend on `u`.

Two caveats about the literal prompt:

1. If all entries of `B_0` are genuinely free while the output is only `(A_0,...,A_{L-1})`, then `B_0` is inert under the displayed formula, so the literal full Jacobian has zero columns / is not the intended square chart. One must fix or discard those inert coordinates, as in the actual normalized chart.
2. If all entries of `Rfin` are free in addition to `u`, the radial block has one coordinate too many. The standard square radial chart fixes one pivot entry, e.g. `Rfin_pivot = 1`, and blows up the other active directions, giving exponent `active.card - 1`.

Failure would require leaving this setup: for example, an active radial coordinate also appearing unscaled elsewhere, or an `R_k` coefficient depending on `u` or nonlinearly on another active radial coordinate. With the exact `chainQ`/`chainA` formulas and independent radial `R` directions, no such leakage occurs, including for `L >= 4`.