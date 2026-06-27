**Verdict:** the per-node R1 chart is **structurally distinct** from the outer L2 unit-pivot split.

- **FACT:** In the outer L2 split, `B` has positive rank and the deepest identity-corner chart contains a regular block with a perturbed-unit pivot `(1 + w0)`. The elimination is unit-Jacobian and uses no blow-up.
- **FACT:** In the per-node zero-core `||prod(C')||^2` at the origin, all generators are homogeneous bilinear, the Jacobian rank is `0`, and there is no regular block or unit pivot.
- **INFERENCE:** Therefore `schur_chart_exists` cannot be routed as “apply #125 directly per node.” The hypotheses that make the #125 outer peel work are absent at the zero-core origin.

The #125 **idea** still recurs, but not the #125 **chart**.

- **FACT:** After the coordinate-subspace/rank-stratum blow-up, e.g. `A1 = x * Ahat` with `Ahat[0,0] = 1`, the pivot is a hard constant `1`.
- **INFERENCE:** The Schur straightening then becomes a hard-pivot transvection: determinant `±1`, measure-preserving, lemma2Fwd-style.
- **Contrast:** Outer L2 uses a perturbed-unit pivot `(1+w0)` and gets a unit-Jacobian change of variables. Per-node R1 first creates a hard pivot by blow-up, then uses a determinant-`±1` transvection.

So the per-node chart is:

```text
coordinate-subspace blow-up, Jacobian x^(Mval-1)
then hard-pivot Schur transvection, det ±1
then recurse on the smaller zero-core
```

whereas the outer L2 split is:

```text
unit-pivot regular peel, det a unit
no blow-up
then residual zero-core
```

**Obstruction status:** no fresh mathematical or Mathlib-shaped obstruction is indicated by the structure.

- **FACT:** The blow-up piece is the already-green coordinate-subspace/pivot blow-up pattern `pivotBlowupOn`.
- **FACT:** The hard-pivot straightening is the already-green lemma2Fwd-style transvection, with measure preservation.
- **INFERENCE:** The recursive node should be elementary modulo assembling these green components uniformly. The crux is routing/packaging, not inventing a new resolution mechanism.

**Precise fm-2 routing verdict:**  
`schur_chart_exists` should be routed as:

```text
distinct C2 node reusing green pieces
```

not as:

```text
apply #125 per-node directly
```

and not as:

```text
fresh construction with a new obstruction
```

The correct statement is: #125’s Schur-pivot *technique* recurs per node only after a blow-up has produced a hard pivot; the outer #125 unit-pivot no-blow-up split itself does not apply at the zero-core origin.