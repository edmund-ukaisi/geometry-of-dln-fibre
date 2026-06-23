**VERDICT:** YES, provided the reg X-block itself is included with coefficient `id` in the sum. The map is a unitriangular shear: it changes the reg coordinate by adding gauge X-coordinates while leaving those gauge coordinates available, so no dimension is lost.

The shear has shape, on the relevant X-coordinates,

```text
(x0, x1, ..., x_{L-1}, rest)
  ↦
(x0 + x1 + ... + x_{L-1}, x1, ..., x_{L-1}, rest)
```

where `x0` is the reg X-block and `x1 ... x_{L-1}` are the interior gauge X-blocks. Its inverse is

```text
(u, x1, ..., x_{L-1}, rest)
  ↦
(u - x1 - ... - x_{L-1}, x1, ..., x_{L-1}, rest)
```

So the linear map is invertible: matrix form is block unitriangular,

```text
[ I   Σ ]
[ 0   I ]
```

with determinant/unit inverse coming from the identity diagonal blocks. In Lean terms, this should package as an explicit continuous linear equivalence `e : M ≃L[ℝ] M`, not as `ContinuousLinearMap.fst`.

Therefore PIN1 should close after weakening the derivative obligation from “derivative equals projection/fst” to:

```lean
HasStrictFDerivAt regStraighten (e : M →L[ℝ] M) wstar
```

for this explicit shear CLE `e`. No reg-slot restructure is forced by PIN1.

PIN2 remains separate: it needs the **value** of `deepestEPivot` / residual to approximate or equal the summed X-corner `Σ_s X_s`. That is independent of whether the derivative is `fst`, `id`, or a shear.

**Cheapest decl-check:** confirm that `regStraighten` leaves the interior `X_s` gauge coordinates as free output coordinates, rather than replacing/duplicating them by the same summed value. In other words, check it is like `(a,b) ↦ (a+b,b)`, not `(a,b) ↦ (a+b,a+b)` or `(a,b) ↦ (b,b)`.

**BLAST RADIUS:** bounded: weaken `_deriv` to an arbitrary invertible CLE, define/package the shear CLE and its inverse, likely small local edits. No reg/image-kernel restructure unless the decl-check shows the interior `X_s` are consumed rather than preserved.