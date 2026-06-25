**Short Verdict**

`toSub` should use `⅟H` on the first edge and `⅟L` on the last edge. Since `aeval toSub` sends `p` to `p(toSub)`, `toSub` must encode the normalized variables `Ã` in terms of the old variables `A`.

For distinct endpoints:

```text
edge 0:
X⟨0,(i,j)⟩ ↦ ∑ m, C ((⅟H) m j) * X⟨0,(i,m)⟩

edge N-1:
X⟨N-1,(i,j)⟩ ↦ ∑ l, C ((⅟L) i l) * X⟨N-1,(l,j)⟩
```

So `aeval toSub (multPoly d r c)` computes `mult(Ã)`, hence gives
`((⅟L)^C * M * (⅟H)^C) r c`, where in Lean the endpoint matrices must be mapped into the polynomial ring, e.g. `(⅟L).map C`, `(⅟H).map C`.

For `N = 1`, the only edge gets both operations:

```text
X⟨0,(i,j)⟩ ↦
  ∑ l, ∑ m, C ((⅟L) i l * (⅟H) m j) * X⟨0,(l,m)⟩
```

This is exactly `(⅟L * A₀ * ⅟H) i j`. If your definition branches `if e = 0 then ... else if e = last then ...`, it is wrong for `N = 1`.

**Round Trip**

`fromSub` is the same construction with `H`, `L` replacing `⅟H`, `⅟L`:

```text
N = 1:
X⟨0,(i,j)⟩ ↦ ∑ l, ∑ m, C (L i l * H m j) * X⟨0,(l,m)⟩
```

The inverse collapses use both orientations:

```text
aeval toSub (fromSub x):
  left side uses  L * ⅟L = 1      -- `mul_invOf_self L`
  right side uses ⅟H * H = 1      -- `invOf_mul_self H`

aeval fromSub (toSub x):
  left side uses  ⅟L * L = 1      -- `invOf_mul_self L`
  right side uses H * ⅟H = 1      -- `mul_invOf_self H`
```

So do not expect only `invOf_mul_self` everywhere.

**Clean Structure**

Best fit for this repo: model the operation as endpoint `baseChange` on the generic tuple, not as ad hoc edge cases.

Take the vertex unit data over `P := MvPolynomial (RepCoord d) R`:

```text
P_to(0) = H^C
P_to(N) = (L^C)⁻¹
P_to(middle) = 1
```

Then `baseChange P_to (genericTuple d)` has exactly the desired endpoint-normalized factors, including the `N = 1` coincidence automatically. The inverse is `P_to⁻¹`.

For the staged contract, define:

```text
toSub x   := (baseChange P_to   (genericTuple d) x.1) x.2.1 x.2.2
fromSub x := (baseChange P_from (genericTuple d) x.1) x.2.1 x.2.2
```

Then assemble with `aeval`. Prove `aeval toSub = φ_to` and `aeval fromSub = φ_from` by `MvPolynomial.algHom_ext` + `MvPolynomial.aeval_X`.

Useful project/API names:

```text
baseChange_apply
baseChange_mul
submult_smul
mult_eq_submult

MvPolynomial.aeval
MvPolynomial.aeval_X
MvPolynomial.aeval_C
MvPolynomial.algHom_ext
MvPolynomial.comp_aeval
AlgEquiv.ofAlgHom

Matrix.mul_apply
Matrix.map_apply
Matrix.map_mul
Matrix.one_apply
Matrix.ext
invOf_mul_self
mul_invOf_self
Matrix.invOf_mul_cancel_left
Matrix.mul_invOf_cancel_left
Matrix.invOf_mul_cancel_right
Matrix.mul_invOf_cancel_right
unitOfInvertible
Invertible.map
map_invOf
RingHom.mapMatrix
```

**Main Traps**

`Matrix` coefficients must live in the polynomial ring for the final statement: use `(⅟L).map C * Matrix.of (multPoly d) * (⅟H).map C`.

If you prove the `N = 1` double-sum directly, expect `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul`, and coefficient reassociation/commutation. The composition/baseChange route avoids most of that.

For mult-transport, Lean will still need an induction/general lemma like `map_multPrefix` or the existing `submult_smul` route. The fact that middle variables are fixed does not by itself make `aeval` simplify an entire prefix product without a product-respecting lemma.