## 1. Irreducible?

**Yes.** The landed bricks do not force the reverse inequality. The missing datum is separability of the orbit map, equivalently that the differential of `μ_M` hits the tangent space of the orbit.

Reason: in characteristic `p`, `G` can act transitively on a smooth open orbit while the orbit map has zero differential. Example: `𝔾ₐ` acts on `𝔸¹` by `t • x = x + t^p`. The orbit of `0` is all `𝔸¹`, but `d(t ↦ t^p)_0 = 0`. So “open dense transitive orbit + smooth closure” does not imply `range dμ = T_O`.

Thus stabilizer smoothness/separability is not cosmetic; it is exactly what excludes this pathology.

## 2. Cheapest Reverse Route

Cheapest math route here is **not Cartier**. Use the special form of the stabilizer.

For a quiver representation,

`Stab(M) = Aut(M) = (End(M))ˣ`

and

`End(M) = ker δ⁰ = Hom(M,M)`.

So `Stab(M)` is the principal open subset of the affine space `Hom(M,M)` where the product of vertex determinants is nonzero. Hence it is smooth and has dimension `finrank Hom(M,M)`.

The Lean chain:

- `LinearMap.finrank_range_add_finrank_ker` / rank-nullity: **KNOWN**.
- `Matrix.isUnit_iff_isUnit_det`, `LinearMap.isUnit_iff_isUnit_det`: **KNOWN**.
- `Stab(M) ≅ D(det) ⊂ Hom(M,M)` as a scheme/principal open: **INFER**.
- principal opens/open immersions are smooth; `Smooth`, `SmoothOfRelativeDimension`, open immersions smooth: **KNOWN**.
- `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`: **KNOWN**, but only “reduced group over alg-closed field is smooth”.
- Cartier “all finite-type group schemes over perfect fields are smooth”: **NOT KNOWN in v4.29**, and false as stated in char `p` without reducedness. Example: `μ_p ⊂ 𝔾ₘ`.

Remaining non-cheap piece: `dim O_M = dim G - dim Stab(M)`. Mathlib v4.29 has scheme fibres (`Scheme.Hom.fiber`, `fiberHomeo`) and smooth morphism infrastructure, but no ready quotient `G/H` or fibre-dimension theorem for this use: **INFER/MISSING**.

## 3. Collapse-Into-One Viability

**No, not as a simplification.** Identifying the local cotangent with `coker (δ⁰)^T` is equivalent to proving `range δ⁰ = T_M Z_M`. That is the same separability/submersion content in dual form.

It can be a good final packaging, especially since your cotangent/Jacobian bricks are strong, but it does not remove the hard theorem. The Frobenius-action example shows the collapse fails without separability.

## 4. Ranking A/B/C

1. **A: Jacobian route + explicit stabilizer smoothness**  
   Cleanest. Keep the landed Jacobian/smooth-local-dimension stack. Prove `Stab(M)` is `D(det)` in `Hom(M,M)`, then add the smallest orbit-submersion/dimension bridge needed.

2. **B: fibre-dimension theorem for `μ_M`**  
   Mathematically standard, but Mathlib support looks thin. You would need a serious generic/all-fibres dimension theorem.

3. **C: scheme quotient `G/Stab`**  
   Cleanest on paper, worst in Lean v4.29. Quotient/group-action scheme infrastructure is not there at the needed level.

**Single cleanest:** A.  
**Hardest sub-lemma:** not stabilizer smoothness; it is the local orbit theorem: smooth stabilizer implies the orbit map is separable/submersive and `dim O_M = dim G - dim Stab(M)`.

## 5. Suspicious Assumption

The suspicious statement is: “closed subgroup of a smooth group over a perfect field is smooth.” False in characteristic `p`; `μ_p ⊂ 𝔾ₘ` is the standard counterexample. Your stabilizer is smooth for the special reason `Aut(M)` is an open subset of `End(M)`, not by that general principle.