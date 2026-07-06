**1. VERDICT**

Route A is sound and should be strictly lower-risk than the two-peel degraded route, provided you formalise the first peel explicitly rather than trying to rescue `dln_hchart_residual`.

The first peel is enough. Higher-rank layers at `v` do not force a second reduction; they only mean the reduced core point `P` is generally not `0`. After the peel, the slice is the loss of an `(H0-r) × (H1-r) × (H2-r)` DLN at that point `P`. Your already-green Aoyagi/Theorem 4 core monotonicity then handles arbitrary `P`.

The hidden obstruction is not mathematical but formalisation-local: you must prove an explicit local chart/splitting with enough measure/Jacobian control. Avoiding `Ψsymm` is exactly right. The danger is accidentally replacing the slice germ by a finite-jet or “comparable” object too early; the Schur-complement identity must be exact on the slice.

**2. THE EXPLICIT FIRST PEEL**

First reduce `B` by invertible output/input changes so that the chosen rank-`r` minor is the upper-left block and

`B = [[I_r, 0], [0, 0]]`.

For `A0 : H0 × H1`, `A1 : H1 × H2`, choose a hidden index set `α` of size `r` such that both selected blocks are invertible at `v`. This exists by Cauchy–Binet: since the upper-left `r × r` block of `B = v0 v1` is invertible, some common hidden minor contributes nontrivially.

Block the layers as

`A0 = [[X, Y], [Z, W]]`,  
`A1 = [[S, T], [U, V]]`,

where `X : r×r`, `Y : r×(H1-r)`, `Z : (H0-r)×r`, `W : (H0-r)×(H1-r)`, and similarly `S,T,U,V`.

Let product blocks be

`M11 = X*S + Y*U`,  
`M12 = X*T + Y*V`,  
`M21 = Z*S + W*U`,  
`M22 = Z*T + W*V`.

On the open set where `X` and `M11` are invertible, define

`K = [-X⁻¹ Y ; I]`,  
`G = [A1_left, K] = [[S, -X⁻¹Y], [U, I]]`.

Then `G` is invertible because `det G = det(X⁻¹) det(M11)` up to the standard block determinant sign convention. Moreover,

`A0 * G = [[M11, 0], [M21, W - Z*X⁻¹*Y]]`

and

`G⁻¹ * A1 = [[I, M11⁻¹*M12], [0, V - U*M11⁻¹*M12]]`.

Therefore the Schur complement of the product is exactly

`M22 - M21*M11⁻¹*M12 = A0red * A1red`

with

`A0red = W - Z*X⁻¹*Y`,  
`A1red = V - U*M11⁻¹*M12`.

This is the reduced DLN core of widths `H-r`.

The regular coordinates are

`p = (M11 - I, M12, M21)`,

of dimension `r² + r(H2-r) + (H0-r)r = nRegL2 H r`.

The residual vector may be taken as

`q(p,z) = M22 - B22 = M21*M11⁻¹*M12 + A0red*A1red`.

Hence on the slice `p = 0`,

`q(0,z) = A0red*A1red`.

So the slice loss is exactly

`∑ q(0,z)^2 = dlnLoss (H-r) 0 (A0red, A1red)`.

The flat variables are the remaining gauge coordinates, e.g. the hidden-pivot data such as `X`, `Y`, `U`, plus redundant coordinates needed to make the map locally bijective. Concretely, the essential projection is

`φ(z) = (A0red(z), A1red(z))`.

The scalar unit `U(z)` only enters if you compare Frobenius loss after non-orthogonal normal-form changes or after replacing a positive quadratic form by the standard squared norm. It must be bounded above and below by positive constants near the basepoint.

This construction is algebraic/rational on the chart open set: polynomial in entries plus inverses of `det X` and `det M11`. No existence-only IFT inverse is needed. You may still use an IFT-style theorem to certify “this explicit map is a local chart,” but not to define the residual.

**3. THE FLAT-DIRECTION FUBINI RLCT LEMMA**

Build the lemma in this form:

For finite-dimensional Euclidean spaces `E,F`, point `(x0,y0)`, measurable nonnegative `g : F → ℝ`, and local RLCT defined by finite integrability of `g y ^ (-c)`,

`rlctAtOn (fun p : E × F => g p.2) (x0,y0) = rlctAtOn g y0`.

More generally, allow closed/local domains if your `rlctAtOn` carries a set parameter, but keep the first version product-open.

Proof route: genuine Tonelli/Fubini, not `rlctAtOn_comp_homeomorph`. Projection is not a homeomorphism.

- If `g^{-c}` is integrable near `y0`, then `(g ∘ Prod.snd)^{-c}` is integrable on `Ux × Uy`, with integral `vol(Ux) * ∫Uy g^{-c}`.
- Conversely, if the pullback is integrable near `(x0,y0)`, choose a product ball/box `Ux × Uy` inside that neighbourhood with `0 < vol(Ux) < ∞`; Tonelli gives finiteness of `vol(Ux) * ∫Uy g^{-c}`, hence finiteness of the base integral.

This is the single load-bearing new analytic brick. Everything else is algebraic chart bookkeeping plus already-banked unit/homeomorphism invariance.

**4. DECOMPOSITION + RISK**

1. `[reuse-banked]` Normalise `B` by `block_elimination`; transfer RLCT through bounded positive quadratic/unit comparison.
2. `[new-clean]` Use Cauchy–Binet to choose a common hidden pivot `α` with `X` and the corresponding left block nonzero at `v`.
3. `[new-clean]` Define the explicit rational chart open set: `det X ≠ 0`, `det M11 ≠ 0`.
4. `[new-clean]` Prove the block identities for `G`, `A0red`, `A1red`, and the Schur complement.
5. `[new-risky]` Prove the explicit coordinate map is a local measurable chart with acceptable Jacobian/unit control.
6. `[reuse-banked]` Apply `rlct_additive_smooth_block` to peel the `p = (M11-I,M12,M21)` block.
7. `[new-risky — likely wall]` Prove flat-direction Fubini RLCT equality for `g ∘ proj`.
8. `[reuse-banked]` Apply `rlctAtOn_unit_invariant_aux` for bounded positive units.
9. `[reuse-banked]` Apply `core_zero_le_of_params` to dominate the resulting core point `P`.

The most likely hidden wall is step 5, not the algebra itself: Lean may make the explicit chart/Jacobian/measurable-equivalence packaging painful.

**5. SECOND PEEL?**

I do not think Route A secretly needs degraded `R1@M'` or a second peel. The first peel already lands on the full reduced-width DLN loss

`dlnLoss (H-r) 0 (A0red, A1red)`

at a generally nonzero point `P`. A second peel is only needed if you insist on moving that reduced point to a deepest/origin-style normal form. Your Theorem 4 bridge makes that unnecessary.