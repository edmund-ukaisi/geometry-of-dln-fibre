**Q1 Verdict**

Choose **route (i), but make it parametric**.

FACT: the determinant algebra in route (ii) is width-parametric once you already have full-ambient CLM factors.  
INFERENCE: the hard part is not the monoid-hom telescope; it is proving

```lean
fderiv phi_M x = list.prod fullAmbientFactors_M x
```

over opaque dependent widths. That proof reintroduces the same indexing burden.

Route (i) does not eliminate the bridge obligation, but it moves it to the right level:

```lean
chartParamsGen(u, B_det) = pack_M (T_M x)
```

That is still a bridge, but it can be one structural, width-parametric extensional proof using canonical `FlatIdx`, `active : Finset`, and the banked `chainA_apply_castAdd/natAdd` entry laws. It avoids the anchor-style explicit vector tables.

**Q2 Route (ii) Obstruction**

Route (ii)’s decomposition is essentially a bridge in disguise.

Since `phi_M` is nonlinear, the Jacobian does not automatically telescope just because the chart was defined by a chain recursion. To get the determinant product, Lean needs either:

```lean
phi_M = F_n ∘ ... ∘ F_1
```

and then the chain rule, or directly:

```lean
fderiv phi_M x = DF_n(...) ∘ ... ∘ DF_1(x)
```

The second proof is not easier. It is the derivative-level version of the same factorization bridge, with extra product-rule and block-embedding noise. Unless the chart is already implemented as a composition/fold of those maps, route (ii) hides the same opaque-width fight inside the fderiv equality.

**Q3 Recommendation**

Use **route (i) parametric**.

The four anchors are valuable because they already validate the factor order, pivot placement, spectator factors, and final determinant shape. The bad part was the explicit coordinate tables, not the factorization strategy.

The clean ∀M move is:

```lean
T_M    : flat coordinates -> flat coordinates
pack_M : flat coordinates -> chart/layer parameters
```

defined from canonical `FlatIdx`, the achiever path `t*`, and residual block sizes. Then prove the bridge once by indexed extensionality, using the banked entry laws. Route (ii) is untested and still needs a compose/fderiv-product bridge before the banked determinant engine can fire.

**Q4 Active Set**

Yes: canonical `FlatIdx` plus a decidable `active : Finset FlatIdx` with

```lean
active.card = minAdm = m
```

suffices for the radial factor, provided it matches the convention of the banked `pivotBlowupOn` theorem, usually including the pivot so the determinant is

```lean
|x_p|^(active.card - 1) = |x_p|^(m - 1)
```

No per-`M` bijection `e_M` is needed. The only extra side condition is the theorem’s pivot membership convention, e.g. `p ∈ active` or equivalently passing `active.erase p` if the theorem expects nonpivot active coordinates.

**Q5 (3,3,3,3) Check**

Here `minAdm = 6`, so the radial pivot contributes

```lean
|x_p|^(6 - 1) = |x_p|^5
```

In the anchor notation this is `|u0|^5`.

All three boundaries drop along `T* = (2,1,0)`. The boundary Schur/LDU spectator determinants contribute the banked factors

```lean
|u1|^4 · |u4|^2 · |u9|^3
```

The unit-triangular chain factors, shears, `pack_M`, and `paramsEquivFlat` contribute determinant `1`. So route (i) gives:

```lean
|det D(phi_M)| = |u0|^5 · |u1|^4 · |u4|^2 · |u9|^3
```

**Q6 Kill Flag**

No: both routes are not walls.

Route (ii) is the risky wall because its advertised telescope still requires an unbanked width-parametric fderiv-as-product proof. Route (i) is a contained bridge problem with four working templates and known local entry laws. Use route (i), parametric.