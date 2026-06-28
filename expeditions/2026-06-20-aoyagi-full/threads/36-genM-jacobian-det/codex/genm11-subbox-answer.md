**1. Source Set And Peel**

Yes: peel only `u_p`. Define

```lean
frontU u := ∑ i, (frontMat M hL u i ⟨0, hm1⟩)^2
p := smPivotCoord M hL hrow hcol
ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (routeMAmbient M) => ℝ) p
S := ee ⁻¹' (Set.Ioo (0:ℝ) α ×ˢ R)
```

where `R : Set (Fin (routeMAmbient M - 1) → ℝ)` is a positive-measure rest box chosen below, and `α < ε`.

Then prove the pivot-independence helper:

```lean
frontU (Fin.insertNth p x y) = frontU (Fin.insertNth p 0 y)
```

from `frontMat_update_pivot`, using
`Fin.insertNth p x y = Function.update (Fin.insertNth p 0 y) p x`.

Under `ee.symm`, the rewritten integrand is

```lean
ENNReal.ofReal (|x| ^ (-(2*c')))
  * ENNReal.ofReal ((frontU (Fin.insertNth p 0 y)) ^ (-c'))
```

so `setLIntegral_prod` gives the same pattern as `subBox121_diverges`, but with the whole rest block left intact. The local project lemma is exactly:

```lean
abs_rpow_lintegral_Ioo_eq_top (s ε : ℝ) (hε : 0 < ε) (hs : s ≤ -1)
```

defined in `Case222Cover.lean`, not Mathlib.

**2. Rest Factor Positivity**

A single witness point is not enough by itself: points have zero measure. You need either:

```lean
witness + continuity ⇒ positive-measure neighborhood where frontU > 0
```

or the polynomial route:

```lean
UPoly ≠ 0 ⇒ frontU ≠ 0 a.e. via MvPolynomial.ae_eval_ne_zero
```

For this certificate, the cleanest is witness plus continuity. Pick a rest witness `y₀` with

```lean
0 < frontU (Fin.insertNth p 0 y₀)
```

then shrink to a rest box `R` where `frontU > 0` everywhere. Then

```lean
rw [setLIntegral_pos_iff hUmeas]
```

and show `R ⊆ support`, so `0 < volume R` implies the rest integral is positive. You do not need bounded-away for positivity alone, but bounded-away is useful because the rate lemma is off-pole and containment needs control of `smearShift`.

**3. Containment**

The naive rest cube near the pole is not safe. `phiSm` changes only the pivot coordinate, but

```lean
(phiSm u) p = u p - smearShift u
```

so the source must bound `smearShift`.

Choose `R` around a rest witness with:

```lean
frontU > 0
smearShift = 0
all non-pivot coordinates small
```

Typically set deepest residual rows to `0`, so `smearShift = 0`, and choose front coordinates nonzero but scaled inside the `ε`-cube. Then shrink `R` so:

```lean
∀ y ∈ R, 0 < frontU (insertNth p 0 y)
∀ y ∈ R, |smearShift (insertNth p 0 y)| ≤ ε/4
∀ y ∈ R, all non-pivot coords are ≤ ε
```

Use `smearShift_update_pivot` to transfer this bound from `insertNth p 0 y` to `insertNth p x y`. With `x ∈ (0, ε/4)`,

```lean
|x - smearShift| ≤ |x| + |smearShift| < ε
```

and all other coordinates are unchanged, so `S ⊆ phiSm ⁻¹' cubeBox _ ε`.

**4. Biggest Risk**

The real wall is containment, specifically proving a uniform bound on `smearShift` on a positive-measure rest box. The Tonelli peel at opaque `p` is routine; the existing `piFinSuccAbove` pattern in `RouteM121Smeared`, `RouteM132Smeared`, and `RouteM231Smeared` already shows it. `U > 0` is also manageable by witness plus continuity.

What you likely need as a helper is a local rest-box lemma:

```lean
∃ R, MeasurableSet R ∧ 0 < volume R ∧
  (∀ y ∈ R, 0 < frontU (insertNth p 0 y)) ∧
  (∀ y ∈ R, |smearShift (insertNth p 0 y)| ≤ ε/4) ∧
  (∀ y ∈ R, rest coords bounded by ε)
```

Once that lands, the divergence proof is essentially the validated one-axis product peel with exponent `-2*c' ≤ -1`.