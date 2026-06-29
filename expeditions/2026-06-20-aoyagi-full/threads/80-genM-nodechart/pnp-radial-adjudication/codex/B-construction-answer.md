**Q1**

Yes in spirit, but I would not call it `phi ∘ section` unless “section” means a formula-level re-interpretation of slots. As an actual map `R^N -> R^N`, a section of `pivotBlowupOn active p` would need `y_i / y_p` on active coordinates, so it is not global and not division-free.

The clean definition is:

```lean
β x := pivotBlowupOn active p x

B y := the same de-radialized chart formula as phi,
       with every radial active monomial x p * x i read as y i,
       pivot read as y p,
       spectators read as y j.
```

Polynomial-level version:

```lean
-- For each output k, choose/define P k in variables y
-- such that evaluating P k at β x gives phi x k.
def B (y : Fin N -> R) : Fin N -> R :=
  fun k => eval y (P k)
```

The key Lean obligation is the map identity:

```lean
theorem phi_eq_B_comp_blowup :
  ∀ x, phi x = B (pivotBlowupOn active p x)
```

or componentwise:

```lean
∀ x k, phi x k = B (pivotBlowupOn active p x) k
```

This is the irreducible proof: each coordinate polynomial of `phi` factors through the blow-up slot map. No inverse of blowup should appear.

**Q2**

Yes. Once you have

```lean
phi = B ∘ β
```

and differentiability of both maps, the determinant factorization is just chain rule plus determinant multiplicativity:

```lean
hβ : HasFDerivAt β Dβ u
hB : HasFDerivAt B DB (β u)

hcomp : HasFDerivAt (B ∘ β) (DB.comp Dβ) u :=
  hB.comp u hβ
```

Then transport across `phi_eq_B_comp_blowup`, identify `fderiv`, and use:

```lean
LinearMap.det_comp DB Dβ
```

giving:

```lean
det (Dphi u) = det (DB (β u)) * det (Dβ u)
```

This is division-free and valid at `u p = 0`. `LinearMap.det_comp` does not require either linear map to be invertible, and the Frechet derivative of the pivot blowup exists at the degenerate locus. The zero determinant at `u p = 0` is exactly allowed.

Lean obligations:

```lean
HasFDerivAt β Dβ u
HasFDerivAt B DB (β u)
phi = B ∘ β
det Dβ = (u p) ^ (active.card - 1)
```

plus the usual `fderiv` uniqueness rewrites if the final statement is phrased using `fderiv`.

**Q3**

Ranked recommendation, least-cast first:

1. **Direct two-factor route: `phi = B ∘ blowup`.**  
   Define `B` directly on `(Fin N -> R)` by the de-radialized polynomial/formula. Then prove one map equality and apply one `det_comp`.

   Irreducible obligations:
   ```lean
   phi = B ∘ pivotBlowupOn active p
   |det DB| = engine product
   det D(pivotBlowupOn active p) = x_p^(|active|-1)
   ```
   This is the cleanest if `B` can be written in ambient `Fin N` coordinates without rebuilding the global staircase.

2. **`composeFold` for `B` as the non-radial factors.**  
   Good if the engine determinant theorem is already banked there. But the cost is lifting/conjugating each small-space boundary factor into a full ambient `ChartFactor`.

   Irreducible obligations:
   ```lean
   B = composeFold engineFactors
   each lifted factor has the expected HasFDerivAt
   each lifted factor has the expected determinant
   product simplification gives the engine product
   phi = B ∘ radialFactor
   ```

   This is still local cast work, usually much lighter than one global staircase equivalence.

3. **Global `stairMap` conjugacy.**  
   Mathematically faithful, but likely most cast-heavy.

   Irreducible obligation:
   ```lean
   hconj :
     fderiv R phi u =
       e.symm.toContinuousLinearMap ∘L
       stairMap V (L+1) f c ∘L
       e.toContinuousLinearMap
   ```

   This forces the whole derivative value into one globally regrouped coordinate equivalence over opaque widths. That is exactly the expensive part.

So: proof-level, the two-factor argument is completely valid and division-free. Engineering-level, the least-cast route is direct ambient `B` plus one `det_comp`; use `composeFold` only to prove `|det DB|` if that is where the engine determinant is already available. The global `stairMap` route should be last unless its `hconj` is already essentially proven.