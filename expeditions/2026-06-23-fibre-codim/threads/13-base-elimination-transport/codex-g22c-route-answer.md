Use **Q2-direct**, but prove the height by **localize the coordinate ideal, then translate**. This avoids both denominator mismatches.

Let

```lean
R  := MvPolynomial (SchurVar q p r) k
f  := detSchurS q p r
S  := Localization.Away f
P0 := MvPolynomial (B22block q p r) R
P  := MvPolynomial (B22block q p r) S
```

Define the real localized forced value in `S`:

```lean
forced b : S := algebraMap R S (forcedNum b) * (algebraMap R S f)⁻¹
-- or cleaner via IsLocalization.mk' S (forcedNum b) ⟨f, ...⟩
```

Then set

```lean
J' : Ideal P := graphIdeal forced
```

**Do not try to get `J'` as the localization of `graphIdeal forcedNum`.** That localizes to generators `X b - C (forcedNum b)`, not `X b - C (forcedNum b / f)`.

The clean height proof is:

1. In `P0`, use your landed theorem at `c = 0`:

```lean
height (Ideal.span (Set.range fun b => X b : Ideal P0)) = Nat.card B22block
```

equivalently `height_coordIdeal_eq`.

2. Localize this coordinate ideal along `R -> S`. `MvPolynomial.isLocalization` gives that `P` is the localization of `P0` at the image of powers of `f`.

3. Prove disjointness by evaluation at zero in the `B22` variables:

```lean
aeval (fun _ => 0) (C (f^n)) = f^n ≠ 0
```

so no power of `C f` lies in the coordinate ideal. You only need `detSchurS_ne_zero`, best proved by evaluating the Schur `Delta` variables at the identity matrix, giving determinant `1`.

4. Apply:

```lean
IsLocalization.height_map_of_disjoint
```

to get the localized coordinate ideal in `P` has height `#B22block`.

5. Now use a translation automorphism of `P`:

```lean
X b ↦ X b - C (forced b)
```

It maps the localized coordinate ideal to `graphIdeal forced`. Therefore `height_map_algEquiv` gives:

```lean
(J' : Ideal P).height = Nat.card (B22block q p r)
```

This is the key shim:

```lean
theorem height_graphIdeal_over_away
    (c : σ → S) :
    (graphIdeal c : Ideal (MvPolynomial σ S)).height = Nat.card σ
```

specialized to `S = Localization.Away detSchurS`.

So:

- **(2a)** is not the right route as stated: the forced graph ideal is not defined over the unlocalized ring. A cleared-denominator ideal is definable, but it is not a graph ideal and proving its height/prime behavior is extra friction.
- **(2b)** is also not right as stated: localizing the numerator graph ideal gives the wrong generators.
- **Best route:** define the graph ideal over `Sd` directly, prove its height by coordinate-ideal localization plus translation.

For the inclusion `J' ⊆ Iad'`, use the cleared relation from minors:

```lean
C f * X b - C (forcedNum b) ∈ Iad'
```

then multiply by the unit `C (algebraMap R S f)⁻¹` in `P` to get:

```lean
X b - C (forced b) ∈ Iad'
```

That handles the `detΔ⁻¹` honestly and locally.

Do **not** route through `ringKrullDim Sd = δ`. Localization can drop dimension in general, and even when this principal open has the expected dimension, proving that is unnecessary. You only need height preservation for one prime disjoint from the inverted element, which is exactly what `height_map_of_disjoint` gives.
