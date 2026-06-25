**1. Choice**

Use **C: Schur-complement coordinates, then an 8-normal-coordinate pivot blowup**. This is the soundest route because it keeps the change of variables equidimensional, gives the exact `u^7` Jacobian, and gives an exact `F = u^2 * U` factorization on a positive-measure full-dimensional tube. Raw-entry fixes A and B both fail for the reason you identified: the needed rank-one slice is not a raw coordinate tube.

**2. Why raw embedding/tube A does not work**

In raw coordinates, thickening the fixed slice breaks the factorization. Write

```text
A = [ a  b ]
    [ c  E ]

C = [ y ]
    [ S ]
```

with `b` the top cross strip. Then

```text
AC_top = a y + b S.
```

If `y = u Tbar` but `b` and `S` vary in a positive-measure box, the term `b S` is not divisible by `u`. So `F = u^2 U` does **not** survive replacing `b = 0` by `b ∈ [-η,η]`. The exact slice `b = 0` has measure zero, and restricting `|b| ≤ O(u)` changes the Jacobian/weight, so it is not the desired finite positive Fubini factor.

**3. Clean reconciliation**

Use the local rank-one chart with pivot minor `a = A₀₀ ≠ 0`:

```text
T := y + a⁻¹ b S
D := E - c a⁻¹ b
```

Equivalently,

```text
y = T - a⁻¹ b S
E = D + c a⁻¹ b.
```

Then exactly

```text
AC = [ a T       ]
     [ c T + D S ].
```

Now blow up the 8 normal coordinates `(T,D)`:

```text
T = u (1, τ₁, τ₂, τ₃)
D = u Δ
```

where the pivot is a normalized top-row coordinate of `T`, not a raw `C` entry. Then

```text
F ∘ Ψ = u^2 * U

U = ‖a (1,τ)‖² + ‖c (1,τ) + Δ S‖².
```

On a box with `a` bounded away from `0`, `U ≥ a_min^2 > 0`, and `U` is bounded above on a compact box. The Schur chart has determinant `1` in these coordinates, and the pivot blowup on the 8 normal coordinates has determinant `u^7`, so the composite equidimensional chart has exactly the desired Jacobian.

Counting note: with your convention `det = u^(|active|-1)`, the active set should have size `8` **including** the pivot, so this is `u + 7` ratio coordinates plus `13` spectator coordinates.

**4. Honest Lean fallback**

The theorem is still achievable. The minimal honest `sorry` is not the divergence argument; it is one local chart lemma asserting the Schur-blowup properties:

```text
∃ Ψ U box C c₀,
  MapsTo Ψ box (cubeBox 21 ε) ∧
  |det fderiv Ψ| = u^7 ∧
  F (Ψ x) = u^2 * U x ∧
  c₀ ≤ U x ∧ U x ≤ C ∧
  0 < c₀
```

with `Ψ` given by the formulas above. After that, the existing equidimensional c-o-v lemma and the monomial leaf atom prove divergence at `c' ≥ 4`: the integrand is bounded below by a positive constant times `u^(7 - 2c')`, whose `u`-integral diverges at `c' = 4` and above.