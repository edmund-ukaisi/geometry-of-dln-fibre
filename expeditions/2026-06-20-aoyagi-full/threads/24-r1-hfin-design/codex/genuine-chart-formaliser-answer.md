**Verdict**

`pivot=a` with exactly 7 active flat coordinates does **not** work. The clean lower-bound architecture is instead:

- use the divergence pivot `u = T₁`, not the flat `a` slot;
- active 7 coords: `T₂,T₃,T₄,D₁₁,D₁₂,D₂₁,D₂₂`;
- avoid `a⁻¹` by writing `b = a β`;
- accept Jacobian `|a|² |u|⁷`, then restrict `a ∈ [αε,βε]` for each cube so `|a|²` is just a harmless unit for the lower bound.

Concretely, set `β : 1×2`, `c : 2×1`, `S : 2×4`, `Δ : 2×2`, `v=(1,τ) : 1×4`, and define the pole-free chart

```text
A = [ a      aβ
      c   cβ + uΔ ]

C = [ u v - βS
          S     ].
```

Then

```text
AC = u · [ a v
           c v + ΔS ],
```

so

```text
F ∘ Φ = u^2 · U,
U = ‖[a v ; c v + ΔS]‖²,
```

and `U ≥ a²` because the first component of `v` is `1`.

The Jacobian is

```text
|det DΦ| = |a|² |u|⁷.
```

This is the original Schur chart with `b=aβ`; clearing the `a⁻¹` pole moves the missing factor into the Jacobian. On an `ε`-cube lower-bound slice, take `a ∈ [αε,βε]`, so `|a|²` is bounded above and below by positive constants depending on `ε`. The only divergent exponent is still

```text
u^(7 - 2c')
```

which diverges at `c' ≥ 4`.

**Why `pivot=a` Fails**

If `pivotBlowupOn` uses the flat coordinate `a=A₁₁` as pivot with only 7 other active flat coords, then at `a=0` those 7 active coords vanish and the remaining 13 spectators are free. For `F∘Ψ` to be divisible by `a²`, `AC` must vanish identically on that coordinate subspace.

For each inner index `j`, you must kill either the whole `j`-th column of `A` or the whole `j`-th row of `C`; otherwise some product `Aᵢⱼ Cⱼₖ` survives.

Costs beyond the pivot `a=A₁₁`:

```text
j=1: need c₁,c₂ or y₁..y₄          cost min(2,4)=2
j=2: need A column 2 or C row 2     cost min(3,4)=3
j=3: need A column 3 or C row 3     cost min(3,4)=3
```

Minimum is `2+3+3 = 8` active coords. So 7 is impossible. If you scale all other `A` entries by `a`, you get determinant `a⁸`, not `a⁷`.

**Lean Architecture**

Reuse `pivotBlowupOn`, but not as “pivot is the `a` slot with 7 actives.”

Use it in two stages:

1. Center-ratio cleanup: `(a,β) ↦ (a,b=aβ)`, determinant `|a|²`.
2. Normal blow-up: `(u,τ,Δ) ↦ (T=u(1,τ), D=uΔ)`, determinant `|u|⁷`.

The remaining shear

```text
y = T - βS
E = cβ + D
```

has determinant `1`.

For the lower bound, a full Hironaka atlas is unnecessary. A measure-zero curve is not enough, but this full-dimensional horn is. For each `ε>0`, restrict parameters so the image lies in `(-ε,ε)^21`, with `a` in a small interval comparable to `ε` and `u∈(0,ηε)`. Then apply image change-of-variables on `{a≠0,u≠0}` and reduce by Tonelli/Fubini to

```text
∫₀ u^(7 - 2c') du = ∞
```

for `c' ≥ 4`.

So: avoid the pole with `b=aβ`; keep the honest codimension in the `u`-pivot; do not try to make the flat `a` slot be the 7-active pivot.