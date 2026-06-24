**Verdict**

Yes, the honest object is the chart trivialization

```lean
S ≃ₐ[R] R ⊗[k] F_E
```

but the cheaper way to build it is **not** to solve the total rank ideal by Schur/graph elimination in factor coordinates. Present the total chart as a **base change / graph ring**, then use endpoint row-column operations.

**Q1**

Let the target chart split the product matrix as

```text
B = [ Δ  P ]
    [ Q  B22 ]
```

with `Δ` invertible. In the rank-`≤ r` target chart,

```text
B22 = Q Δ⁻¹ P
R = k[Δ, P, Q, det(Δ)⁻¹].
```

Define

```text
L = [ Δ  0 ]          H = [ I  Δ⁻¹P ]
    [ Q  I ]              [ 0    I   ]

E = [ I 0 ]
    [ 0 0 ].
```

Then

```text
B = L E H.
```

For a tuple `A = (A₁,...,A_N)` over the chart, normalize only the endpoints:

```text
Ã₁ = A₁ H⁻¹
Ãᵢ = Aᵢ              for 1 < i < N
Ã_N = L⁻¹ A_N.
```

Then

```text
A_N ... A₁ = B    ⇔    Ã_N ... Ã₁ = E.
```

Conversely,

```text
A₁ = Ã₁ H
Aᵢ = Ãᵢ
A_N = L Ã_N.
```

So the factor coordinates are not “free vs forced” in the original coordinate system. The clean coordinates are:

```text
base:       Δ, P, Q, det(Δ)⁻¹
fibre:      normalized factor entries Ãᵢ, modulo mult(Ã)=E
```

The section exists: choose canonical rank-`r` maps `e_i : k^{d_{i-1}} → k^{d_i}` with an `I_r` in the pivot block and zero elsewhere, so `e_N ... e_1 = E`. Then for `N ≥ 2`,

```text
s(B)_1 = e₁ H
s(B)_i = eᵢ
s(B)_N = L e_N.
```

For Lean, the best presentation is:

```text
T = k[target entries]
P = k[factor entries]
R = target rank chart

S := P ⊗[T] R
   ≃ R[factor entries] / (mult(A) - B_univ)
```

Then the endpoint change above transports the ideal `(mult(A)-B_univ)` to `(mult(Ã)-E)`, giving

```text
S ≃ R[factor entries] / (mult(Ã)-E)
  ≃ R ⊗[k] F_E.
```

This avoids porting the G2-2 graph-ideal trick to product entries. The factoring phenomenon `det(A₂A₁)=det A₁ det A₂` is real, but it becomes a fibre relation, e.g. `ℓm=0`, not an obstruction.

**Q2**

The flatness chain is the right one:

```lean
e : S ≃ₐ[R] R ⊗[k] F_E
Module.Free R (R ⊗[k] F_E)      -- over a field, F_E is a free k-module
Module.Flat R S                 -- `Module.Flat.of_linearEquiv e.toLinearEquiv`
Algebra.HasGoingDown R S        -- instance from flatness
Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m_B P
```

The local probes already pin this API: tensor-product freeness and flatness transport are in [ChartFlatnessProbe.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:94), and the going-down height consumer is pinned at [ChartFlatnessProbe.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:76).

For `P` minimal over `m_B S`, the relative term is zero because the image of `P` in `S ⧸ m_BS` is a minimal prime. So

```text
height_S P = height_R m_B + 0 = δ.
```

That step is sound. But phrase it as “minimal over the fibre ideal”, not merely “minimal prime of `F_E`” until after transporting through `S ⧸ m_BS ≃ F_E`.

The flat-quasi-finite brick is not the right tool. The fibre is positive-dimensional, so `Algebra.QuasiFiniteAt R P` fails in the relevant cases; the local file [FlatQuasiFiniteHeight.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:71) is for zero-dimensional fibre behavior.

For `height m_B = δ`: correct, but in Lean do not rely on “regular dim `δ`” alone. Use the explicit presentation `R = Localization.Away detSchurS` of a polynomial ring in `δ` Schur variables, and prove the point maximal ideal has height `δ`.

One red-team caveat: adding the ambient `+ C` is not automatic from Brick A alone. You still need the minimal-prime/catenary/localization assembly: the fibre lies wholly in the chosen chart because the pivot minor evaluates to a nonzero scalar on `B`, and then quotient-height `δ` must be lifted over minimal primes of `Σ̄^r` of height `C`.

**Q3**

The explicit-equations/Jacobian reserve is not cleaner.

A full-rank Jacobian at one smooth point proves only a local statement for one component. It does not rule out larger-dimensional components elsewhere, which is exactly the danger in this reducible setting. Krull gives height upper bounds from generator counts, not the needed lower bound. And producing `C+δ` global equations is unrealistic: the product rank locus is not generally a complete intersection, and `C` comes from orbit-closure combinatorics, not from an explicit regular sequence.

The cheapest serious route is therefore:

```text
base-change graph presentation
→ endpoint normalization AlgEquiv
→ R ⊗ F_E
→ free/flat
→ going-down height additivity
→ reducible minimal-prime assembly for +C.
```

Estimate: relative chart flatness is a real 4-6 module build; the full ambient `C+δ` theorem with localization and minimal-prime bookkeeping is more like 7-10 modules. The hard wall is the explicit quotient/tensor `AlgEquiv`, not Mathlib’s flatness API.