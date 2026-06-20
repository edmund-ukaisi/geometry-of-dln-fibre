**A1 — Criterion**

Let `K = Frac(B)` and `F = Frac(A) = k(f_1,...,f_n) ⊆ K`. By definition `trdeg_k(A) = trdeg_k(F)`.

Since `B = S^{-1}k[x_1,...,x_M]`,

```text
Ω_{B/k} ≅ ⊕_j B dx_j,
Ω_{K/k} ≅ K ⊗_B Ω_{B/k} ≅ ⊕_j K dx_j.
```

Thus

```text
df_i = Σ_j (∂f_i/∂x_j) dx_j
```

in `Ω_{K/k}`, so the `K`-rank of `{df_i}` is exactly the row rank of the Jacobian matrix `J = (∂f_i/∂x_j)` over `K`. This part is characteristic-free.

Key field-differential lemma, in the form needed here:

If `E/k` is purely transcendental with basis `t_1,...,t_r`, then `Ω_{E/k}` is free over `E` with basis `dt_1,...,dt_r`. This follows from the polynomial-ring basis and localization.

If `L/E` is separable algebraic, then

```text
L ⊗_E Ω_{E/k} → Ω_{L/k}
```

is an isomorphism. Proof: for `L = E(α)` with separable minimal polynomial `p`, every `k`-derivation `D : E → M` extends uniquely by

```text
D(α) = -D(p)(α) / p'(α),
```

and `p'(α) ≠ 0` is exactly separability. Then use towers/filtered colimits.

Hence if `L/E` is separably generated, the same map is injective. In characteristic `0`, all algebraic extensions appearing here are separable, so this injectivity is automatic.

Now choose a maximal algebraically independent subfamily

```text
f_{i_1},...,f_{i_r}
```

among the finite set `{f_1,...,f_n}`. Then every other `f_j` is algebraic over

```text
E = k(f_{i_1},...,f_{i_r}),
```

so `F/E` is algebraic and `r = trdeg_k(F)`.

Lower bound: `Ω_{E/k}` has basis `df_{i_1},...,df_{i_r}`. Since `K/E` is separably generated in characteristic `0`, the map

```text
K ⊗_E Ω_{E/k} → Ω_{K/k}
```

is injective. Therefore `df_{i_1},...,df_{i_r}` remain `K`-linearly independent in `Ω_{K/k}`. Hence

```text
trdeg_k(A) = r ≤ rank_K span(df_1,...,df_n).
```

Upper bound: for `j ∉ {i_1,...,i_r}`, let `p(T) ∈ E[T]` be the minimal polynomial of `f_j`. In characteristic `0`, `p'(f_j) ≠ 0`. Differentiating `p(f_j)=0` gives

```text
0 = d(p(f_j)) = p'(f_j) df_j + terms in the E-span of df_{i_1},...,df_{i_r}.
```

After dividing by `p'(f_j)`, `df_j` lies in the `K`-span of the chosen `df_{i_a}`. Thus the whole span has rank at most `r`.

Therefore, in characteristic `0`,

```text
trdeg_k k[f_1,...,f_n]
= rank_K span(df_1,...,df_n)
= generic rank of J.
```

Equivalently, for a finite family `y_a ∈ K`, in characteristic `0`:

```text
{y_a} algebraically independent over k
⇔
{dy_a} K-linearly independent in Ω_{K/k}.
```

The characteristic-zero/separability point is essential. In characteristic `p`, with `B = k[x]` and `f = x^p`, one has `trdeg_k k[x^p] = 1` but `df = d(x^p) = 0`, so the generic Jacobian rank is `0`.

**A2 — Homogeneity**

Let `ρ : G → GL(V)` be the linear action, so `Q • v = ρ(Q)v`, and assume

```text
μ(QP) = ρ(Q) μ(P).
```

For fixed `Q`, write `L_Q(P)=QP`. Then

```text
μ ∘ L_Q = ρ(Q) ∘ μ.
```

Differentiating at `P` gives

```text
dμ_{QP} ∘ d(L_Q)_P = ρ(Q) ∘ dμ_P.
```

Both `d(L_Q)_P` and `ρ(Q)` are vector-space isomorphisms, so

```text
rank(dμ_{QP}) = rank(dμ_P).
```

Taking `Q = RP^{-1}` shows the rank is independent of `P`. This uses only equivariance plus invertibility; characteristic `0` is not used. Smoothness is not needed for this pointwise tangent-rank equality, although it is needed for the usual vector-bundle/generic-rank interpretation.

For the generic statement, assume `G` is smooth irreducible affine, with coordinate domain `k[G]`, and let `K_G = Frac(k[G])`. Left translation trivializes the tangent bundle:

```text
T_PG ≅ d(L_P)_e Lie(G).
```

Differentiating

```text
μ ∘ L_P = ρ(P) ∘ μ
```

at `e` gives

```text
dμ_P ∘ d(L_P)_e = ρ(P) ∘ dμ_e.
```

At the generic point `η`, the generic differential matrix is therefore

```text
ρ(η) · dμ_e
```

after left-trivializing `TG`. Since `ρ(η)` is invertible over `K_G`,

```text
generic rank(dμ) = rank_k(dμ_e : Lie(G) → V).
```

Thus the Jacobian generic rank equals the rank at the identity. We need `G` smooth so `TG` is a vector bundle and `Lie(G)=T_eG` has the expected meaning; connected smooth affine gives irreducibility/domain in the usual algebraic-group setting.

Split of dependencies:

```text
trdeg = generic Jacobian rank
```

is the separability-sensitive fact; characteristic `0` guarantees it. In characteristic `p`, Frobenius can kill differentials.

```text
generic rank = rank at e by homogeneity
```

is characteristic-free for smooth groups and equivariant maps. It can hold in characteristic `p` even while `trdeg = generic rank` fails; e.g. `G_m` acting on `A^1` by the character `t ↦ t^p` has orbit map `μ(t)=t^p`, constant differential rank `0`, but image dimension `1`.

**A3 — Formalisation Sizing**

This is not a one-lemma job. I would decompose it into roughly 8 genuinely distinct lemmas:

1. finite maximal algebraically independent subfamily of `{f_i}` has size `trdeg_k k(f_i)`;
2. `Ω_{k(t_1,...,t_r)/k}` has basis `dt_i`;
3. separable algebraic extensions preserve differentials: `L ⊗_E Ω_{E/k} ≃ Ω_{L/k}`;
4. separably generated extensions give injectivity on differentials;
5. char-zero finite-family theorem: `AlgIndependent y ↔ LinearIndependent K (dy)`;
6. finite-family rank theorem: `rank span(d f_i) = trdeg_k k(f_i)`;
7. localization/polynomial-coordinate lemma: `df_i` has coordinates `pderiv f_i`, so differential rank equals Jacobian matrix rank;
8. equivariant-map lemma: `dμ_P` is conjugate to `ρ(P) dμ_e`, hence generic rank equals identity rank.

The single hardest piece is 3-6 as a package: differential theory of finitely generated field extensions, especially the separable algebraic extension step and its use to bridge `AlgebraicIndependent`/`trdeg` with linear independence of Kähler differentials.

Verdict on the “secret” dependency: the inequality `trdeg ≤ generic Jacobian rank` does not logically require proving the full theorem `dim_L Ω_{L/k} = trdeg_k L` for every field extension. But it does require the core half of that theory: `Ω` of a rational function field plus injectivity after separably generated extension. In practice, if Mathlib lacks the field-extension `Ω`/`trdeg` bridge, this pulls in a real chunk of infrastructure, not a small wrapper lemma.

**A4 — Bottom Line**

Yes: the bound `trdeg ≤ rank δ⁰` is sound if `rank δ⁰` is the generic Jacobian/differential rank over the function field, or if homogeneity proves that this generic rank equals the rank computed at the identity. It is not sound for an arbitrary special point. The most likely naive formalisation break is silently using pointwise rank where generic rank is needed, or assuming `AlgIndependent ↔ LinearIndependent differentials` without first proving the separability/injectivity lemmas for Kähler differentials of field extensions.