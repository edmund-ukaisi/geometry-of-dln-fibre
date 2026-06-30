**Q1**

Yes. The clean route is a **gauge-fixed tangent-space injection**, not `S_row ⊔ S_col`.

Take a rank factorization

```text
B = v⁰ v¹ = U W
U : H0 × r,     W : r × H2,
rank U = r,     rank W = r.
```

Because `B = v⁰ v¹`, choose lifts

```text
U = v⁰ C        with C : H1 × r,
W = K v¹        with K : r × H1.
```

Because `U` has full column rank and `W` has full row rank, choose one-sided inverses

```text
Λ U = I_r       with Λ : r × H0,
W Ρ = I_r       with Ρ : H2 × r.
```

Now define

```text
T(X,Y) = X W + U Y
       = (X K) v¹ + v⁰ (C Y),
```

so every `T(X,Y)` lies in `range Dg`.

Instead of taking all `(X,Y)`, restrict to the gauge slice

```text
Λ X = 0.
```

So use the domain

```text
G := { X : Mat(H0 × r) | Λ X = 0 } × Mat(r × H2).
```

The map

```text
Ψ : G → range Dg,
Ψ(X,Y) = X W + U Y
```

is injective:

```text
X W + U Y = 0
Λ(X W + U Y) = 0
(Λ X) W + (Λ U) Y = 0
0 + Y = 0
Y = 0
X W = 0
X W Ρ = 0
X = 0.
```

So

```text
finrank G ≤ finrank range Dg.
```

Finally,

```text
finrank {X | ΛX = 0} = H0*r - r*r
```

because `X ↦ ΛX` is surjective onto `Mat(r × r)`, with right inverse `Z ↦ UZ`. Hence

```text
finrank G
= (H0*r - r*r) + r*H2
= r*(H0 + H2 - r)
= nReg.
```

This gives the desired lower bound without computing `S_row ∩ S_col`.

**Mathlib status:** the rank-as-finrank-range facts and basic matrix-rank lemmas exist in Mathlib’s matrix rank API; exact lemma names may differ at v4.29, verify locally. The docs list `Matrix.rank`, `Matrix.rank_eq_finrank_range_toLin`, `Matrix.rank_eq_finrank_span_cols`, `Matrix.rank_eq_finrank_span_row`, and rank multiplication bounds. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Rank.html))

**Q2**

Use neither the disjoint union family nor the quotient-overlap domain.

The clean Lean object should be:

```text
G = ker (X ↦ Λ X) × Mat(r × H2)
```

and then an injective linear map

```text
G →ₗ[ℝ] range Dg.
```

This avoids:

```text
(A) ∪ (B) with overlap removed,
Mat(H0×r) ⊕ Mat(r×H2) / Mat(r×r),
finrank_sup,
explicit basis indexing by Fin nReg.
```

For the final inequality, it is enough to prove:

```text
finrank G = nReg
```

and then use the standard “injective linear map gives finrank inequality” route. If the exact lemma name is annoying, take a basis of `G`, push it forward by the injective map, and use linear independence in `range Dg`.

**Q3**

Your full map

```text
Φ : Mat(H0×r) × Mat(r×H2) → Mat(H0×H2),
Φ(X,Y) = X K v¹ + v⁰ C Y = XW + UY
```

does have rank exactly

```text
H0*r + r*H2 - r*r.
```

The kernel is exactly

```text
ker Φ = { (-U Z, Z W) | Z : Mat(r×r) }.
```

Proof: if `XW + UY = 0`, then

```text
X + UYΡ = 0          by right-multiplying by Ρ,
Y + ΛXW = 0          by left-multiplying by Λ.
```

Let `Z = YΡ`. Then

```text
X = -U Z,
Y = Z W.
```

Conversely, `(-UZ)W + U(ZW) = 0`.

But for the lower bound, do not formalize this unless you want the exact image dimension. The kernel computation is the overlap computation in disguised form. It is easier than `S_row ∩ S_col` because `Λ` and `Ρ` make it explicit, but the gauge-slice injection from Q1 is still cleaner.

**Q4**

Cheapest first:

1. **Better route: gauge-fixed injection.**  
   Domain `ker (X ↦ ΛX) × Mat(r×H2)`; map `(X,Y) ↦ XW + UY`; injectivity by multiplying on the left by `Λ` and on the right by `Ρ`. This proves only the lower bound and avoids overlap deletion.

2. **Route (iii): full `ι_A ⊕ ι_B` map with kernel parametrized by `Z`.**  
   Formalizable and algebraically clean, but it proves more than needed and still asks you to identify a kernel of dimension `r²`.

3. **Route (i): explicit `(A) ∪ (B)` family.**  
   Mathematically fine, but Lean-expensive: disjoint indexing, overlap removal, coefficient bookkeeping, and extensional matrix equalities.

4. **Route (ii): `finrank_sup` for `S_row + S_col`.**  
   Avoid unless you already have a strong reusable lemma for the intersection. Computing  
   `S_row ∩ S_col = colspace(v⁰) ⊗ rowspace(v¹)`  
   is the hard part.

Named trap: **the intersection-dimension trap**. If the proof starts requiring a general lemma about matrices whose rows lie in one subspace and columns lie in another, stop after three serious attempts and switch to the gauge-fixed injection.