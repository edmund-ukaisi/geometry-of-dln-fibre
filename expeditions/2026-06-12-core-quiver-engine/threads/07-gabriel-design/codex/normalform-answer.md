**A. RECOMMENDED ROUTE**

Use **(b)+(d) hybrid**: induction on total dimension, peeling one leftmost-born interval, with the splitting proved by a kernel/preimage complement lemma.

This is cleanest to formalise because it avoids classifying automorphisms of an already decomposed prefix. Route **(a)** forces a parabolic Gaussian elimination at the last vertex. Route **(c)** is a good normal-form output but a costly proof driver. Route **(d)** via full kernel/image filtrations computes barcodes elegantly, but quotient-filtration bookkeeping is heavier than needed. The peeling proof uses only finite-dimensional linear algebra.

**B. THE INDUCTIVE STATEMENT**

Prove a strengthened “barcode basis” theorem for arbitrary finite-dimensional vector spaces, then specialise to matrices.

For fixed `N`, induct on

```text
D(V) = sum_{t=0}^N finrank_k V_t.
```

Statement:

For every chain

```text
V_0 --f_1--> V_1 --f_2--> ... --f_N--> V_N
```

there is a finite label set `Λ`, birth/death functions

```text
b,e : Λ -> {0,...,N},    b(λ) <= e(λ),
```

and for each vertex `t` a basis of `V_t` indexed by

```text
Λ_t = { λ | b(λ) <= t <= e(λ) },
```

such that for every edge `f_t : V_{t-1} -> V_t`:

```text
f_t(v_{t-1,λ}) = v_{t,λ}     if b(λ) <= t-1 < t <= e(λ),
f_t(v_{t-1,λ}) = 0           if e(λ) = t-1.
```

This basis is exactly a direct sum of interval modules. In the matrix encoding, if `Q_t` has these basis vectors as columns, then

```text
Q_t^{-1} A_t Q_{t-1}
```

is the interval block normal form. With your group-action convention, take `P_t = Q_t^{-1}`.

**C. THE INDUCTIVE STEP**

Assume `D(V) > 0`. Let `s` be the least vertex with `V_s ≠ 0`. Choose `v_s ≠ 0`. Define the forward trajectory

```text
v_t = f_t f_{t-1} ... f_{s+1}(v_s)   for t >= s.
```

Let `j` be the largest index with `v_j ≠ 0`. Then `v_t ≠ 0` for `s <= t <= j`, and if `j < N`, then `f_{j+1}(v_j)=0`.

Key splitting lemma:

**FACT.** If `f : V -> W`, `f v = w ≠ 0`, and `W = k w ⊕ U`, then

```text
V = k v ⊕ f^{-1}(U).
```

Proof: if `c v ∈ f^{-1}(U)`, then `c w ∈ U`, hence `c=0`. For any `x`, decompose `f x = c w + u`; then `x = c v + (x-cv)` with `x-cv ∈ f^{-1}(U)`.

Use it backwards. Choose a complement

```text
V_j = k v_j ⊕ U_j.
```

For `t = j, j-1, ..., s+1`, define

```text
U_{t-1} = f_t^{-1}(U_t).
```

For `t > j`, set `U_t = V_t`; for `t < s`, `V_t = 0` by minimality of `s`.

Then

```text
V_t = k v_t ⊕ U_t     for s <= t <= j,
V_t = U_t             otherwise,
```

and the `U_t` form a subrepresentation. The line chain spanned by the `v_t` is an interval module `M_{s j}`. The complement chain `U_*` has strictly smaller total dimension, so apply the induction hypothesis to `U_*`, then add one new barcode label with birth `s` and death `j`.

The single hardest formal step is the indexed backward construction `U_{t-1}=f_t^{-1}(U_t)` together with the proof that each `V_t = k v_t ⊕ U_t`. It is linear algebra, but the `Fin`/inequality bookkeeping is the nuisance.

**D. UNIQUENESS**

Once existence is known, uniqueness is essentially free.

For a direct sum with multiplicities `m_{ab}`, the composite

```text
A_j ... A_{i+1} : V_i -> V_j
```

has rank contribution `1` from exactly those interval summands `M_{ab}` with

```text
a <= i <= j <= b.
```

Therefore

```text
rank_pattern(⊕ M_{ab}^{m_ab})_{ij}
  = sum_{a <= i <= j <= b} m_ab
  = S(m)_{ij}.
```

Since rank pattern is base-change invariant, any decomposition of `A_*` has `S(m)=r(A_*)`. Applying the already-formalised inverse `T` gives

```text
m = T(r(A_*)).
```

Thus multiplicities are unique, and equal rank patterns imply isomorphic normal forms.

**E. PROVE-vs-CITE**

- **PROVE**: the peeling/splitting lemma. It is short and type-A-specific.
- **PROVE**: the total-dimension induction. This is the core normal-form existence proof.
- **PROVE**: rank pattern of interval sums equals `S(m)`. It is just block-rank additivity.
- **PROVE**: completeness of rank pattern using `S`/`T`. Already nearly immediate from your API.
- **CITE/USE Mathlib**: existence of complements for subspaces of vector spaces. Do not reprove.
- **CITE/USE Mathlib**: basis extension / basis from a complemented subspace. Routine library material.
- **DO NOT FORMALISE** Krull-Schmidt or general Gabriel theorem for this target. Too much category-theory cost for no benefit here.
- **DO NOT DRIVE BY** Smith/staircase normal form. It creates algorithmic matrix bookkeeping you do not need.

**F. MATHLIB LEVERS**

- **FACT / standard API shape**: `LinearMap.ker`, `LinearMap.range`, `Submodule.comap`, `Submodule.map` are the right language for kernels, images, and preimages.
- **INFERENCE**: Mathlib likely has `Submodule.exists_isCompl` or equivalent complement-existence lemmas over fields/division rings.
- **INFERENCE**: Mathlib likely has finrank lemmas for complements: if `IsCompl U W`, then `finrank V = finrank U + finrank W`.
- **INFERENCE**: singleton-span facts such as `finrank (span {v}) = 1` when `v ≠ 0` should exist, perhaps under a nearby name.
- **INFERENCE**: use `Basis` APIs to concatenate a basis of `U_t` with the vector `v_t` under an `IsCompl` proof.
- **RECOMMENDATION**: avoid depending on a partial-permutation matrix library. The interval matrices are partial permutations as an output, but the proof only needs adapted bases and change-of-basis matrices.