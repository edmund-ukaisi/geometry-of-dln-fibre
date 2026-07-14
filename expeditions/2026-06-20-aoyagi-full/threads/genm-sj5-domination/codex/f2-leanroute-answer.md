## Verdict

For (i), I would use route (c), but not by proving `Polynomial.roots` measurable. Encode an antitone root tuple by its Vieta coefficient vector and invert that map with Mathlib’s Lusin–Souslin theorem. At v4.29 the required measurable-embedding inverse API exists.

For (ii), explicit multiplicity-pattern strata are avoidable. A zero-safe global Lagrange projector plus sequential “first nonzero projected coordinate” gives a cleaner measurable eigenframe. Some finite pivot branching remains unavoidable.

### 1. Measurability of `eigenvalues₀`

My ranking is:

| Rank | Route | Estimated lines | Assessment |
|---|---|---:|---|
| 1 | (c′) Vieta map + Lusin–Souslin inverse | 450–900 | Best bet |
| 2 | (d1) direct one-sided spectral-count LSC | 500–900 | Good, especially with local bank |
| 3 | (a) Weyl bound from spectral counting | 600–1100 | Robust and reusable |
| 4 | (b) Ky Fan sums + LSC | 900–1600 | Sound but substantially more algebra |
| 5 | Countable dense min–max / inertia | 1200–2500+ | Poor Mathlib fit |

#### Recommended route: Vieta + Lusin–Souslin

Define

```lean
def OrderedRoots (n : ℕ) :=
  {r : Fin n → ℝ // Antitone r}

def vietaCoeff (r : OrderedRoots n) : Fin (n + 1) → ℝ :=
  fun k => (∏ i, (Polynomial.X - Polynomial.C (r.1 i))).coeff k
```

Then establish:

```lean
theorem measurable_vietaCoeff :
    Measurable (vietaCoeff : OrderedRoots n → Fin (n + 1) → ℝ)

theorem injective_vietaCoeff :
    Function.Injective (vietaCoeff : OrderedRoots n → Fin (n + 1) → ℝ)
```

The load-bearing v4.29 declarations are:

- `isClosed_antitone`
- `IsClosed.measurableSet`
- `MeasurableSet.standardBorel`
- `Measurable.measurableEmbedding`
- `MeasurableEmbedding.measurable_invFun`
- `MeasurableEmbedding.leftInverse_invFun`
- `Polynomial.prod_X_sub_C_coeff`
- `Finset.esymm_map_val`
- `Polynomial.roots_multiset_prod_X_sub_C`
- `Matrix.IsHermitian.eigenvalues₀_antitone`
- `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀`
- `Matrix.IsHermitian.splits_charpoly`
- `Matrix.charpoly_monic`
- `measurable_pi_lambda`

The proof architecture is:

1. `{r | Antitone r}` is closed in `Fin n → ℝ`, hence its subtype is standard Borel.
2. Rewrite each coefficient of the product using Vieta and `Finset.esymm_map_val`; it is a finite sum of finite products of coordinate maps, hence measurable.
3. Prove injectivity: equal coefficient vectors give equal monic polynomials, hence equal root multisets; sorting the multisets in decreasing order recovers `List.ofFn r`, because `r` is antitone.
4. Lusin–Souslin gives:

   ```lean
   have he : MeasurableEmbedding vietaCoeff :=
     measurable_vietaCoeff.measurableEmbedding injective_vietaCoeff
   ```

   Therefore `he.invFun` is measurable.
5. For a Hermitian `A`, the charpoly coefficient vector lies in the range, witnessed by `A.eigenvalues₀`. Thus

   ```lean
   he.invFun (charpolyCoeff A) =
     ⟨hA.eigenvalues₀, hA.eigenvalues₀_antitone⟩
   ```

6. Compose with the measurable charpoly coefficients and subtype coercion.

This genuinely avoids root continuity. It uses no KRN-style selection. The theorem `sort_roots_charpoly_eq_eigenvalues₀` is useful for the final identification, but supplies no regularity itself.

A good general standalone statement is:

```lean
theorem measurable_orderedRoots_of_vieta
    {X : Type*} [MeasurableSpace X]
    (c : X → Fin (n + 1) → ℝ) (hc : Measurable c)
    (r : X → Fin n → ℝ)
    (hr : ∀ x, Antitone (r x))
    (hv : ∀ x, c x = vietaCoeff ⟨r x, hr x⟩) :
    Measurable r
```

There is no circularity in using `eigenvalues₀` as the witness `r`: only its algebraic factorization and antitonicity are used before measurability is concluded.

#### Route (a): Weyl

This is the second proof I would retain as a fallback. Do not build Courant–Fischer first. Prove directly

```lean
|hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖
```

under `open scoped Matrix.Norms.L2Operator`.

The ingredients are:

- a strong spectral subspace of dimension at least `i + 1`;
- Rayleigh lower bound on that subspace;
- `|⟪x, (A-B)x⟫| ≤ ‖A-B‖ * ‖x‖²`, using `Matrix.toEuclideanCLM` and operator norm;
- the threshold-count dimension lemma;
- conversion between counts for `eigenvalues` and `eigenvalues₀`;
- `LipschitzWith.continuous`.

Much of this is already banked in [RouteMSJKyFan.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJKyFan.lean:43) and [RouteMSJShellContain.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJShellContain.lean:48). Those results are network-free mathematically but currently sit under a DLN import chain; a Core theorem should refactor them rather than import that chain.

#### Route (b): Ky Fan

The uncountable projection/frame index is acceptable. For `ℝ`, however, the relevant declaration is:

```lean
lowerSemicontinuous_ciSup
```

and it requires pointwise `BddAbove`. `lowerSemicontinuous_iSup` applies directly only to complete linear orders. No `Countable` assumption on the index is required. Do not use `Measurable.iSup`, which does require countability.

I would index by orthonormal `k`-frames

```lean
{Q : Matrix (Fin n) (Fin k) ℝ // Qᵀ * Q = 1}
```

and use `trace (Qᵀ * A * Q)`.

You do need, logically, the full Ky Fan value equality:

- every frame value is at most the sum of the top `k` eigenvalues;
- the first `k` spectral vectors attain equality.

No compactness/maximizer theorem is needed, but the hard weighted-eigenvalue inequality remains. Once equality is available, the LSC and difference-of-partial-sums argument is short.

#### Other routes

The direct threshold-LSC route is a useful Weyl-lite variant: if `λᵢ(A) > c`, choose `d` strictly between them, preserve a strong `(i+1)`-dimensional Rayleigh subspace under small operator-norm perturbations, and use the count lemma to obtain `λᵢ(B) ≥ d`. It saves the symmetric half of Weyl but introduces neighborhood/filter bookkeeping.

Countable dense min–max is unattractive: formalizing dense rational frames and preservation of the extremum costs more than the spectral-count proof.

An inertia/Sylvester characterization is also a poor fit. v4.29 lacks the needed inertia and sign-variation infrastructure; rebuilding it would resemble the stratification needed for (ii).

## 2. Measurable sorted orthogonal eigenframe

Explicit multiplicity-pattern stratification is not necessary. Use the global projector

```lean
F i j :=
  1 + (λ i - λ j)⁻¹ • (A - λ i • 1)

P i := ∏ j, F i j
```

with Lean’s total inverse `0⁻¹ = 0`.

On an eigenvector of eigenvalue `μ`:

- if `μ = λ i`, every factor acts as `1`;
- if `μ ≠ λ i`, choose `j` with `λ j = μ`; that factor acts as `0`;
- when `λ j = λ i`, the corresponding factor is automatically `1`.

Thus `P i` is the orthogonal projector onto the full `λ i`-eigenspace. It is globally measurable without an explicit equality-pattern partition.

Construct columns sequentially. If `U₍<i₎` contains the previously chosen columns and zeros elsewhere, put

```lean
S i := 1 - U₍<i₎ * U₍<i₎ᵀ
R i := P i * S i
v i := normalize (firstNonzeroColumn (R i))
```

Then:

- `R i` is the projector onto the part of the `λ i`-eigenspace orthogonal to the previous columns;
- multiplicity counting shows `R i ≠ 0`;
- some column of `R i` is nonzero;
- normalizing the first such column gives a canonical unit eigenvector;
- a fold over `List.finRange n` produces all columns.

This replaces both explicit multiplicity strata and per-block Gram–Schmidt. The remaining finite “first nonzero column” pivot is unavoidable: there is no continuous global eigenframe, so some discontinuous canonicalization must occur.

A correction of `eigenvectorUnitary` is not a shortcut. For repeated eigenvalues its ambiguity is a whole `O(m)` block. Proving a correction measurable requires reconstructing the eigenspace projector and a canonical basis anyway. Even for simple spectrum, sign normalization only helps after the eigenline has been expressed measurably from `A`.

A general measurable kernel selector followed by deflation is possible, but likely longer: v4.29 has little rank-by-minors API, so the selector would require a separate rank/minor/Gaussian-elimination stratification.

The main named lemmas should be:

```lean
measurable_lagrangeProjector
lagrangeProjector_mulVec_eigenvector
lagrangeProjector_idempotent
lagrangeProjector_transpose
range_lagrangeProjector_eq_eigenspace

measurable_firstNonzeroColumn
firstNonzeroColumn_ne_zero
normalize_firstNonzeroColumn_norm
normalize_firstNonzeroColumn_mem_range

partialEigenframe_measurable
partialEigenframe_orthonormal
partialEigenframe_eigenvector
residualProjector_ne_zero

canonicalEigenframe_measurable
canonicalEigenframe_transpose_mul_self
hermitian_eq_canonicalEigenframe_mul_diagonal
```

Prove the projector and recursion lemmas over abstract parameters `A`, `λ`, and an abstract eigenbasis. Instantiate with `hA.eigenvalues₀` only in thin terminal lemmas. The repository has already observed severe elaboration timeouts when heavy spectral definitions are inlined; `set` is insufficient, while abstract `...Aux` lemmas and syntactic `rw` work.

## 3. Scope and module cuts

Estimated compiled Lean:

| Brick | Lines |
|---|---:|
| Ordered roots, Vieta embedding, measurable inverse | 350–700 |
| Charpoly coefficients → measurable `eigenvalues₀` | 100–250 |
| Global Lagrange projectors | 400–800 |
| Measurable first-nonzero-column selector | 150–350 |
| Finite frame fold and invariants | 800–1600 |
| Orthogonality and diagonalization assembly | 200–400 |
| Integration/refactoring friction | 200–400 |
| **Total** | **2200–4500** |

A literal multiplicity-stratified, block-Gram–Schmidt implementation is more plausibly 3500–6000 lines.

This is a multi-module effort, not one tide. I would land, in order:

1. `Core/Matrix/OrderedRootsMeasurable.lean` — standalone Vieta/Lusin–Souslin theorem.
2. `Core/Matrix/HermitianEigenvaluesMeasurable.lean` — conjunct (i), complete and reusable.
3. `Core/Matrix/MeasurablePivot.lean` — generic finite first-nonzero-coordinate selector.
4. `Core/Matrix/HermitianSpectralProjector.lean` — zero-safe global projectors.
5. `Core/Matrix/MeasurableEigenframe.lean` — recursive canonical frame.
6. `Core/Matrix/MeasurableEigendecomp.lean` — theorem-level assembly.

The first brick is the best sorry-free bedrock target: it is independent of spectral linear algebra and resolves conjunct (i)’s principal uncertainty immediately.