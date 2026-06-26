1. **NESTED COVER SOUNDNESS: NEEDS-CARE**

**PROVEN:** As a finite set-theoretic cover, the descent is sound and does not need the theorem “rank = maximal nonzero minor.” For each matrix, either some `k`-minor is nonzero, or all `k`-minors are zero and the matrix belongs to the next level. Since the original `R` has a pinned nonzero entry, the descent reaches level `1`; no point escapes.

**NEEDS-CARE:** If you recurse on a Schur complement `Sc`, that residual block no longer has a pinned nonzero entry. So termination cannot rely on the original pin. You need either:

- a zero-residual leaf, or
- the statement that the complement `{all entries of Sc = 0}` is null in the residual Euclidean coordinates and may be dropped for integration.

That is not the rank theorem, but it is a separate measure-theoretic endpoint.

2. **ARGMAX OVER MINORS: CORRECT for cover, NEEDS-CARE for disjointness**

**PROVEN:** `Finset.exists_max_image` does not care that the functions are linear coordinates. It works for any finite family of real-valued functions. So applying the coordinate argmax cover to

```lean
R ↦ det (minor R I J)
```

is mathematically valid. The cells are preimages of ordinary argmax cells under the measurable/continuous polynomial minor map.

**NEEDS-CARE:** A.e.-disjointness is not automatic from `exists_max_image`. Tie sets are

```text
|det minor_a| = |det minor_b|
```

equivalently

```text
(det minor_a)^2 - (det minor_b)^2 = 0.
```

In the full matrix space this is a proper algebraic hypersurface for distinct minors, hence null. But formalising “proper polynomial zero set is null” may be expensive. Cleaner fix: impose a deterministic tie-break order and make genuinely disjoint measurable cells. Then you do not need nullity of tie loci at all.

3. **COMPARISON vs EQUALITY: CORRECT**

**PROVEN:** The clean equality of Frobenius norms is false in general. From

```text
L R U = blockdiag(M11, Sc)
```

and `S = U (P,Q)`, one gets

```text
R S = L⁻¹ (M11 P, Sc Q).
```

Since `L` is usually non-orthogonal, Frobenius norm is only comparable, not equal.

If `A = M21 M11⁻¹` is uniformly bounded, then

```text
c0 (‖M11 P‖² + ‖Sc Q‖²)
≤ ‖R S‖²
≤ c1 (‖M11 P‖² + ‖Sc Q‖²)
```

with constants depending only on `r`. Such a bounded sandwich preserves the integrability threshold because for `c' > 0`,

```text
c1^(-c') D^(-c') ≤ ‖RS‖^(-2c') ≤ c0^(-c') D^(-c').
```

**NEEDS-CARE:** This comparison does not by itself turn `‖M11 P‖²` into a uniform Euclidean Morse block `‖P‖²`. The determinant of `M11` may still approach zero. Any later step replacing `M11 P` by `P` must pay the determinant/Jacobian divisor.

4. **THE `det M11 → 0` EDGE: CORRECT for shears, but scrutinise inverse use**

**PROVEN:** The argmax-over-`k`-minors condition really does bound the shear entries.

For `A = M21 M11⁻¹`, Cramer’s rule expresses each entry of `A` as

```text
det(M11 with one pivot row replaced by an outside row) / det(M11).
```

The numerator is itself a `k × k` minor of `R`. Since `M11` was chosen with maximal absolute `k`-minor,

```text
|numerator| ≤ |det M11|,
```

so each entry of `A` has absolute value `≤ 1`.

Similarly, entries of `B = M11⁻¹ M12` are ratios of `k`-minors obtained by replacing one pivot column, hence are also bounded by `1`.

So there is no hidden sublocus where a large `(k−1)`-minor of `M11` makes `M21 M11⁻¹` blow up. The inverse `M11⁻¹` alone can blow up, but the products `M21 M11⁻¹` and `M11⁻¹ M12` are controlled by the max-minor condition.

Smallest apparent danger: `r = 3, k = 2`, with `M11 = diag(ε,1)`. The inverse has size `1/ε`, but the max-minor condition forces outside-row/column replacement minors to be `O(ε)`, cancelling the blow-up in the shears.

5. **FRAGILITY: NEEDS-CARE**

Most likely formalisation cost: **proving and using the Cramer-rule shear bounds uniformly for arbitrary minor index pairs and permutations.** That is the critical bridge from “argmax minor” to bounded analytic comparison.

Second cost: Schur complement bookkeeping for arbitrary indexed submatrices. The determinant identity itself is standard, but making all row/column permutations, block decompositions, and minor-replacement determinants line up in Lean will be tedious.

I would not recommend a global blow-up of the maximal-minor ideal as the first formalisation route. It is cleaner conceptually, but likely heavier in Mathlib. The nested finite argmax cover is more elementary and Lean-compatible, provided you add:

- deterministic tie-breaking, avoiding algebraic tie-null proofs;
- an explicit zero-residual endpoint for recursive Schur blocks;
- Cramer-rule lemmas bounding both shears from the max-minor hypothesis;
- a clear separation between bounded norm comparison and later determinant-divisor/Jacobian estimates.