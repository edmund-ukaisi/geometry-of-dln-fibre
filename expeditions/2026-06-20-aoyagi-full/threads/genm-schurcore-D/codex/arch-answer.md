Verdict: keep the mathematical route, but implement it as:

1. `a = 0`.
2. Singular Gram branch.
3. Enlarge to a column ball with radius `n + 1`.
4. Route A for orthogonal invariance.
5. Use the existing `exists_ortho_ext`, placing the kernel block first, so `Acor * O = [0 | L]`.
6. After splitting rows, enlarge directly to “active row-balls × tail matBox”.

This uses the most already-banked machinery and avoids `WithLp`/matrix compatibility glue.

### Q1 — choose route A

For the present repository, route A is shorter and less instance-sensitive:

- Transpose/reindex to `Fin p → Fin n → ℝ`.
- Apply `lintegral_comp_mulLeftₚ p O`.
- Encode the ball restriction with an indicator:
  ```lean
  g := colBall.indicator weight
  ```
- Use:
  - `lintegral_indicator`
  - `Measurable.indicator`
  - `MeasurableSet.univ_pi`
  - `measurableSet_ball`
  - `measurable_detGram`
  - `lintegral_comp_mulLeftₚ`

There is no obstruction from the full-space CoV, but you cannot apply it directly to `∫⁻ ... in ball`. Apply it to the measurable indicator. Since `|det O| = 1`, its Jacobian factor simplifies to `1`.

Order: first
```lean
box integral ≤ column-ball integral
```
by `lintegral_mono_set`, then prove exact invariance of the ball integral. Do not transform the original box: it is not rotation-invariant.

Route B is conceptually pleasant and uses:

- `LinearIsometryEquiv.measurePreserving`
- `volume_preserving_pi`
- `LinearIsometryEquiv.preimage_ball`
- `MeasurePreserving.setLIntegral_comp_preimage_emb`
- `PiLp.volume_preserving_toLp`

but it requires a raw-matrix ↔ columnwise-`EuclideanSpace` equivalence and an algebraic bridge between the isometry and matrix multiplication. That is more glue here.

A useful helper to bank is:
```lean
norm_mulVec_eq_of_transpose_mul_self
  (hO : Oᵀ * O = 1) :
  ‖WithLp.toLp 2 (O *ᵥ x)‖ = ‖WithLp.toLp 2 x‖
```
using `EuclideanSpace.real_norm_sq_eq`, `Matrix.dotProduct_mulVec`,
`Matrix.vecMul_transpose`, and `Matrix.mulVec_mulVec`.

### Q2 — do not reconstruct the extension

The repository already has exactly the extension lemma you need:
[RouteMSJOrthoExtend.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a041830c5733b5748/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJOrthoExtend.lean:24):
```lean
exists_ortho_ext
```

Take an orthonormal basis of `ker A`, form its coordinate matrix
```lean
Uker : Matrix (Fin n) (Fin (n - b)) ℝ
```
and call `exists_ortho_ext`. It preserves these as the first columns. Thus use
```text
A * O = [0 | L]
```
rather than `[L | 0]`. This avoids a final column permutation.

For the kernel dimension, use:

- `Matrix.rank_self_mul_transpose`
- `Matrix.rank_of_isUnit`
- `Matrix.isUnit_iff_isUnit_det`
- `isUnit_iff_ne_zero`
- `Matrix.rank_eq_finrank_range_toLin`
- `LinearMap.finrank_range_add_finrank_ker`
- `finrank_euclideanSpace_fin`

For orthogonality, `exists_ortho_ext` gives `Oᵀ * O = 1`. Obtain the other orientation through:
```lean
Matrix.mem_orthogonalGroup_iff'
Matrix.mem_orthogonalGroup_iff
```
Do not silently use `O * Oᵀ = 1` from `Oᵀ * O = 1`.

If constructing from Mathlib directly, prefer
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, not
`Orthonormal.exists_orthonormalBasis_extension`: the latter returns a basis indexed by an arbitrary `Finset`, causing reindexing work.

The basis-matrix API is:

- `a.toBasis.toMatrix b`
- `OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal`
- `OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose`
- `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self`
- `Matrix.conjTranspose_eq_transpose_of_trivial`

There is no main constructor named `OrthonormalBasis.toMatrix`; use `toBasis.toMatrix`.

Do not prove `L` invertible first. Prove
```lean
L * Lᵀ = A * Aᵀ
```
from `O * Oᵀ = 1` and the zero columns, then take determinants. Invertibility follows afterward if ever needed.

### Q3 — no materially simpler mathematical reduction

A Cauchy–Binet expansion does not uniformly extract
`det (A Aᵀ)`: the Plücker coordinates of `A` remain mixed with those of `S`. Recovering a uniform factor again requires orthogonal invariance or an equivalent Grassmannian argument.

QR/Gram–Schmidt merely repackages the same kernel-complement construction. Gaussian or coarea routes introduce substantially heavier measure theory. PSD square roots are worse at this pin.

A possible reusable abstraction is a cross-index isometry
```lean
EuclideanSpace ℝ (Fin (n-b) ⊕ Fin b) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)
```
which makes the row split definitionally clean, but for this theorem it is more new infrastructure than reusing `exists_ortho_ext`.

### Q4 — simplify the product enlargement

After splitting the rotated matrix as `(β, α)`, with `β` the first `n-b` zero-block rows and `α` the active `b` rows, do not enlarge to two column-ball domains.

With column-ball radius `R`, enlarge directly to:
```text
α ∈ product of b row-balls of radius p*R² + 1
β ∈ matBox (n-b) p R
```
This is exactly what `qbox_lintegral_lt_top` and `matBox_volume_lt_top` consume.

Use:

- `volume_preserving_arrowCongr'`
- `volume_measurePreserving_sumPiEquivProdPi`
- `MeasurePreserving.setLIntegral_comp_preimage_emb`
- `lintegral_mono_set`
- `setLIntegral_prod_symm` — convenient because the split is tail first
- `setLIntegral_const`
- `lintegral_mul_const''`
- `Measure.volume_eq_prod` if product-volume inference stalls
- `Fintype.sum_sum_type` for block matrix multiplication
- `ENNReal.mul_lt_top`

The active integrand is measurable via
[measurable_detGram](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a041830c5733b5748/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJProductTube.lean:368). Transport to `qbox_lintegral_lt_top` using the already-banked `rowsEquiv`, `measurePreserving_rowsEquiv`, and `gram_rowsEquiv` in that file.

Important trap: your stated open balls of radius `√n` and `√(pn)` do not contain boundary points. A column with all entries `±1` has norm exactly `√n`. Use closed balls, or—cleaner—open radii such as
```lean
R := n + 1
Rrow := p * R^2 + 1
```
The theorem only needs a finite uniform constant, so avoiding square roots is worthwhile.

Finally, Tonelli for `ℝ≥0∞` removes integrability hypotheses, but `setLIntegral_prod` still asks for `AEMeasurable`; it is not completely hypothesis-free.