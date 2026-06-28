**1. Soundness**

Follows from your summary: for non-radial boundary coordinates, the outer layer grading is triangular.

Rows = output layer `A_k`; columns = boundary coordinate `k'`. Since `A_k` reads only boundary `k` and future boundaries `≥ k+1`, we have

```text
∂(A_k entries) / ∂(boundary k' coords) = 0  when k' < k.
```

With layers ordered `0 < 1 < ...`, this is an **upper-triangular** Jacobian: nonzero blocks occur only on/above the diagonal. So there is no two-sided dependency, assuming the recursion really has no hidden dependence of `C(k+1)` on `N_k,W_k`.

ASSUMPTION: the shared radial coordinate `u` is either factored out separately or assigned a grade compatible with its all-layer dependence. If `u` is treated as an ordinary layer coordinate, it can break the clean boundary-only grading.

**2. Within-Layer Determinant**

Follows from your summary: the diagonal block for layer `k` differentiates `A_k = chainA(N_k,W_k,C(k+1))` with `C(k+1)` held fixed, because future-boundary dependence lies in off-diagonal blocks. Thus the diagonal determinant should be the local Schur-frame determinant times the LDU-core determinant, provided the banked lemma is stated for exactly this “future `C` fixed” map.

So the expected factor is:

```text
|det K_k|^(r_k+c_k) · LDU-pivot-monomial_k
```

ASSUMPTION: `chainA`/`chainQ` shears are unipotent or determinant-1 in the local frame, as in `chainChartFactor`. Verify that `schurFrame_abs_det` already includes the kept/lift row ordering used by `chainA`.

The extra `|z0|^5` in `(3,3,3,3)` is radial scaling. The extra `|z9|^3` is not automatically “chaining”; it should be checked semantically. If `z9 = det K_s` or a one-dimensional K/LDU pivot, it belongs to the `|det K_s|^(r+c)`/LDU monomial. If not, then your local Schur-frame lemma is missing a factor.

**3. Radial**

In the raw fused chart, the radial power is **distributed** across the layer diagonal blocks, because `u` appears inside `u·Rmat` and `u·Rfin`.

But algebraically you can factor it as a separate radial blowup:

```text
chartParamsGen ∘ kLDU
= normalizedChart ∘ radialBlowupOn ∘ kLDU
```

if you prove that factorization. Then the determinant contribution is a clean front factor

```text
|u_p|^(minAdm - 1)
```

and the remaining per-layer determinants should not count those `u` powers again.

Recommendation: use the separate `pivotBlowupOn`/radial factor if available. It isolates the shared coordinate and keeps the layer grading honest. Otherwise, the fused proof must account for the same exponent distributed through the layer blocks.

**4. Lean Route**

Ranking, least brittle first:

1. **Composition via `det_comp`**, after factoring radial and per-layer insertion maps, if that factorization is already natural.
2. **Structured block-triangular proof before flattening**, on layer/boundary product types, with `paramsEquivFlat` handled as det `1`.
3. **One global flat `Fin N` block-triangular matrix** through opaque `chartIdxEquiv`.

So yes: avoiding the single `N × N` flat matrix is cleaner. The global grading is mathematically sound, but in Lean it will be cast-heavy because `chartIdxEquiv` is Classical/opaque. If you do use it, prove vanishing by “unflatten, cancel `Equiv.symm_apply_apply`, use dependency lemma,” not by `fin_cases` or literal indices.