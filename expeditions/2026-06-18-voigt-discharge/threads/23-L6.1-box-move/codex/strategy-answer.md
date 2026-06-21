**1. General**

Use **A, but consume it as direct orbit membership**, not as a detour through rank equality.

For `ht : t ≠ 0`, build `φ_v(t)` and apply `baseChange_of_intertwine upstairs (F t) φ hφ`; then prove
`canonicalCoord d (F t) ∈ orbitSet upstairs` directly. The `t⁻¹` is harmless because it is only in the nonzero-fibre orbit certificate, not in the polynomial curve.

Special block formula:

```lean
S_t     = !![1, -t⁻¹; 0, 1]
S_t_inv = !![1,  t⁻¹; 0, 1]
```

On the overlap vertices `c ≤ v ≤ b`, use `S_t`; on the right tail `b < v ≤ e`, use scalar multiplication by `t`; elsewhere identity; on `rest`, identity, packaged with product/sum splitting.

Worst subgoal: the `hφ` edge proof at the cut arrow, after unfolding nested direct-sum coordinates:

```lean
[t, 1] * S_t = [t, 0]
```

inside a `Fin (1 + (1 + foldDim rest v))` split. The algebra is tiny; the `Fin`/`foldDim` bookkeeping is the cost.

**2. (1,2,1) Witness**

Use **explicit base change**, even simpler than full rank computation.

Take:

```lean
P₀ = 1
P₁ = !![1, -t⁻¹; 0, 1]
P₂ = !![t]
```

with inverses `P₁⁻¹ = !![1, t⁻¹; 0, 1]`, `P₂⁻¹ = !![t⁻¹]`. Then check:

```lean
P₁ * !![1; 0] = !![1; 0]
!![t] * !![1, 0] * P₁⁻¹ = !![t, 1]
```

Worst subgoal: proving the symbolic units, especially `P₂ * P₂⁻¹ = 1` and `P₁ * P₁⁻¹ = 1`; solve by `ext`, `fin_cases`, `simp [ht]`.

**3. Third Route**

Yes: **direct orbit certificate**. Skip `rankPattern_eq_iff_orbit` entirely for step 2.

Lean on the landed repo lemma `baseChange_of_intertwine`; Mathlib names I verified locally: `LinearEquiv.ofLinear`, `Matrix.toLin'OfInv`, `LinearEquiv.prodCongr`, `LinearEquiv.sumArrowLequivProdArrow`, `Units.mk0`, `LinearEquiv.smulOfUnit`.

Staying only on `multiplicityArray`/`cumul` does not close this: `rankPattern_intervalDirectSum_eq_cumul` applies to block-diagonal interval sums, while `F(t)` is not one.

**4. Warning**

The proof will balloon at the **common dimension-vector / nested direct-sum coordinates**, not at `t⁻¹`.

Pre-empt it by defining a common box dimension and local coordinate-splitting lemmas before the curve. Do not repeatedly unfold `intervalDirectSum` in the main proof. Also do not rely on an inferred row-rank shortcut like `rank_nonzero_row`; I did not find such a verified Mathlib lemma at this pin. Verified rank lemmas include `Matrix.rank_of_isUnit`, `Matrix.rank_diagonal`, and the rank-preservation lemmas `Matrix.rank_mul_eq_left_of_isUnit_det` / `Matrix.rank_mul_eq_right_of_isUnit_det`.