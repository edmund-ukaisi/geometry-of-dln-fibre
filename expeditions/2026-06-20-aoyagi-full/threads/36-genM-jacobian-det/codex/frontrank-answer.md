**Verdict**

**FACT:** Use **(a), literal factorization through `Fin 1`**, not rank theory. The load-bearing identity is simply

```lean
(X * Y) i j = X i 0 * Y 0 j
```

for `X : Matrix (Fin m0) (Fin 1) ℝ` and `Y : Matrix (Fin 1) (Fin m1) ℝ`, proved by `Matrix.mul_apply` + `Fin.sum_univ_one`.

**FACT:** This mechanism covers both subcases uniformly. If `M₀ = 1`, take the split at `p* = 0`: the left factor is the empty prefix `I₁`, and the right factor is the whole front product `P`, so `P = I₁ * P`. No rank argument is needed.

**Important correction, FACT:** The statement “all columns are multiples of column `0`” is **false without a nonzero column-0/off-pole hypothesis**. Example: a single row `P = [0 1]` factors through `Fin 1` and has rank `≤ 1`, but column `1` is not a scalar multiple of column `0 = 0`. The unconditional Fin-1 factorization gives columns as multiples of the hidden column `U`, not necessarily of `P.col 0`.

**INFERRING:** Since your downstream separately supplies `‖col 0‖² ≠ 0`, the right Lean statement should include that hypothesis when normalizing to `c0 = column 0`.

**Split Point**

**FACT:** Choose any certified `p*` with `M p* = 1`; the first such index is a clean deterministic choice.

Define

```text
U = A⁰ * ... * A^(p*-1)      -- empty product if p* = 0
V = A^(p*) * ... * A^(L-2)   -- empty product if p* = L-1
```

Then

```text
P = U * V
```

with shapes

```text
U : M₀ × M_{p*} = m0 × 1
V : M_{p*} × M_{L-1} = 1 × m1
```

Corner cases:

```text
p* = 0:     U = I₁, V = P
p* = L-1:   U = P,  V = I₁
```

No excluded last layer `A^(L-1)` appears.

**Lean Route**

Use a generic bridge first:

```lean
def FactorsThroughOne {r c : Type*} [Fintype r] [Fintype c]
    (P : Matrix r c ℝ) : Prop :=
  ∃ U : Matrix r (Fin 1) ℝ,
  ∃ V : Matrix (Fin 1) c ℝ,
    P = U * V
```

Unconditional outer-product form:

```lean
theorem outerColumns_of_factorsThroughOne
    {r c : Type*} [Fintype r] [Fintype c]
    {P : Matrix r c ℝ}
    (hP : FactorsThroughOne P) :
    ∃ u : r → ℝ, ∃ v : c → ℝ,
      ∀ i j, P i j = v j * u i := by
  rcases hP with ⟨U, V, rfl⟩
  refine ⟨fun i => U i 0, fun j => V 0 j, ?_⟩
  intro i j
  simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]
```

Column-`0` normalized version, matching downstream:

```lean
theorem col0Columns_of_eq_mul_fin_one_of_col0_norm_ne_zero
    {m0 m1 : ℕ} (hm1 : 0 < m1)
    {P : Matrix (Fin m0) (Fin m1) ℝ}
    (U : Matrix (Fin m0) (Fin 1) ℝ)
    (V : Matrix (Fin 1) (Fin m1) ℝ)
    (hP : P = U * V)
    (hcol0 : (∑ i : Fin m0, (P i ⟨0, hm1⟩)^2) ≠ 0) :
    ∃ c0 : Fin m0 → ℝ, ∃ μ : Fin m1 → ℝ,
      c0 = (fun i => P i ⟨0, hm1⟩) ∧
      μ ⟨0, hm1⟩ = 1 ∧
      ∀ i j, P i j = μ j * c0 i
```

Here `μ j = V 0 j / V 0 ⟨0, hm1⟩`; `hcol0` implies `V 0 ⟨0, hm1⟩ ≠ 0`.

Key lemmas/tools:

```lean
Matrix.mul_apply
Fin.sum_univ_one
Matrix.mul_assoc
Matrix.one_mul
Matrix.mul_one
Matrix.reindex
Matrix.reindex_refl_refl
Matrix.submatrix_mul_equiv
```

For the dependent chain, the real cost is **not** the Fin-1 algebra. The cost is proving

```lean
prod frontWidths frontParams = U * V
```

after splitting a left-associated dependent-width `prodAux` at `p*`. That is where casts, `Matrix.reindex`, `finCongr`, and reassociation overhead live. Once the `FactorsThroughOne` witness is available, the rank-one-column proof is short and rank-free.