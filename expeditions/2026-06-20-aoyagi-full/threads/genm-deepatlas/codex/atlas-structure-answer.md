## 1. Route verdict

| Rank | Route | Verdict |
|---|---|---|
| 1 | **(B) rank factorization** | Pick this. Highest reachability, lowest dependent-index risk. |
| 2 | **(A) pivot permutation** | Mathematically clean, and `blockSplitEquiv` is already banked, but un-permuting `X*M` and pivot columns is the classic Lean time-sink. |
| 3 | **(C) direct column-span proof** | Correct, but recreates range/finrank/coefficient infrastructure with no benefit over the banked factorization. |

The decisive repository fact is that rank factorization is already proved:

- `exists_rank_factorization_gen` in [D1JointDiffRankExact.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/DLN/RLCT/Validate/D1JointDiffRankExact.lean:53).
- Full-column/row-rank one-sided inverses in [D1HChartRank.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/DLN/RLCT/Validate/D1HChartRank.lean:90).

For `M=P*Q`, put
\[
P_\rho=P[\rho,:],\qquad Q_\kappa=Q[:,\kappa].
\]
Then
\[
U=M[\rho,\kappa]=P_\rho Q_\kappa.
\]
Since `U` is a unit, `IsUnit.mul_iff` makes both square factors units. Therefore
\[
\begin{aligned}
C\,U^{-1}R
 &=P Q_\kappa(P_\rho Q_\kappa)^{-1}P_\rho Q\\
 &=P Q_\kappa Q_\kappa^{-1}P_\rho^{-1}P_\rho Q\\
 &=PQ=M.
\end{aligned}
\]
This is exactly where verified `Matrix.mul_inv_rev` pays off.

Ordered build:

1. **BANKED-repo**
   ```lean
   exists_rank_factorization_gen (M) :
     ∃ P : Matrix (Fin m) (Fin M.rank) ℝ,
       ∃ Q : Matrix (Fin M.rank) (Fin n) ℝ,
         M = P * Q ∧ P.rank = M.rank ∧ Q.rank = M.rank
   ```

2. **BANKED-Mathlib**
   ```lean
   Matrix.submatrix_mul_equiv
   IsUnit.mul_iff
   ```

3. **NEW**
   ```lean
   exists_pivotUnit_factorization
     (hM : M.rank = r) (hU : IsUnit (M.submatrix ρ κ)) :
     ∃ P : Matrix (Fin m) (Fin r) ℝ,
       ∃ Q : Matrix (Fin r) (Fin n) ℝ,
         M = P * Q ∧ P.rank = r ∧ Q.rank = r ∧
         IsUnit (P.submatrix ρ id) ∧ IsUnit (Q.submatrix id κ)
   ```

4. **NEW — HARDEST**
   ```lean
   generalPivot_CUR
     (hM : M.rank = r) (hU : IsUnit (M.submatrix ρ κ)) :
     M = M.submatrix id κ * (M.submatrix ρ κ)⁻¹ *
           M.submatrix ρ id
   ```
   The difficulty is only noncommutative reassociation plus submatrix normalization, not dependent-width permutation bookkeeping.

5. **NEW**
   ```lean
   generalPivot_sideRanks ... :
     (M.submatrix ρ id).rank = r ∧
     (M.submatrix id κ * (M.submatrix ρ κ)⁻¹).rank = r
   ```

6. **BANKED-repo**
   ```lean
   exists_right_inverse_of_rank_eq_height
   rank_mul_eq_of_mul_eq_one
   ```

7. **NEW target**
   ```lean
   generalPivot_reduce_rank
     (hM : M.rank = r) (hU : IsUnit (M.submatrix ρ κ)) :
     (X * M).rank =
       (X * M.submatrix id κ * (M.submatrix ρ κ)⁻¹).rank
   ```

Route B solves the algebraic bridge only. For the unit-Jacobian chart transport, continue using banked `blockSplitEquiv` and `measurePreserving_matReindexEquiv` from [RouteMSJBlockReindex.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJBlockReindex.lean:232). Mixing B for rank and A-style permutation for measure transport is the clean combination.

## 2. Mathlib check

1. Rank factorization: **ABSENT** as a packaged Mathlib v4.29 matrix theorem.

   Repository alternatives are **VERIFIED-name**:

   - `DLNFibre.DLN.RLCT.exists_rank_factorization`
   - `DLNFibre.DLN.RLCT.exists_rank_factorization_gen`

2. Reindex rank invariance: **VERIFIED-name**:

   - `Matrix.rank_reindex`
   - `Matrix.rank_submatrix` for submatrices indexed by equivalences

   Both are in [Rank.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Rank.lean:234).

   `rank_submatrix_equiv` itself: **ABSENT** as that exact name.

3. Reverse inverse: **VERIFIED-name**:

   ```lean
   Matrix.mul_inv_rev (A B) : (A * B)⁻¹ = B⁻¹ * A⁻¹
   ```

   It is unconditional for Mathlib’s nonsingular inverse; invertibility is needed only for cancellation. See [NonsingularInverse.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:641).

## 3. Effective-state recursion

Yes, this closes without constructing a reduced `Params`.

For `j=k+1`, let `Aₖ` denote the cast-normalized layer exposed by `prodAux_succ`. With
\[
M=A_kQ,\qquad
Q'=M[:,\kappa]\,M[\rho,\kappa]^{-1},
\]
the descent lemma should be shaped as:

```lean
theorem effectiveState_descend
    (k : ℕ) (hk : k + 1 < L + 1)
    (q : ℕ)
    (Q : Matrix (Fin (H ⟨k + 1, hk⟩)) (Fin q) ℝ)
    (hQ : Q.rank = q)
    (r : ℕ) (hr : (Aₖ * Q).rank = r)
    (ρ : Fin r ↪ Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩))
    (κ : Fin r ↪ Fin q)
    (hU : IsUnit ((Aₖ * Q).submatrix ρ κ)) :
    let Q' :=
      (Aₖ * Q).submatrix id κ *
        ((Aₖ * Q).submatrix ρ κ)⁻¹
    Q'.rank = r ∧
      (prodAux H A (k + 1) hk * Q).rank =
        (prodAux H A k (Nat.lt_of_succ_lt hk) * Q').rank
```

The proof is `prodAux_succ`, one fully applied `Matrix.mul_assoc`, then `generalPivot_reduce_rank`. `hQ` is an invariant carried by the state; the algebraic transition itself does not consume it.

- Initial state: `j=L`, `q=H (Fin.last L)`, `Q=1`; hence `prod = prodAux L * Q`.
- Terminal state: `j=0`; `prodAux 0=1`, so the represented rank is `Q.rank=q`.
- For the rank-`s` locus, retain precisely the terminal branches with `q=s`.

No bespoke flat enumeration is needed. Nested finite unions suffice. If the final gluing consumer is invoked once, flatten the finite decision tree only syntactically as a dependent `Sigma`; its `Fintype` instance is inferred. Bound each rank choice by `min (H k) q`.

Also, `lintegral_lt_top_of_finite_cover` requires null uncovered remainder, not pairwise-null chart overlaps. Pivot charts may overlap freely.

## 4. Cheapest first green

Land first:

```lean
exists_pivotUnit_factorization
```

It tests the factorization import, dependent `M.rank = r` rewrite, `submatrix_mul_equiv`, and the matrix `IsUnit.mul_iff` instance—the uncertain API seam of route B.

Estimated size:

- First checkpoint: **20–35 proof LoC**
- General-pivot bridge family: **80–140 LoC**
- Whole Tide B: **450–750 theorem/proof LoC**, roughly **650–950** including documentation, witnesses, and axiom checks.

Those bands are design estimates, not source facts.