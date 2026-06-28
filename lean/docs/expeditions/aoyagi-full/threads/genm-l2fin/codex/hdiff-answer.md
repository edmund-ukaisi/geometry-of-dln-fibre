Certainty: Mathlib names are `Matrix.submatrix_sub`, `Matrix.submatrix_submatrix`, `Matrix.reindex_apply`, `Matrix.reindex_refl_refl`, `Matrix.reindex_trans`, `Matrix.fromBlocks_multiply`, `Matrix.toBlocks_fromBlocks₁₁/₁₂/₂₁/₂₂`, `Matrix.mul_sub`, `Matrix.add_mul`, `Matrix.mul_assoc`, `Matrix.zero_mul`. There is no separate `Matrix.reindex_sub`; use `Matrix.reindexAddEquiv ... .map_sub` or unfold to `submatrix_sub`. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Defs.html)) ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Block.html))

Common prefix, assumed local names `hΔC1`, `hRblocks`, `hLtop`:

```lean
have hsplit : M - N = L0 * R1 := by
  subst M; subst N
  rw [show (Matrix.reindex eR eC) (prod H Cψ) - (Matrix.reindex eR eC) (prod H Cq)
      = (Matrix.reindex eR eC) (prod H Cψ - prod H Cq) by
      simpa [Matrix.coe_reindexAddEquiv] using
        ((Matrix.reindexAddEquiv _ eR eC).map_sub (prod H Cψ) (prod H Cq)).symm]
  rw [prod_eq_two_of_L2 H Cψ, prod_eq_two_of_L2 H Cq]
  simp only [finCongr_refl]; erw [Matrix.reindex_refl_refl]
  rw [framedParamsPivot_psiSplitRawL2Core_of_ne 0 hs0, ← Matrix.mul_sub]
  rw [reindex_mul_split eR eM eC]
```

`hRblocks` should be:

```lean
have hRblocks : R1 = Matrix.fromBlocks 0 (ΔY * d') 0 (ΔT * d') := by
  rw [hΔC1, reindex_mul_fromBlocks eM eQ eC]
  simp [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
        Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
        Matrix.toBlocks_fromBlocks₂₂, hQtri]
```

`hdiff11`:

```lean
rw [hsplit, hRblocks, ← Matrix.fromBlocks_toBlocks L0]
rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
simp
```

`hdiff21`:

```lean
rw [hsplit, hRblocks, ← Matrix.fromBlocks_toBlocks L0]
rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
simp
```

Yes: after `hsplit`, `hdiff11/21` use only `hQtri` plus zero-left-column shape. No `hPtri`, no `e2`.

`hdiff12`:

```lean
rw [hsplit, hRblocks, hLtop, ← Matrix.fromBlocks_toBlocks L0]
rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂]
simp only [zero_mul, add_zero]
rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul]
rw [he2zero, Matrix.zero_mul]
```

The residual for `e2` is exactly:

```lean
he2zero : A0 * ΔY + Y0 * ΔT = 0
-- goal becomes:
(A0 * ΔY + Y0 * ΔT) * d' = 0
```

No extra leading frame if `hLtop` identifies `L0.toBlocks₁₁ = A0` and `L0.toBlocks₁₂ = Y0`. If `e2_regPreserve` is for raw, unframed reads, then `hPtri` alone is not enough; you need a framed-top-row lemma or framed `e2` variant.

Big cast pitfall: do not let outer `eM` compose with `finCongr rfl` implicitly. Normalize immediately:

```lean
simp only [finCongr_refl] at *
erw [Matrix.reindex_refl_refl] at *
```

If you must compose, use `Matrix.reindex_trans`; unfolded form is `Matrix.submatrix_submatrix`.