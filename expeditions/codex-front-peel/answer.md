**1. Recommended Technique**

Pick **(a)** for a reusable `prod_front_peel`: prove the `k+1` prefix statement by induction on `k`, never by entrywise `ext`. Ranking: **(a) > (d) > (b) > (c)**. Strategy (a) is local, uses your existing `prodAux_succ` and `reindex_finCongr_mul`, and turns the problem into associativity plus cast transport. Strategy (d) is best only if the real target is the `suffix 0 = prod M A` bridge and you do not need a standalone front-peel. Strategy (b) is clean architecturally but creates new API and still needs a `prod = prodFrom 0` reassociation proof. Strategy (c) is highest churn. The cast tools I would rely on are: `prodAux_succ`, `reindex_finCongr_mul`, `Matrix.reindex_apply`, `Matrix.submatrix_mul_equiv`, `Matrix.submatrix_submatrix`, `Equiv.symm_symm`, `Equiv.symm_comp_self`, `Equiv.self_comp_symm`, and `finCongr_refl`. No `HEq`; use proof irrelevance/`Subsingleton.elim` for equality proofs.

**2. Generalized Induction Statement**

I would avoid `k - 1`; state the theorem for the nonzero prefix:

```lean
theorem prodAux_front_peel_succ
    (M : Fin (L + 1 + 1) → ℕ) (A : Params M)
    (k : ℕ) (hk : k + 1 < L + 1 + 1)
    (erow :
      M ((0 : Fin (L + 1)).castSucc) =
        M (0 : Fin (L + 1 + 1)))
    (ecol :
      Mtail M (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin (L + 1)) =
        M (⟨k + 1, hk⟩ : Fin (L + 1 + 1))) :
    prodAux M A (k + 1) hk =
      Matrix.reindex (finCongr erow) (Equiv.refl _) (A (0 : Fin (L + 1))) *
        Matrix.reindex (Equiv.refl _) (finCongr ecol)
          (prodAux (Mtail M) (Atail M A)
            k (Nat.lt_of_succ_lt_succ hk)) := by
  ...
```

Then `prod_front_peel` is this theorem at `k = L`, followed by collapsing `erow`/`ecol` using `finCongr_refl`.

Inductive step shape:

```lean
rw [prodAux_succ M A (k + 1) hk₂ eP₁ eP₂]
rw [prodAux_succ (Mtail M) (Atail M A) k hkTail eT₁ eT₂]
rw [IH]
rw [reindex_finCongr_mul]
rw [Matrix.mul_assoc]
```

The key is: expand the parent last step and the tail last step, distribute the outer tail reindex over the tail product with `reindex_finCongr_mul`, then use associativity to identify

```lean
(A 0 * tailPrefix) * parentLayer
=
A 0 * (tailPrefix * tailLayer)
```

After unfolding `Atail`, the parent layer `A ⟨k+1,_⟩` and the tail layer `(Atail M A) ⟨k,_⟩` are the same matrix modulo `finCongr_refl`/`Subsingleton.elim` casts. The base `k = 0` should use `prodAux_succ` on the parent plus `prodAux _ _ 0 = 1`; then collapse the boundary reindex and finish with `Matrix.one_mul`/`Matrix.mul_one`.

**3. Cast-Collapse Tactic**

Your repo precedent is the right tactic. When `e : n = n` is propositionally but not syntactically `rfl`:

```lean
rw [show (finCongr e) = Equiv.refl _ from finCongr_refl _]
rfl
```

or for the common orientation:

```lean
rw [show (finCongr e.symm) = Equiv.refl _ from finCongr_refl _]
rfl
```

For two-sided matrix reindex:

```lean
rw [show (finCongr erow) = Equiv.refl _ from finCongr_refl _,
    show (finCongr ecol) = Equiv.refl _ from finCongr_refl _]
rfl
```

If Lean still sees nested reindexes, use:

```lean
simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
  Equiv.symm_symm, Equiv.symm_comp_self, Equiv.self_comp_symm,
  Matrix.submatrix_id_id]
```

The important rule: collapse `finCongr` at the equivalence level before doing entrywise sums. Avoid the `∑ if ...` goal entirely.