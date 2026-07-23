### 1. Dependent-sigma reindexing

Recommend **other**: build an equivalence from the fixed product directly to the subtype of layer coordinates:

```lean
P := Fin (d ℓ'.succ) × Fin (d ℓ'.castSucc)
enc : P → {x // x ∈ X}
E := Equiv.ofBijective enc ⟨hinjective, hsurjective⟩
```

For surjectivity, destruct the decoded sigma as `⟨⟨j,r⟩,c⟩`, prove `j = ℓ'` using `Fin.ext`, then `subst j`. This avoids every explicit dependent `Fin.cast`. Injection uses `Sigma.mk.inj` and `eq_of_heq`.

Define

```lean
b x u := if hx : x ∈ X then coeff (E.symm ⟨x, hx⟩) u else 0
```

Then reindex through:

```lean
_ = ∑ p : P, coeff p u * u (enc p) := (Fintype.sum_prod_type _).symm
_ = ∑ y : {x // x ∈ X}, b y u * u y := by simpa [b] using E.sum_comp _
_ = ∑ x ∈ X, b x u * u x := by
      rw [Finset.sum_coe_sort_eq_attach]
      exact Finset.sum_attach X _
```

Verified v4.29 names: `Equiv.ofBijective`, `Equiv.sum_comp`, `Fintype.sum_prod_type`, `Finset.sum_coe_sort_eq_attach`, `Finset.sum_attach`. No `Finset.sum_image` or sigma-filter equivalence is needed.

### 2. Slicker route

No. The 3-split is the cleanest route for this `AffineOn` definition. Prefix induction or scaling merely relocates the same coefficient bookkeeping; scaling does not construct `b`.

A useful local helper is interval congruence for `submult`: equality of all matrices in the interval implies equality of the subproducts. Use it for both `M` and `R`.

### 3. Cast/index traps

The orientation of `submult_comp` is upper piece times lower piece:

```lean
submult i m = submult j m * submult i j
```

Splitting first at `ℓ'.succ`, then at `ℓ'.castSucc`, therefore gives `M * (A ℓ' * R)`.

The one-layer reduction is cast-clean and was verified:

```lean
rw [submult_succ d A ℓ'.castSucc ℓ' le_rfl,
    submult_self, Matrix.mul_one]
```

Use `Fin.castSucc_le_succ ℓ'`, `Fin.le_last ℓ'.succ`, and `Fin.zero_le _`; proof-argument discrepancies disappear by proof irrelevance. The `canonFlatten` coordinate formula is indeed `rfl`.