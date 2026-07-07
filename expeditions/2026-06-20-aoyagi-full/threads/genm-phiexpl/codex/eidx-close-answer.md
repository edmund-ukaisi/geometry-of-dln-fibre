1. **Classification:** correct, with one caveat. For `Q := b x + C₀`,
`recoverProduct Q` reads only
`Q.2.toBlocks₁₁`, `Q.2.toBlocks₁₂`, `Q.1.toBlocks₂₁`, `Q.1.toBlocks₂₂`, `Q.2.toBlocks₂₂`.

So:
- regular: `L0.₂₁ = M21`, `L1.₁₁ = M11`, `L1.₁₂ = M12`
- core: `L0.₂₂ = A0red`, `L1.₂₂ = A1red`
- spec: `L0.₁₁ = X`, `L0.₁₂ = Y`, `L1.₂₁ = Uu`

No spec leak. Caveat: this is for the **Schur-output coordinates** `Q`, not the original pre-Schur layer blocks. Also the `₂₂` residual depends on regular variables through `M21 * M11⁻¹ * M12`, so `qₑ p` depends on `p`; only the slice `p=0` collapses to the core product.

2. **Build `e_idx` by semantic partition, then `Fintype.equivFin`.** Avoid glued injections / `Equiv.ofBijective`; the inverse readbacks will be opaque.

Use semantic types:
```lean
RegIdx  := (Fin (H 0 - r) × Fin r)
        ⊕ (Fin r × (Fin r ⊕ Fin (H 2 - r)))

CoreIdx := FlatIdx (fun s => H s - r)

SpecIdx := (Fin r × (Fin r ⊕ Fin (H 1 - r)))
        ⊕ (Fin (H 1 - r) × Fin r)
```
Then build an explicit
```lean
roleToFlatIdx :
  RegIdx ⊕ (CoreIdx ⊕ SpecIdx) ≃ FlatIdx H
```
by cases, using `sumSplit I hI`, `sumSplit K hK`, `sumSplit J hJ`. The inverse classifies by layer and by applying the corresponding `sumSplit.symm`.

Final shape:
```lean
e_idx :=
  (Equiv.sumCongr regE (Equiv.sumCongr coreE specE)).trans
    (roleToFlatIdx.trans (Fintype.equivFin (FlatIdx H)))
```
where `coreE := (Fintype.equivFin CoreIdx).symm`, similarly for spec, and `regE` uses one card lemma `Fintype.card RegIdx = nRegL2 H r`. I would set `specDim := Fintype.card SpecIdx`; prove the subtraction formula separately only if needed.

3. You do **not** logically need literal on-the-nose core equality, but you need it up to the consumer’s `e`. A “refl-ish” `e` only works if the split core slot is already in `paramsEquivFlat (H-r)` order. Otherwise you have merely moved the permutation/decode proof into `qₑ` and `hfact`.

Leaner route: make the core slot equal to the reduced `paramsEquivFlat` order, and let `e` handle only the core translation by `coreShift` plus identity on spec. Decoupling `qₑ(0,t)` from the actual `₂₂` residual is valid only after proving the germ equality with `F`; that proof is usually harder than aligning the core index once.

4. Yes: split `F` into the three regular residual blocks plus the `₂₂` residual. Prove:
- `₁₁`, `₁₂`, `₂₁` residuals are exactly the regular coordinates, hence sum to `∑ p_i^2`;
- `₂₂` residual equals `qₑ p` near the base, using the bump-global inverse `G = M11⁻¹` eventually;
- at `p=0`, Schur complement of `Br₀` is zero, giving `A0red * A1red`.

No real Euclidean/Pi trap: `EuclideanSpace ℝ (Fin n)` is coordinate-readable, and the expression `∑ i, qₑ p i ^ 2` is just a coordinate sum. The only nuisance is flattening the `(H0-r) × (H2-r)` residual matrix to `Fin n`; again, prefer `n := Fintype.card (Fin (H0-r) × Fin (H2-r))` unless the product formula is required.

5. Top pitfalls:
- **Spec leak by naming confusion:** keep `P` pre-Schur and `Q = b x + C₀` post-Schur separate. The classification is true for `Q`.
- **Opaque index equivs:** do not use `Equiv.ofBijective` for the central split. Explicit semantic equiv with an explicit inverse gives usable readbacks.
- **Global vs germ equality:** `hchart` may use eventual `G = inv`, but `hfact` is `∀ t`. Ensure that on `p=0` the inverse argument is the constant base `M11`, so `G M11₀ = M11₀⁻¹` globally in `t`.