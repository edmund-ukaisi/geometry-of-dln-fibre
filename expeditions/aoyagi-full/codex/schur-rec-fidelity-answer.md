1. **FAITHFUL.** Derived: `Kcoup C k = (C k)₂₁ · (partProd C (k+1))₁₁⁻¹ · (partProd C k)₁₂`. With inclusive `P_k = partProd C (k+1)`, this is exactly cert `K_k`; no shift.

2. **FAITHFUL.** Derived: `partProd C 0 = 1`, so `(partProd C 0)₁₂ = 0`, hence `Kcoup C 0 = 0`. Unrolling:
`coreProd C 3 = (((1·(1-K₀)·S₀)·(1-K₁)·S₁)·(1-K₂)·S₂) = (S₀·(1-K₁)·S₁)·(1-K₂)·S₂`.

3. **TOO-STRONG.** Derived: the fold step needs `P_k₁₁`, `C_k₁₁`, and `P_{k+1,11}` invertible for `0≤k<L`, so partial products through `L` are needed except `P_0` is automatic and `P_1` duplicates `C_0`. Not too weak and not vacuous; just not literally minimal.

4. **FAITHFUL.** Derived: factor order and block shapes match the cert, with only left-associated matrix products. Intent inference: no further sign/order/index gap found; `L=0` is just a harmless empty-product extension.

Overall verdict: **TOO-STRONG** hypotheses only; no off-by-one or other fidelity gap.