**1. Verdict**

**CORRECT.** Derivation: for `Q_b : b × q`, `rank Q_b = b` gives injectivity of `Q_bᵀ` on the row-dual side, hence for `x ≠ 0`,
`xᵀ (Q_b Q_bᵀ) x = ‖Q_bᵀ x‖² > 0`; with `posDef_iff_dotProduct_mulVec`, this is exactly `(Q_b Q_bᵀ).PosDef`. Since Regime A asks for `PosDef` directly, Cauchy-Binet is not needed to enter the good stratum. Inference: modulo the banked pivot cover and ordinary measurability of minor nonvanishing loci, this is the minimal missing prerequisite for good-stratum closure.

**2. Possible Trap**

The thing most likely to still force Cauchy-Binet is a **quantitative lower bound** on the Gram determinant on a pivot chart, e.g. `det(Q_b Q_bᵀ) ≥ minor²`, used to dominate or integrate the emitted weight `det(Q_b Q_bᵀ)^{-a/2}`. But merely defining/measuring/routing `{rank Q_b = b}` does **not** need that: use the finite pivot cover `{rank ≥ b} = ⋃ minor≠0`, and since `rank Q_b ≤ b`, this is the full-row-rank stratum. Strict positivity from `PosDef` is enough unless a later estimate specifically needs comparison to a chosen minor.

**3. Shift-Source**

**YES.** Derivation: the `ab/2` loss comes from the Γ-peel in Regime A, producing `c'' = c' - ab/2`; the radial `u`-scale condition with `α = M₁M₂ - 1 - 2c'` is non-binding as stated and is not the source of the shift.