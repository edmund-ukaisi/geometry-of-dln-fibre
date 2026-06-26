1. **Q1.** Use the two direct inequalities, not a reusable `weightedThreshold_cover_min`.

Reason: all chart thresholds are intended to equal the same `v`, so the reusable infimum lemma buys little and forces you to formalize relative domains, null sets, neighborhood shrinking, and fibre issues all at once.

2. **Q2.** Yes, there is a real domain-quantifier gap if you use the fixed full `V_i \ Z_i`.

Reason: `c < chartThreshold_i` gives integrability on some open `Ω_i ⊇ fibre_i`, not automatically on the chart domain used by `g5_flat_cover`. The sound move is to shrink the target neighborhood `U` and use clipped domains
`V_i ∩ φ_i ⁻¹' U \ Z_i`,
with compactness of the bounded exceptional fibre plus continuity giving inclusion in `Ω_i`. This is assembly if the fibre is bounded/compact; it is false as stated for an arbitrary fixed full chart domain.

3. **Q3.** `weightedThreshold_le_transport` is usable for LE only for a restricted/proper chart version.

Reason: the global blow-up `(u,z) ↦ (u, u z)` is not proper, since the fibre over `0` is noncompact. On the bounded chart domain, injectivity off `pivotZero`, differentiability, Jacobian, and null exceptional set are exactly your existing facts. If your transport lemma accepts domain-restricted proper maps, use it; otherwise prove this LE directly from the same change-of-variables machinery.

4. **Q4.** This is the main real obstruction.

Reason: `φ_i ⁻¹' {0}` is an exceptional divisor, not `{(0,0)}`. A pointwise lemma
`weightedProductMin_mono1D_of_ne` at `{(0,0)}` does not imply the threshold over the whole fibre. You need a fibre/compact-parameter version, or a separate uniform proof that the core threshold along every exceptional direction is at least the claimed value and is attained somewhere. Without that, the proposed chart-threshold identification is unsound.

5. **Q5.** Cheapest sound route:

1. Build `chartThreshold_eq_v_onExceptional`:
   ```lean
   weightedThreshold (F ∘ φ_i) (fun x => |det Dφ_i x|)
     (φ_i ⁻¹' {0} ∩ chartDom_i)
   = v
   ```
   Uses `pivotBlowupDeriv_det`, the factorization `F ∘ φ_i = y₀² * core_i`, and a new fibrewise/compact version of `weightedProductMin_mono1D_of_ne`.

2. Build/use `rlct_le_chartThreshold_i`:
   ```lean
   rlctAtOn F 0 ≤ chartThreshold_i
   ```
   Uses `weightedThreshold_le_transport` if available for restricted charts; otherwise `g5_step`, `pivotBlowupAt_image`, `pivotZero` null, and injectivity off `pivotZero`.

3. Build `rlct_ge_of_chartThresholds`:
   ```lean
   (∀ i, c < chartThreshold_i) →
     ∃ U, IsOpen U ∧ 0 ∈ U ∧ IntegrableOn (fun x => |F x| ^ (-c)) U volume
   ```
   Uses admissible `Ω_i`, compactness/shrinking of clipped chart domains, `argmaxCell_cover`, `argmaxCell_aedisjoint`, `g5_flat_cover`, and finite-sum finiteness.

**FLAGS:** hyperplane/fibre versus point is a genuine new obstruction. Domain reconciliation is not a wall only after shrinking `U` and clipping chart domains. Global properness of `pivotBlowupAt` is false; use restricted charts.