# Statement card — `fixedF_wide_cov_bound` (Lane 1 §1 CoV core, the fixed-F wide two-matrix CoV absorption bound)

**Claim.** Fixed-F wide two-matrix change-of-variables absorption bound (d1design's Lane-1 Gram-Schmidt route).
For a wide `F` (m≤n, entries in [−1,1], Gram-nonsingular / full row rank) and measurable `g`, the box integral of
`g(F·A₁)` over the free tail `A₁` is bounded by the free-F Gram Jacobian × an F-independent finite slack-box
volume × the W-box integral of `g`.

- **Lean.** `DLNFibre.DLN.RLCT.fixedF_wide_cov_bound`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFrontCoV.lean`, on `origin/genm-lane1-shell`; +309 LoC):

      theorem fixedF_wide_cov_bound {m n p : ℕ} (hmn : m ≤ n)
          (F : Fin m → Fin n → ℝ) (hFbox : ∀ i j, F i j ∈ Set.Icc (-1:ℝ) 1)
          (hFdet : (Matrix.of F * (Matrix.of F)ᵀ).det ≠ 0)
          (g : (Fin m → Fin p → ℝ) → ℝ≥0∞) (hg : Measurable g) :
          ∫⁻ A₁ in matBox n p 1, g (rmatMul F A₁)
            ≤ ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(p:ℝ)/2))
              * (ENNReal.ofReal ((2*(n:ℝ))^((n-m)*p)) * ∫⁻ W in matBox m p (n:ℝ), g W)

- **Gloss.** ∫_box g(F·A₁) ≤ (free-F Gram Jacobian `det(FFᵀ)^{−p/2}`) × (F-independent finite slack-box volume
  `(2n)^{(n−m)p}`) × (W-box integral of g).

- **Proved.** Sorry-free. Route (GS, NOT Cauchy-Binet): extend F to square `G=[F;S]` via
  `exists_ortho_complement_rows`; `(det G)²=det(FFᵀ)` via `det_gram_fromRows_of_orthonormal`; the **row-major
  left-mult CoV** `lintegral_comp_rmatMulLeft` (conjugate `mulLeftₚ p G` by the transpose LinearEquiv →
  `det=(det G)^p` via `LinearMap.det_conj` + `det_mulLeftₚ`, then `map_linearMap_addHaar` on the raw pi type —
  **sidesteps the transpose measure-preservation bridge**, the transpose enters only at the linear-algebra
  level); the exact box CoV via an **indicator** over `matBox n p n` (`A₁∈box(1) ⟹ G·A₁∈box(n)`, every
  G-entry |·|≤1) so the box→univ enlargement is the ONLY `≤` step; the bottom `(n−m)` slack rows Fubini out
  (`lintegral_topRows_box`) at cost `(2n)^{(n−m)p}`. NO `lintegral_box_le_absorption` (would enlarge to the
  infinite full space).

- **Also delivered (reusable):** `lintegral_comp_rmatMulLeft` (row-major left-mult CoV), `lintegral_topRows_box`
  (Fubini top-rows split), `transposeLE` (transpose LinearEquiv + apply lemmas).

- **Assumed.** m≤n (wide); F entries in [−1,1]; Gram-nonsingular (full row rank); g measurable.

- **Cited.** none. Consumes banked engine bricks `exists_ortho_complement_rows` (rowcomp),
  `det_gram_fromRows_of_orthonormal` (lane1shell).

- **Status.** sorry-free; clean-three `[propext, Classical.choice, Quot.sound]` (forced `#print axioms` on all
  three results); fidelity-reviewed PASS (independent reviewer + decorrelated Codex xhigh). Consumed by
  lane1shell's §1 a=0 bounded-base assembly.
