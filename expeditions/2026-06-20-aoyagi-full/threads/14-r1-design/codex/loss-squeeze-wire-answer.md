Use **option (iii)**: a post-telescoping, post-block bridge. Do not make `deepest_loss_squeeze` rerun the per-layer frame algebra. The bridge should expose fixed endpoint frames and a local per-`w` block cert.

```lean
(hframe_bridge :
  let wstar := (paramsEquivFlat H) (deepestPoint H r B hB hr hL)
  let e₁ := rThresholdSplit r (H 0) (hr 0)
  let e₂ := rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))
  ∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (Pi : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    (Qi : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ)
    (t : ℝ),
    Pi * P0 = 1 ∧ QL * Qi = 1 ∧
    ∃ U ∈ 𝓝 wstar, ∀ w ∈ U,
      ∃ (P00 : Matrix (Fin r) (Fin r) ℝ)
        (P01 : Matrix (Fin r) (Fin (H (Fin.last L) - r)) ℝ)
        (P10 : Matrix (Fin (H 0 - r)) (Fin r) ℝ)
        (P11 : Matrix (Fin (H 0 - r)) (Fin (H (Fin.last L) - r)) ℝ),
      ∃ hP00 : Invertible P00,
        letI : Invertible P00 := hP00
        let N := prod H ((paramsEquivFlat H).symm w) - B
        let Preg := Matrix.reindex e₁ e₂
          (prod H (framedParamsReg H r hr hL ((split w).1, (split w).2.2)))
        Matrix.reindex e₁ e₂ (P0 * N * QL)
          = Matrix.fromBlocks (P00 - 1) P01 P10 P11 ∧
        P00 = Preg.toBlocks₁₁ ∧ P01 = Preg.toBlocks₁₂ ∧ P10 = Preg.toBlocks₂₁ ∧
        (∑ i, ∑ j, ((P10 * ⅟P00 * P01) i j) ^ 2)
          ≤ t ^ 2 * (((∑ i, ∑ j, ((P00 - 1) i j) ^ 2)
            + (∑ i, ∑ j, (P01 i j) ^ 2))
            + (∑ i, ∑ j, (P10 i j) ^ 2)) ∧
        (∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2)
          = deepestCoreF H r
              ((deepestCoreAbsorb H r hr hL (split w)).2.1))
```

Then choose

```lean
Klo := (2 * (1 + t^2)) *
  ((∑ i, ∑ k, (P0 i k)^2) * (∑ j, ∑ k, (QL k j)^2))
Kup := ((∑ i, ∑ k, (Pi i k)^2) * (∑ j, ∑ k, (Qi k j)^2)) *
  (2 + 2*t^2)

c₁ := Klo⁻¹
c₂ := Kup
```

Per `w`:

```lean
rcases hbr w hw with ⟨P00,P01,P10,P11,hP00,hconj,h00,h01,h10,hleak,hcore⟩
letI := hP00
let N := prod H ((paramsEquivFlat H).symm w) - B

obtain ⟨hlo,hhi⟩ :=
  dlnLoss_two_sided_of_frame N P0 QL Pi Qi hP hQ e₁ e₂
    P00 P01 P10 P11 t hconj hleak
```

Build `hclean_eq_Φ` by `rw [hregval (split w), hcoreabs]`; use
`deepestEPivot_sq_sum_eq_blocks H r hr hL ((split w).1,(split w).2.2)` and `h00,h01,h10` for the regular block, and `hcore` for the core. Then rewrite `hlo/hhi`, unfold `dlnLoss`, and finish lower by multiplying `hlo : Φ ≤ Klo * loss` by `Klo⁻¹`; upper is `hhi` plus associativity.

Most likely wall: **the core equality**. Repo comments say full-product Schur `P11 - P10*⅟P00*P01` is not generally the same as the absorbed per-layer Schur core; they agree only modulo regular leakage. Fallback: replace the final equality by local comparability `γ₁*Φ ≤ cleanEnergy ∧ cleanEnergy ≤ γ₂*Φ`, then use `c₁ := γ₁ / Klo`, `c₂ := Kup * γ₂`.