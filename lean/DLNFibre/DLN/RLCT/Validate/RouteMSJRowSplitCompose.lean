import DLNFibre.DLN.RLCT.Validate.RouteMSJTransport

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJRowSplitCompose` — the row-split composition (transport a+b)

**Thread `genm-mountain`, Stage 2 (S,J) CoV mountain, gap (1).** Composes the banked row-split
atom onto the entry point, producing the missing `gammaPeelIntegral_rowSplit_eq` the
`RouteMSJTransport` docstring names (C3 in the mountain recon): `gammaPeelIntegral` written as an
integral over the *split* leading layer — its `κ`-pivot rows `Upiv : t × M₂` and its corank rows
`W : (M₁−t) × M₂` — of the good-chart loss on the reassembled factor `Matrix.of (Sum.elim Upiv W)`.

The entry point `gammaPeelIntegral_piSplit_eq` (`RouteMSJTransport`) writes `gammaPeelIntegral` as
the nested integral over the leading layer `p.1 : M₁ × M₂` (row-reindexed by `blockSplitEquiv κ`)
and the deeper layers `p.2`. This module splits the leading layer's row axis by lifting the
measure-preserving `rowSplitEquiv κ n` (`RouteMSJRowSplit`) to the leading factor of the product
measure (`MeasurableEquiv.prodCongr … (refl deeper)`, MP via `MeasurePreserving.prod`) and
transporting the outer integral through it (`setLIntegral_comp_preimage_emb`, no integrand
measurability). The factorization `rowSplitEquiv_preimage_box` factors the leading box, and the
reassembly identity `rowSplitEquiv_reindex` (`Sum.elim … = fun I => U (blockSplitEquiv κ I)`)
matches the substituted integrand to the entry point's row-reindexed front factor.

The remaining step (c) — the pivot-row → free-`v` translation
(`sjGoodChartLoss_pivotRows_translate_eq`, `RouteMSJPivotTranslate`) — exposes `v` only once `Upiv`
is brought innermost (a Tonelli reorder past `W, deeper, x, Γ`). That reorder is NOT plumbing: it
is a genuine Fubini swap whose side-conditions need joint measurability of the pre-translation
integrand, which carries the matrix inverse `(of x.1.1)⁻¹` (the good-chart shear). It is deferred
to a dedicated measurability rung and is NOT proved here.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (MP product transport + defeq).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **Transport steps (a)+(b), composed (sorry-free EQUALITY).** `gammaPeelIntegral M t ρ κ c'`
equals the nested integral in which the leading tail layer is split, by `rowSplitEquiv κ`, into its
`κ`-pivot rows `q.1.1 : t × M₂` and its corank rows `q.1.2 : (M₁−t) × M₂`, with the deeper layers
`q.2` and the front factor reassembled as `Matrix.of (Sum.elim q.1.1 q.1.2)`. Transport the leading
factor of the `gammaPeelIntegral_piSplit_eq` product measure through the measure-preserving row
split `rowSplitEquiv κ n` (lifted by `MeasurableEquiv.prodCongr` over the deeper factor,
`setLIntegral_comp_preimage_emb`), factor the leading box (`rowSplitEquiv_preimage_box`), and match
the integrand by the reassembly identity `rowSplitEquiv_reindex`. No measurability side-conditions —
the product transport is measure-preserving. -/
theorem gammaPeelIntegral_rowSplit_eq (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ q in (matBox t ((tailChain M) ((0 : Fin (L + 1)).succ)) 1
            ×ˢ matBox (M 1 - t) ((tailChain M) ((0 : Fin (L + 1)).succ)) 1)
          ×ˢ {g : (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
              → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) |
              ∀ s i j, g s i j ∈ Set.Icc (-1 : ℝ) 1},
          ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
              ENNReal.ofReal
                ((sjGoodChartLoss x Γ (Matrix.of (Sum.elim q.1.1 q.1.2))
                    (sjDeepFactorCore M q.2)) ^ (-c')) := by
  rw [gammaPeelIntegral_piSplit_eq M t ρ κ c']
  -- Abbreviations matching the entry-point / target shapes.
  set n : ℕ := (tailChain M) ((0 : Fin (L + 1)).succ) with hn
  -- The deeper-layer type and its box `D`, and the target integrand `G` and domain `S`.
  set DT := (∀ s : Fin L, Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).castSucc)
      → Fin ((tailChain M) ((0 : Fin (L + 1)).succAbove s).succ) → ℝ) with hDT
  set D : Set DT := {g | ∀ s i j, g s i j ∈ Set.Icc (-1 : ℝ) 1} with hD
  set G : ((Fin t → Fin n → ℝ) × (Fin (M 1 - t) → Fin n → ℝ)) × DT → ℝ≥0∞ :=
    fun q => ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
          ENNReal.ofReal
            ((sjGoodChartLoss x Γ (Matrix.of (Sum.elim q.1.1 q.1.2))
                (sjDeepFactorCore M q.2)) ^ (-c')) with hG
  set S : Set (((Fin t → Fin n → ℝ) × (Fin (M 1 - t) → Fin n → ℝ)) × DT) :=
    (matBox t n 1 ×ˢ matBox (M 1 - t) n 1) ×ˢ D with hS
  -- The row split lifted to the leading factor of the product measure (measure-preserving).
  let e : ((Fin (M 1) → Fin n → ℝ) × DT) ≃ᵐ
      ((Fin t → Fin n → ℝ) × (Fin (M 1 - t) → Fin n → ℝ)) × DT :=
    (rowSplitEquiv κ n).prodCongr (MeasurableEquiv.refl DT)
  have he : MeasurePreserving (⇑e) (volume : Measure ((Fin (M 1) → Fin n → ℝ) × DT)) volume :=
    (measurePreserving_rowSplitEquiv κ n).prod (MeasurePreserving.id (volume : Measure DT))
  have hep : ∀ (u : Fin (M 1) → Fin n → ℝ) (d : DT), e (u, d) = (rowSplitEquiv κ n u, d) :=
    fun _ _ => rfl
  -- The transport identity from the measure-preserving embedding.
  have hmp := he.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding e) G S
  -- The product-box factorization: `e ⁻¹' S = matBox (M 1) n 1 ×ˢ D`.
  have hpre : (⇑e ⁻¹' S) = matBox ((tailChain M) ((0 : Fin (L + 1)).castSucc)) n 1 ×ˢ D := by
    ext p
    obtain ⟨u, d⟩ := p
    simp only [Set.mem_preimage, hep, hS, Set.mem_prod]
    constructor
    · rintro ⟨huv, hd⟩
      exact ⟨by
        have := rowSplitEquiv_preimage_box κ n
        rw [Set.ext_iff] at this
        exact (this u).mp huv, hd⟩
    · rintro ⟨hu, hd⟩
      refine ⟨?_, hd⟩
      have := rowSplitEquiv_preimage_box κ n
      rw [Set.ext_iff] at this
      exact (this u).mpr hu
  -- Transport the target RHS (`∫ q in S, G q`) back through the embedding, then match integrands.
  rw [← hmp, hpre]
  -- goal: `∫ p in (matBox … ×ˢ D), entryInner p = ∫ p in (matBox … ×ˢ D), G (e p)`.
  refine lintegral_congr fun p => ?_
  obtain ⟨u, d⟩ := p
  -- the reassembled front factor is the row-reindexed leading layer (`rowSplitEquiv_reindex`).
  have hfront : Matrix.of (Sum.elim (rowSplitEquiv κ n u).1 (rowSplitEquiv κ n u).2)
      = Matrix.submatrix u (blockSplitEquiv κ) id := by
    rw [rowSplitEquiv_reindex κ n u]; rfl
  change (∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
          ENNReal.ofReal ((sjGoodChartLoss x Γ (Matrix.submatrix u (blockSplitEquiv κ) id)
              (sjDeepFactorCore M d)) ^ (-c')))
    = ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
          ENNReal.ofReal ((sjGoodChartLoss x Γ
              (Matrix.of (Sum.elim (rowSplitEquiv κ n u).1 (rowSplitEquiv κ n u).2))
              (sjDeepFactorCore M d)) ^ (-c'))
  rw [hfront]

end DLNFibre.DLN.RLCT
