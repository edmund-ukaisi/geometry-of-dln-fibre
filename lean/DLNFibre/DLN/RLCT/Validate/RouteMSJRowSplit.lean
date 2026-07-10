import DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJRowSplit` — the leading-tail-layer row split (transport step b)

**Thread `genm-covfinish`, Stage 2 (S,J) CoV mountain, transport step (b).** The measure transport
(route A, `genm-covmount/codex/transport-answer.md`) splits the leading tail layer `A' 0 : M₁ × M₂`
into its pivot rows (the `t` rows fronted by `κ`) and its corank rows `W` (the remaining `M₁ − t`
rows), so the pivot-row integral can be handed to the translation atom
`sjGoodChartLoss_pivotRows_translate_eq` (`RouteMSJPivotTranslate`) while the corank rows `W` stay
fixed. This is the ONLY un-banked transport atom the `genm-covmount` handoff left (steps a and c were
banked as `tailParams_pi_split` / `sjGoodChartLoss_pivotRows_translate_eq`).

* **`rowSplitEquiv κ n`** — the measure-preserving row split `(Fin m → Fin n → ℝ) ≃ᵐ (Fin t → Fin n →
  ℝ) × (Fin (m − t) → Fin n → ℝ)`: reindex the rows by `blockSplitEquiv κ` (pivot rows first,
  `arrowCongr'`, MP), then split the `Fin t ⊕ Fin (m − t)` row sum into the two blocks
  (`sumPiEquivProdPi`, MP).
* **`rowSplitEquiv_reindex`** — `Sum.elim (rowSplitEquiv U).1 (rowSplitEquiv U).2 = fun I => U
  (blockSplitEquiv κ I)` (the reassembly is the row-reindexed matrix, = `U.submatrix (blockSplitEquiv
  κ) id`).
* **`rowSplitEquiv_preimage_box`** — the box factorization: `rowSplitEquiv ⁻¹' (matBox t n 1 ×ˢ
  matBox (m − t) n 1) = matBox m n 1` (`blockSplitEquiv κ` is a row bijection, so every row bounded
  iff both blocks bounded).
* **`rowSplit_lintegral_eq`** — the transport identity: for any `ℝ≥0∞`-valued `F` on the row-reindexed
  matrix, `∫_{U ∈ matBox m n 1} F (fun I => U (blockSplitEquiv κ I))` equals the product integral
  `∫_{(Upiv, W) ∈ matBox t n 1 ×ˢ matBox (m − t) n 1} F (Sum.elim Upiv W)`. Transport through the MP
  `rowSplitEquiv` (`setLIntegral_comp_preimage_emb`) + the box factorization.

The row-reindexed matrix `fun I => U (blockSplitEquiv κ I)` is definitionally `U.submatrix
(blockSplitEquiv κ) id`, so this atom directly rewrites the front factor `Ã₁ = (A' 0).submatrix
(blockSplitEquiv κ) id` that `gammaPeelIntegral_sjGoodMap_eq'` (`RouteMSJDeepFactor`) carries — and the
output `Sum.elim Upiv W` is the `Matrix.of (Sum.elim U W)` shape the translation atom consumes.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (MP Pi-reindex + Pi-sum-split + box preimage).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {t m n : ℕ}

/-- **The leading-layer row split** `(Fin m → Fin n → ℝ) ≃ᵐ (Fin t → Fin n → ℝ) × (Fin (m − t) → Fin
n → ℝ)`: reindex rows by `blockSplitEquiv κ` (pivot rows first), then split the `Fin t ⊕ Fin (m − t)`
row sum into the two matrix blocks. Measure-preserving (both factors are). -/
noncomputable def rowSplitEquiv (κ : Fin t ↪ Fin m) (n : ℕ) :
    (Fin m → Fin n → ℝ) ≃ᵐ (Fin t → Fin n → ℝ) × (Fin (m - t) → Fin n → ℝ) :=
  (MeasurableEquiv.arrowCongr' (blockSplitEquiv κ).symm (MeasurableEquiv.refl (Fin n → ℝ))).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin t ⊕ Fin (m - t) => Fin n → ℝ))

/-- `rowSplitEquiv` is measure-preserving (MP `arrowCongr'` then MP `sumPiEquivProdPi`). -/
theorem measurePreserving_rowSplitEquiv (κ : Fin t ↪ Fin m) (n : ℕ) :
    MeasurePreserving (rowSplitEquiv κ n)
      (volume : Measure (Fin m → Fin n → ℝ)) volume := by
  unfold rowSplitEquiv
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin t ⊕ Fin (m - t) => Fin n → ℝ))
  exact volume_preserving_arrowCongr' (blockSplitEquiv κ).symm (MeasurableEquiv.refl (Fin n → ℝ))
    (MeasurePreserving.id volume)

/-- The two blocks of `rowSplitEquiv κ n U` read the `blockSplitEquiv`-reindexed rows. -/
theorem rowSplitEquiv_fst (κ : Fin t ↪ Fin m) (n : ℕ) (U : Fin m → Fin n → ℝ) (i : Fin t) :
    (rowSplitEquiv κ n U).1 i = U (blockSplitEquiv κ (Sum.inl i)) := rfl

theorem rowSplitEquiv_snd (κ : Fin t ↪ Fin m) (n : ℕ) (U : Fin m → Fin n → ℝ) (i : Fin (m - t)) :
    (rowSplitEquiv κ n U).2 i = U (blockSplitEquiv κ (Sum.inr i)) := rfl

/-- The reassembly of the two blocks is the row-reindexed matrix `fun I => U (blockSplitEquiv κ I)`. -/
theorem rowSplitEquiv_reindex (κ : Fin t ↪ Fin m) (n : ℕ) (U : Fin m → Fin n → ℝ) :
    Sum.elim (rowSplitEquiv κ n U).1 (rowSplitEquiv κ n U).2
      = fun I => U (blockSplitEquiv κ I) := by
  funext I
  cases I with
  | inl i => rfl
  | inr i => rfl

/-- **The box factorization.** `rowSplitEquiv κ n ⁻¹' (matBox t n 1 ×ˢ matBox (m − t) n 1) = matBox m
n 1`: `blockSplitEquiv κ` is a bijection on rows, so every row of `U` is bounded iff both the pivot
block and the corank block are. -/
theorem rowSplitEquiv_preimage_box (κ : Fin t ↪ Fin m) (n : ℕ) :
    rowSplitEquiv κ n ⁻¹' (matBox t n 1 ×ˢ matBox (m - t) n 1) = matBox m n 1 := by
  ext U
  simp only [Set.mem_preimage, Set.mem_prod, matBox, Set.mem_setOf_eq, rowSplitEquiv_fst,
    rowSplitEquiv_snd]
  constructor
  · rintro ⟨hpiv, hcork⟩ I k
    obtain ⟨S, rfl⟩ := (blockSplitEquiv κ).surjective I
    cases S with
    | inl i => exact hpiv i k
    | inr i => exact hcork i k
  · intro h
    exact ⟨fun i k => h _ k, fun i k => h _ k⟩

/-- **The row-split transport identity (transport step b).** For any `ℝ≥0∞`-valued `F` on the
row-reindexed matrix, the leading-layer box integral over `U` equals the product integral over the
pivot block `Upiv` and the corank block `W`, with the row-reindexed matrix reassembled as `Sum.elim
Upiv W`. Transport through the MP `rowSplitEquiv` (`setLIntegral_comp_preimage_emb`) + the box
factorization (`rowSplitEquiv_preimage_box`); the reassembly identity `rowSplitEquiv_reindex`
identifies the substituted integrand. -/
theorem rowSplit_lintegral_eq (κ : Fin t ↪ Fin m) (n : ℕ)
    (F : ((Fin t ⊕ Fin (m - t)) → Fin n → ℝ) → ℝ≥0∞) :
    (∫⁻ U in matBox m n 1, F (fun I => U (blockSplitEquiv κ I)))
      = ∫⁻ p in matBox t n 1 ×ˢ matBox (m - t) n 1, F (Sum.elim p.1 p.2) := by
  have hmp := (measurePreserving_rowSplitEquiv κ n).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (rowSplitEquiv κ n))
    (fun p : (Fin t → Fin n → ℝ) × (Fin (m - t) → Fin n → ℝ) => F (Sum.elim p.1 p.2))
    (matBox t n 1 ×ˢ matBox (m - t) n 1)
  rw [rowSplitEquiv_preimage_box κ n] at hmp
  rw [← hmp]
  refine setLIntegral_congr_fun (matBox_measurableSet m n 1) (fun U _ => ?_)
  rw [rowSplitEquiv_reindex κ n U]

end DLNFibre.DLN.RLCT
