import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotDom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotFin` — GLUE-2 (b): the pivot→`decLoss` finiteness

**Thread `genm-sj5` (aoyagi-full Stage 2), the analytic CRUX of the head-split (GLUE-2).**
`pivotDom_finiteness_impl` reproduces the `RouteMSJPivotDom.pivotDom_finiteness` stub signature VERBATIM;
the controller wires the stub to it.

## Sound decomposition (Option B, locked with the controller, 2026-07-13)

The crux `pivotDomRHS < ⊤ → pivotDomLHS < ⊤` is the σ-coupled DOMINATION, properly hypothesised on the
RHS finiteness `hRHS` (which — via the reduced-chain comparator shape — carries exactly the reduced-chain
box-finiteness the `z`-integral needs; the earlier "extract `c' < X` from `hRHS` then re-derive `LHS < ⊤`
self-contained" split was an artefact of the failed uniform-`C_hle` attempt, since `c' < X` ALONE lacks the
reduced-chain finiteness — that lives in `hRHS`):

* **Forward finiteness** `forward_LHS_finiteness` (the ISOLATED CRUX). `pivotDomRHS < ⊤ ⟹ pivotDomLHS < ⊤`.
  The genuine bilinear-RLCT: `freedLoss = Σ_i σ_i(z,A_cor)²·|β_i|²` (SVD/eigenframe of `Q_stack`, Brick F),
  σ-coupled peel RETAINING the `σ_i(z,A_cor)`-dependence (a uniform pivot pull-out DIVERGES — archfin +
  Codex). Degenerating small-`σ_i` directions charge the corank `ab` (S3 `shell_corankOffSector_le_unif`,
  `Ccross`-uniform) + the reduced-chain via `hRHS`; `σ_i`-bounded-below directions give the uniform pivot
  capacity `uρ`, non-binding by `hpiv` (`uρ ≥ minAdm(redChain u M)`). Yields `pivotDomLHS ≤ C·pivotDomRHS`
  (`C < ⊤`), closed by `hRHS`.

* **`u = 0` edge** `pivotDom_finiteness_uzero`: the `0`-width pivot makes the front block vanish
  (`freedSchurLoss = ‖Γ·Q_b‖²`) and `decLoss = 0`, so `pivotDomLHS ≤ pivotDomRHS` (`pivotDom_uzero`) — no
  pivot energy, not the analytic crux.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The `matBox` volume** `= ofReal(2ρ)^{a·b}` (for `ρ ≥ 0`). Nested `volume_pi_pi` + `Real.volume_Icc`. -/
theorem matBox_volume (a b : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (matBox a b ρ) = ENNReal.ofReal (2 * ρ) ^ (a * b) := by
  have hset : matBox a b ρ
      = Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => Set.Icc (-ρ) ρ)) := by
    ext X
    simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hset, MeasureTheory.volume_pi_pi]
  have hinner : ∀ _i : Fin a,
      volume (Set.univ.pi (fun _ : Fin b => Set.Icc (-ρ) ρ)) = ENNReal.ofReal (2 * ρ) ^ b := by
    intro _
    rw [MeasureTheory.volume_pi_pi]
    simp only [Real.volume_Icc]
    rw [show ρ - -ρ = 2 * ρ by ring, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_congr rfl (fun i _ => hinner i),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- **The corner sublevel-volume lower bound.** For `w > 0` and a `Γ`-box of radius `ρ ≤ 1` on which
`frobSq(Γ·(A·Z)) ≤ w` (uniformly over `A ∈ matBox`), the corank inner integral dominates
`(2w)^{−c'}·(2ρ)^{ab}·vol(matBox b M₂ 1)`: restrict `Γ` to `matBox a b ρ ⊆ genBox`, use the pointwise
`(w+frobSq)^{−c'} ≥ (2w)^{−c'}` and `matBox_volume`. The `(2ρ)^{ab}` scaling is what produces the `ab/2`
threshold shift downstream. -/
theorem corner_inner_ge {a b M₂ nn : ℕ} (Z : Matrix (Fin M₂) (Fin nn) ℝ) {c' : ℝ} (hc0 : 0 ≤ c')
    {w ρ : ℝ} (hw : 0 < w) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbound : ∀ A : Fin b → Fin M₂ → ℝ, A ∈ matBox b M₂ 1 →
      ∀ Γ : Fin a → Fin b → ℝ, Γ ∈ matBox a b ρ →
        frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z)) ≤ w) :
    ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b) * volume (matBox b M₂ 1)
      ≤ ∫⁻ A in matBox b M₂ 1, ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) := by
  have hsub : matBox a b ρ ⊆ genBox (Fin a) (Fin b) 1 := by
    intro Γ hΓ i k
    have := hΓ i k
    rw [Set.mem_Icc] at this ⊢
    constructor <;> [nlinarith [this.1]; nlinarith [this.2]]
  -- per-`A` inner lower bound
  have hinner : ∀ A : Fin b → Fin M₂ → ℝ, A ∈ matBox b M₂ 1 →
      ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b)
        ≤ ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
            ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) := by
    intro A hA
    calc ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b)
        = ENNReal.ofReal ((2 * w) ^ (-c')) * volume (matBox a b ρ) := by
          rw [matBox_volume a b hρ0.le]
      _ = ∫⁻ _Γ in matBox a b ρ, ENNReal.ofReal ((2 * w) ^ (-c')) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ Γ in matBox a b ρ,
            ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) := by
          refine setLIntegral_mono_ae' (matBox_measurableSet a b ρ) (ae_of_all _ (fun Γ hΓ => ?_))
          refine ENNReal.ofReal_le_ofReal ?_
          have hfnn : (0 : ℝ) ≤ frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z)) := frobSq_nonneg _
          have hle : w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z)) ≤ 2 * w := by
            have := hbound A hA Γ hΓ; linarith
          exact Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
      _ ≤ ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
            ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) :=
          lintegral_mono_set hsub
  calc ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b) * volume (matBox b M₂ 1)
      = ∫⁻ _A in matBox b M₂ 1,
          ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ A in matBox b M₂ 1, ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) :=
        setLIntegral_mono_ae' (matBox_measurableSet b M₂ 1) (ae_of_all _ (fun A hA => hinner A hA))

/-- **Entrywise upper bound for the corank block** `frobSq(Γ·(A·Z)) ≤ (a·nn)·(b·M₂·BZ)²·ρ²` when
`|Γ| ≤ ρ`, `|A| ≤ 1`, `|Z| ≤ BZ` entrywise. Per-entry triangle bound `|(Γ·(A·Z))_{ij}| ≤ b·ρ·M₂·BZ`, then
`frobSq ≤ card · (entry bound)²`. Supplies `corner_inner_ge`'s `hbound` with `ρ ~ √(w/C)`. -/
theorem frobSq_corank_le {a b M₂ nn : ℕ} (Z : Matrix (Fin M₂) (Fin nn) ℝ)
    {BZ : ℝ} (hBZ0 : 0 ≤ BZ) (hBZ : ∀ l j, |Z l j| ≤ BZ)
    (A : Fin b → Fin M₂ → ℝ) (hA : ∀ k l, |A k l| ≤ 1)
    (Γ : Fin a → Fin b → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hΓ : ∀ i k, |Γ i k| ≤ ρ) :
    frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))
      ≤ ((a * nn : ℕ) : ℝ) * (b * M₂ * BZ) ^ 2 * ρ ^ 2 := by
  classical
  set W : Matrix (Fin b) (Fin nn) ℝ := (Matrix.of A) * Z with hW
  -- entry bound on `W = A·Z`
  have hWentry : ∀ k j, |W k j| ≤ (M₂ : ℝ) * BZ := by
    intro k j
    have : W k j = ∑ l, A k l * Z l j := by simp [hW, Matrix.mul_apply, Matrix.of_apply]
    rw [this]
    calc |∑ l, A k l * Z l j| ≤ ∑ l, |A k l * Z l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin M₂, (1 : ℝ) * BZ := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hA k l) (hBZ l j) (abs_nonneg _) (by norm_num)
      _ = (M₂ : ℝ) * BZ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- entry bound on `Γ·W`
  have hprodentry : ∀ i j, |((Matrix.of Γ) * W) i j| ≤ (b : ℝ) * ρ * ((M₂ : ℝ) * BZ) := by
    intro i j
    have : ((Matrix.of Γ) * W) i j = ∑ k, Γ i k * W k j := by
      simp [Matrix.mul_apply, Matrix.of_apply]
    rw [this]
    calc |∑ k, Γ i k * W k j| ≤ ∑ k, |Γ i k * W k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin b, ρ * ((M₂ : ℝ) * BZ) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hΓ i k) (hWentry k j) (abs_nonneg _) hρ0
      _ = (b : ℝ) * ρ * ((M₂ : ℝ) * BZ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- `frobSq ≤ card · (entry bound)²`
  have hE0 : (0 : ℝ) ≤ (b : ℝ) * ρ * ((M₂ : ℝ) * BZ) := by positivity
  calc frobSq ((Matrix.of Γ) * W)
      = ∑ i, ∑ j, (((Matrix.of Γ) * W) i j) ^ 2 := rfl
    _ ≤ ∑ _i : Fin a, ∑ _j : Fin nn, ((b : ℝ) * ρ * ((M₂ : ℝ) * BZ)) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        have := hprodentry i j
        nlinarith [abs_nonneg (((Matrix.of Γ) * W) i j), sq_abs (((Matrix.of Γ) * W) i j), hE0, this]
    _ = ((a * nn : ℕ) : ℝ) * (b * M₂ * BZ) ^ 2 * ρ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- **The comparator `decLoss` at the clean data** `k = ![1]`: `decLoss v z = (v 0)²·frobSq(prod z)`
(`commonDivisor = |v 0|^1`). Isolates the `cornerComparator` instance setup (`fι/fν/Nonempty ι`), computing
`sharedDivisorExp = 1` directly (`Finset.inf'_const`, uniform support). -/
theorem pivotRHS_decLoss_eq (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u) (hnd : ∀ i, 1 ≤ M i)
    (v : Fin 1 → ℝ) (z : Params (redChain u M)) :
    (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).decLoss v z
      = (v 0) ^ 2 * frobSq (prod (redChain u M) z) := by
  have hu1 : 0 < redChain u M 0 := by rw [redChain_zero]; omega
  have hlast1 : 0 < redChain u M (Fin.last (L + 1)) := by
    rw [show redChain u M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) by
      rw [← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]]
    exact hnd _
  set i₀ : Fin (redChain u M 0) × Fin (redChain u M (Fin.last (L + 1)))
      := (⟨0, hu1⟩, ⟨0, hlast1⟩) with hi₀
  letI := (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).fι
  letI := (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).fν
  haveI hne : Nonempty (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).ι := ⟨i₀⟩
  haveI hne0 : NeZero (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).d :=
    ⟨by rw [show (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).d = 1 from rfl]; omega⟩
  haveI hss : Subsingleton (Fin (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).d) := by
    rw [show (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).d = 1 from rfl]; infer_instance
  rw [cornerComparator_decLoss (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) i₀ v z]
  have hcd : commonDivisor (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).carrier.supp v = |v 0| := by
    unfold commonDivisor
    rw [Fintype.prod_subsingleton _
      (0 : Fin (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).d)]
    have he0 : sharedDivisorExp (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).carrier.supp
        (0 : Fin (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
          (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).d) = 1 := by
      rw [cornerComparator_sharedDivisorExp (redChain u M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) i₀]
      rfl
    rw [he0, pow_one]
    rfl
  rw [hcd, sq_abs]

/-- **Reformulation: the freed Schur loss is the full-block loss (on the chart).** On `outerDom`
(`IsUnit (Matrix.of x.1.1)`), the freed Schur loss equals the plain block loss of the reconstructed
block matrix `[[P, B₁₂], [C, Γ + schurShift x]]` against `Q`. The Schur / `P⁻¹` coupling CANCELS: the
freed loss was the block loss all along, re-parametrised. Banked `schurLoss_of_blockSplitD_symm_shift`
(freed = `schurLoss` of the reconstructed block) + `frobSq_schur_split_inv` (`schurLoss = frobSq(·)` on
`IsUnit` pivot). Turns the σ-coupled peel into a clean block-front RLCT integral (the `(2,2)` block
`D := Γ + schurShift x` ranges over `genBox` as `Γ` ranges over the shifted set). -/
theorem freedSchurLoss_eq_frobSq_block {t a b q : ℕ} (x : SJOuter t a b)
    (hP : IsUnit (Matrix.of x.1.1)) (Γ : Fin a → Fin b → ℝ)
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    freedSchurLoss x Γ Q
      = frobSq (Matrix.of ((blockSplitD t a b).symm (x, Γ + schurShift x)) * Q) := by
  have hblk : (Matrix.of ((blockSplitD t a b).symm (x, Γ + schurShift x))).toBlocks₁₁
      = Matrix.of x.1.1 := by
    rw [of_blockSplitD_symm_eq_fromBlocks]; rfl
  have hU' : IsUnit (Matrix.of ((blockSplitD t a b).symm (x, Γ + schurShift x))).toBlocks₁₁ := by
    rw [hblk]; exact hP
  rw [← schurLoss_of_blockSplitD_symm_shift x Γ Q]
  exact (frobSq_schur_split_inv _ hU' Q).symm

/-- **Row-split of `frobSq` over a `⊕`-indexed row type.** `frobSq X = frobSq (top rows) + frobSq
(bottom rows)` — the Frobenius square of a row-block-stacked matrix is the sum of the row-blocks'
Frobenius squares (`Fintype.sum_sum_type`). Feeds the pivot(top-`Fin u`)/corank(bottom-`Fin a`) separation
of the block-front loss `frobSq(fromBlocks P B₁₂ C D · Q_stack)` in the peel scaffold. -/
theorem frobSq_sum_rows {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (X : Matrix (α ⊕ β) γ ℝ) :
    frobSq X = frobSq (X.submatrix Sum.inl id) + frobSq (X.submatrix Sum.inr id) := by
  unfold frobSq
  rw [Fintype.sum_sum_type (fun i => ∑ j, (X i j) ^ 2)]
  simp only [Matrix.submatrix_apply, id_eq]

/-- **Step 1 — the `D`-substitution (translation change-of-variables).** The freed-`Γ` inner integral
(domain `{Γ | Γ + schurShift x ∈ genBox}`) equals the block-front integral over the raw `(2,2)`-block
`D ∈ genBox`: reformulate the integrand (`freedSchurLoss_eq_frobSq_block`, needs `IsUnit P`), then
substitute `D := Γ + schurShift x` — a measure-preserving translation on the RAW pi type
`Fin a → Fin b → ℝ` (`measurePreserving_add_right`, NO `Matrix.module` diamond since `Γ`/`genBox`/
`schurShift` are all raw functions). `setLIntegral_comp_preimage_emb` on the translation embedding. -/
theorem pivotInner_Dsubst {t a b q : ℕ} (x : SJOuter t a b) (hP : IsUnit (Matrix.of x.1.1))
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' : ℝ) :
    (∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) 1},
        ENNReal.ofReal (freedSchurLoss x Γ Q ^ (-c')))
      = ∫⁻ D in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD t a b).symm (x, D)) * Q) ^ (-c')) := by
  have hmp : MeasurePreserving (fun Γ : Fin a → Fin b → ℝ => Γ + schurShift x) volume volume :=
    measurePreserving_add_right volume (schurShift x)
  have hemb : MeasurableEmbedding (fun Γ : Fin a → Fin b → ℝ => Γ + schurShift x) :=
    (Homeomorph.addRight (schurShift x)).measurableEmbedding
  calc (∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) 1},
          ENNReal.ofReal (freedSchurLoss x Γ Q ^ (-c')))
      = ∫⁻ Γ in (fun Γ : Fin a → Fin b → ℝ => Γ + schurShift x) ⁻¹' (genBox (Fin a) (Fin b) 1),
          ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD t a b).symm (x, Γ + schurShift x)) * Q)
            ^ (-c')) := by
        refine lintegral_congr fun Γ => ?_
        rw [freedSchurLoss_eq_frobSq_block x hP Γ Q]
    _ = ∫⁻ D in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD t a b).symm (x, D)) * Q) ^ (-c')) :=
        hmp.setLIntegral_comp_preimage_emb hemb
          (fun D => ENNReal.ofReal
            (frobSq (Matrix.of ((blockSplitD t a b).symm (x, D)) * Q) ^ (-c')))
          (genBox (Fin a) (Fin b) 1)

/-- **Step 2-prep — the block-front row-split.** `frobSq(fromBlocks P B₁₂ C D · Q_stack)` splits into
the pivot (top rows `(P|B₁₂)`) energy `frobSq(P·Q_p + B₁₂·Q_b)` plus the corank (bottom rows `(C|D)`)
energy `frobSq(C·Q_p + D·Q_b)`, with `Q_p = Q.submatrix Sum.inl id`, `Q_b = Q.submatrix Sum.inr id`.
`frobSq_sum_rows` + the block-row identities (`Fintype.sum_sum_type` on the product's `⊕`-column sum
via `fromBlocks_apply₁₁/₁₂/₂₁/₂₂`). Feeds D-A-radial (top) + S3-corank (bottom). -/
theorem blockFront_rowSplit {t a b q : ℕ} (P : Matrix (Fin t) (Fin t) ℝ)
    (B12 : Matrix (Fin t) (Fin b) ℝ) (C : Matrix (Fin a) (Fin t) ℝ) (D : Matrix (Fin a) (Fin b) ℝ)
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    frobSq (Matrix.fromBlocks P B12 C D * Q)
      = frobSq (P * Q.submatrix Sum.inl id + B12 * Q.submatrix Sum.inr id)
        + frobSq (C * Q.submatrix Sum.inl id + D * Q.submatrix Sum.inr id) := by
  rw [frobSq_sum_rows]
  have htop : (Matrix.fromBlocks P B12 C D * Q).submatrix Sum.inl id
      = P * Q.submatrix Sum.inl id + B12 * Q.submatrix Sum.inr id := by
    ext i k
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Matrix.add_apply]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  have hbot : (Matrix.fromBlocks P B12 C D * Q).submatrix Sum.inr id
      = C * Q.submatrix Sum.inl id + D * Q.submatrix Sum.inr id := by
    ext i k
    simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, Matrix.add_apply]
    rw [Fintype.sum_sum_type]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [htop, hbot]

/-- **The σ-coupled S3-variant (the ISOLATED new lemma; STATEMENT for review, fill pending).** The
corank `(A_cor, Γ)` integral with an A_cor-DEPENDENT pivot weight `wf A_cor` — S3's per-`A_cor` corank
charge (`corankBlock_morsePeel_setLE` at `Apiv = 0`, valid for ANY `w > 0`) integrated over `A_cor`
WITHOUT the A_cor-free pull-out (the banked `shell_corankOffSector_le_unif` requires `w` A_cor-free; the
head-split's `w = frobSq([P|B₁₂]·Q_stack)` depends on `A_cor` via `Q_b = A_cor·Z`, so the pull-out is the
unsound one archfin ruled out). The `½ab` charge appears as the Gram divisor `det((A_cor·Z)(A_cor·Z)ᵀ)^{−a/2}`
and the exponent shift `c' → c'−½ab`, with `wf A_cor` and the divisor left COUPLED inside the `A_cor`
integral — the coupled residual is bounded downstream (D-A radial for `wf` + couplingfin's shell/transversality).
PLAN: `corank_survival_ae Z hbZ` (`A_cor·Z` full row-rank a.e.) → per such `A_cor`,
`corankBlock_morsePeel_setLE (Apiv := 0) (Ccross) (Qb := A_cor·Z) (posDef_gram_of_rank_eq …) c' hc' (wf A_cor)
(hwf A_cor) sΓ` (the `frobSq 0 = 0` term drops) → `lintegral_mono_ae`.

INDEX PINNING (couplingfin's `½ab`): `a = Ccross rows = Γ rows = M₀−u` (the corank/`D` rows), `b = A_cor
rows = Γ cols = (A_cor·Z) rows = M₁−u`; the atom's `p·q = a·b`, matching `½ab` (the charge is `a,b`-symmetric).
DOWNSTREAM (not this lemma): the hypothesis `ab/2 < c'` is the shifted-exponent validity — the assembly must
discharge it in the good-branch shell regime, and route the `c' ≤ ab/2` shells (less singular corner) through
a cruder no-shift bound. `_hgm` (`Measurable wf`) is statement hygiene (the bound holds regardless — the
downstream `wf` = the post-D-A-radial pivot energy is measurable). -/
theorem shell_corankPivot_coupled_le {a b M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (hbZ : b ≤ Z.rank) (c' : ℝ) (hc' : (a * b : ℝ) / 2 < c')
    (Ccross : Matrix (Fin a) (Fin n) ℝ)
    (wf : (Fin b → Fin M₂ → ℝ) → ℝ) (hwf : ∀ A_cor, 0 < wf A_cor) (_hgm : Measurable wf)
    (sΓ : Set (Fin a → Fin b → ℝ)) :
    (∫⁻ A_cor in matBox b M₂ 1, ∫⁻ Γ in sΓ,
        ENNReal.ofReal
          ((wf A_cor + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c')))
      ≤ ∫⁻ A_cor in matBox b M₂ 1,
          ENNReal.ofReal
            (((Matrix.of A_cor * Z) * (Matrix.of A_cor * Z)ᵀ).det ^ (-(a : ℝ) / 2)
              * Cresid (a * b) c'
              * (wf A_cor + frobSq (Ccross * (1 - (Matrix.of A_cor * Z)ᵀ
                  * ((Matrix.of A_cor * Z) * (Matrix.of A_cor * Z)ᵀ)⁻¹ * (Matrix.of A_cor * Z))))
                ^ (-(c' - (a * b : ℝ) / 2))) := by
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hfz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
  refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
  filter_upwards [corank_survival_ae Z hbZ] with A hrank _hAbox
  have hPD := posDef_gram_of_rank_eq (Matrix.of A * Z) hrank
  have hatom := corankBlock_morsePeel_setLE (Apiv := (0 : Matrix (Fin 0) (Fin n) ℝ))
    (Ccross := Ccross) (Qb := Matrix.of A * Z) hPD c' hc' (wf A) (hwf A) sΓ
  simpa only [hfz, add_zero] using hatom

/-- **The block-front reduction of `pivotDomLHS` (scaffold, cert-free).** Threading `pivotInner_Dsubst`
(step 1) through the outer `(z, A_cor)` integrals (per `x ∈ outerDom`, so `IsUnit P` holds via the 4th
`outerDom` conjunct) rewrites the freed-`Γ` spine as the clean block-front integral over the raw `(2,2)`
block `D ∈ genBox`. This is the concrete starting point the σ-coupled analytic core (D-A-radial + S3 +
C-absorption) attaches to; the core then applies `of_blockSplitD_symm_eq_fromBlocks` + `blockFront_rowSplit`
pointwise to expose the pivot(top)/corank(bottom) split. -/
theorem pivotDomLHS_eq_blockFront (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (ε : ℝ) (c' : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) :
    pivotDomLHS M u ε c' Zf
      = ∫⁻ z in paramsBoxM (redChain u M) 1,
          ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1 ∩ pivotShell M u ε Zf z,
            ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
              ∫⁻ D in genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1,
                ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD u (M 0 - u) (M 1 - u)).symm (x, D))
                  * hsQ M u Zf z A_cor) ^ (-c')) := by
  unfold pivotDomLHS
  refine lintegral_congr fun z => ?_
  refine lintegral_congr fun A_cor => ?_
  refine setLIntegral_congr_fun (measurableSet_outerDom u (M 0 - u) (M 1 - u) 1) (fun x hx => ?_)
  exact pivotInner_Dsubst x hx.2.2.2 (hsQ M u Zf z A_cor) c'

/-! ## The full-block finiteness route (S3-free crux, approved 2026-07-14)

The crux `pivotPeel_domination` reduces — via the generic `ℝ≥0∞` ratio trick — to `pivotDomRHS < ⊤ →
pivotDomLHS < ⊤`. On the `pivotShell` the ENTIRE block `T = [[P,B₁₂],[C,D]]` maps through the
uniformly-full-row-rank `Q_stack = hsQ`, giving a joint full-block Loewner floor `frobSq (T·Q) ≥ ε²·frobSq T`
(`frobSq_mul_ge_of_gramFloor`); a crude pure-cube bound then wins, WITHOUT the S3 corank peel. The
`c'`-threshold is supplied by the comparator-side divergence `pivotDomRHS_eq_top_of_critical`, and the nat
chain `minAdm_add_peel_le` closes it against the block dimension `(u+a)·(u+b)` via `hpiv`. Design:
`s1-Chle-angular-integrability-cert` §8 + the S3-free simplification (Codex xhigh corroborated, 2026-07-14). -/

/-- **Generic `ℝ≥0∞` ratio trick.** If `R ≠ 0` and `R < ⊤ → L < ⊤`, then `∃ C < ⊤, L ≤ C · R`
(`C := 1` if `R = ⊤`, else `C := L / R` via `ENNReal.div_mul_cancel`). -/
theorem exists_finite_mul_of_finite_imp {L R : ℝ≥0∞} (hR0 : R ≠ 0) (hfin : R < ⊤ → L < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ L ≤ C * R := by
  by_cases htop : R = ⊤
  · exact ⟨1, ENNReal.one_lt_top, by rw [one_mul, htop]; exact le_top⟩
  · have hRlt : R < ⊤ := lt_top_iff_ne_top.mpr htop
    have hL : L < ⊤ := hfin hRlt
    exact ⟨L / R, ENNReal.div_lt_top hL.ne hR0, by rw [ENNReal.div_mul_cancel hR0 htop]⟩

/-- **The joint full-block Loewner floor.** If the column-Gram of `Q` is floored, `Q·Qᵀ ⪰ ε²·1`, then the
whole-block product energy is floored: `ε²·frobSq T ≤ frobSq (T·Q)`, for ANY `T`. Per row `v = T i`:
`∑ₖ ((T·Q) i k)² = v ⬝ᵥ ((Q·Qᵀ) *ᵥ v) ≥ ε²·(v ⬝ᵥ v)` (the PSD quadratic form); sum over rows. -/
theorem frobSq_mul_ge_of_gramFloor {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq κ]
    (T : Matrix ι κ ℝ) (Q : Matrix κ ν ℝ) {ε : ℝ}
    (hfloor : (Q * Qᵀ - (ε ^ 2) • (1 : Matrix κ κ ℝ)).PosSemidef) :
    (ε ^ 2) * frobSq T ≤ frobSq (T * Q) := by
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hfloor).2
  have hrow : ∀ i, (ε ^ 2) * (∑ j, (T i j) ^ 2) ≤ ∑ k, ((T * Q) i k) ^ 2 := by
    intro i
    -- the `i`-th row of `T·Q` is `T i ᵥ* Q`
    have hval : ∀ k, (T * Q) i k = (T i ᵥ* Q) k := by
      intro k; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    have hsum : (∑ k, ((T * Q) i k) ^ 2) = (T i ᵥ* Q) ⬝ᵥ (T i ᵥ* Q) := by
      rw [dotProduct]
      exact Finset.sum_congr rfl (fun k _ => by rw [hval k]; ring)
    have hvv : (T i) ⬝ᵥ (T i) = ∑ j, (T i j) ^ 2 := by
      rw [dotProduct]; exact Finset.sum_congr rfl (fun j _ => (sq (T i j)).symm)
    have hstar : star (T i) = T i := by funext j; exact star_trivial (T i j)
    have key : (ε ^ 2) * ((T i) ⬝ᵥ (T i)) ≤ (T i ᵥ* Q) ⬝ᵥ (T i ᵥ* Q) := by
      have h := hquad (T i)
      rw [hstar] at h
      have e1 : (Q * Qᵀ - (ε ^ 2) • (1 : Matrix κ κ ℝ)) *ᵥ (T i)
          = (Q * Qᵀ) *ᵥ (T i) - (ε ^ 2) • (T i) := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [e1, dotProduct_sub, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at h
      linarith
    rw [hsum, ← hvv]; exact key
  calc (ε ^ 2) * frobSq T
      = ∑ i, (ε ^ 2) * (∑ j, (T i j) ^ 2) := by rw [frobSq, Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, ((T * Q) i k) ^ 2 := Finset.sum_le_sum (fun i _ => hrow i)
    _ = frobSq (T * Q) := rfl

/-- **Pure-cube matrix-box finiteness.** For `0 < c' < (p·q)/2`, the pure squared-Frobenius power is
integrable over the matrix box: `∫_{matBox p q 1} frobSq(of T)^{−c'} < ⊤`. Flatten `matReshapeEquiv`
(measure-preserving) → cube `[−1,1]^{p·q}`, then the banked `lintegral_box_sq_neg_lt_top`. -/
theorem matBox_frobSq_neg_lintegral_lt_top {p q : ℕ} {c' : ℝ} (hc0 : 0 < c')
    (hpq : c' < ((p * q : ℕ) : ℝ) / 2) :
    (∫⁻ T in matBox p q 1, ENNReal.ofReal (frobSq (Matrix.of T) ^ (-c'))) < ⊤ := by
  have hpq0 : 0 < p * q := by
    rcases Nat.eq_zero_or_pos (p * q) with h | h
    · exfalso; rw [h] at hpq; simp only [Nat.cast_zero, zero_div] at hpq; linarith
    · exact h
  set e := matReshapeEquiv p q with he
  have hmp := measurePreserving_matReshapeEquiv p q
  -- the flattened coordinate reads off the matrix entry
  have hval : ∀ (T : Fin p → Fin q → ℝ) (ij : Fin p × Fin q), e T (finProdFinEquiv ij) = T ij.1 ij.2 := by
    intro T ij
    rw [← matReshapeEquiv_symm_apply p q (e T) ij.1 ij.2, he, (matReshapeEquiv p q).symm_apply_apply]
  -- `frobSq` is the flattened squared norm
  have heq : ∀ T : Fin p → Fin q → ℝ, frobSq (Matrix.of T) = ∑ k, (e T k) ^ 2 := by
    intro T
    have hsplit : (∑ k, (e T k) ^ 2)
        = ∑ i, ∑ j, (e T (finProdFinEquiv (i, j))) ^ 2 := by
      rw [← Equiv.sum_comp finProdFinEquiv (fun k => (e T k) ^ 2), Fintype.sum_prod_type]
    rw [hsplit, frobSq]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => by rw [Matrix.of_apply, hval T (i, j)]))
  -- the matrix box is the flat cube's preimage
  have hbox : matBox p q 1
      = e ⁻¹' (Set.univ.pi (fun _ : Fin (p * q) => Set.Icc (-1 : ℝ) 1)) := by
    ext T
    simp only [matBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h k
      obtain ⟨ij, rfl⟩ := finProdFinEquiv.surjective k
      rw [hval T ij]; exact h ij.1 ij.2
    · intro h i j
      have := h (finProdFinEquiv (i, j)); rwa [hval T (i, j)] at this
  -- transport to the flat cube and apply the banked finiteness
  rw [show (∫⁻ T in matBox p q 1, ENNReal.ofReal (frobSq (Matrix.of T) ^ (-c')))
        = ∫⁻ T in matBox p q 1, ENNReal.ofReal ((∑ k, (e T k) ^ 2) ^ (-c')) from
      setLIntegral_congr_fun (matBox_measurableSet p q 1) (fun T _ => by rw [heq T])]
  rw [hbox, hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun y => ENNReal.ofReal ((∑ k, (y k) ^ 2) ^ (-c')))
    (Set.univ.pi (fun _ : Fin (p * q) => Set.Icc (-1 : ℝ) 1))]
  exact lintegral_box_sq_neg_lt_top hpq0 1 hc0.le hpq

/-- **The full-block shell bound (the checkpoint lemma).** On the shell (`Q·Qᵀ ⪰ ε²·1`), the block-front
integral over the block box is dominated by a `Q`-UNIFORM constant `ε^{−2c'}·(pure-cube)`: apply the
Loewner floor pointwise (`frobSq_mul_ge_of_gramFloor`), then reindex the block box to `matBox (u+a) (u+b) 1`
(`matReindexEquiv`, measure-preserving; Frobenius is reindex-invariant). The RHS constant is `Q`-free. -/
theorem shell_fullBlock_le {u a b n : ℕ} {ε c' : ℝ} (hε : 0 < ε) (hc0 : 0 < c')
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ)
    (hshell : (Q * Qᵀ - (ε ^ 2) • (1 : Matrix (Fin u ⊕ Fin b) (Fin u ⊕ Fin b) ℝ)).PosSemidef) :
    (∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1,
        ENNReal.ofReal (frobSq (Matrix.of B * Q) ^ (-c')))
      ≤ ENNReal.ofReal ((ε ^ 2) ^ (-c'))
          * ∫⁻ A₀ in matBox (u + a) (u + b) 1, ENNReal.ofReal (frobSq (Matrix.of A₀) ^ (-c')) := by
  classical
  set er : Fin (u + a) ≃ Fin u ⊕ Fin a := finSumFinEquiv.symm with her
  set ec : Fin (u + b) ≃ Fin u ⊕ Fin b := finSumFinEquiv.symm with hec
  -- (i) reindex the pure-`frobSq` integral: block box → matrix box
  have hpre : matReindexEquiv er ec ⁻¹' genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1
      = matBox (u + a) (u + b) 1 := by
    ext A₀
    simp only [Set.mem_preimage, genBox, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k
      have := h (er i) (ec k)
      rwa [matReindexEquiv_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
    · intro h I J; rw [matReindexEquiv_apply]; exact h _ _
  have hfrob : ∀ A₀ : Fin (u + a) → Fin (u + b) → ℝ,
      frobSq (Matrix.of (matReindexEquiv er ec A₀)) = frobSq (Matrix.of A₀) := by
    intro A₀
    simp only [frobSq, Matrix.of_apply, matReindexEquiv_apply]
    rw [← Equiv.sum_comp er (fun I => ∑ J, (A₀ (er.symm I) (ec.symm J)) ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Equiv.symm_apply_apply, ← Equiv.sum_comp ec (fun J => (A₀ i (ec.symm J)) ^ 2)]
    exact Finset.sum_congr rfl (fun j _ => by rw [Equiv.symm_apply_apply])
  have hpure : (∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1,
        ENNReal.ofReal (frobSq (Matrix.of B) ^ (-c')))
      = ∫⁻ A₀ in matBox (u + a) (u + b) 1, ENNReal.ofReal (frobSq (Matrix.of A₀) ^ (-c')) := by
    have hmp := measurePreserving_matReindexEquiv er ec
    have hstep := hmp.setLIntegral_comp_preimage_emb (matReindexEquiv er ec).measurableEmbedding
      (fun B => ENNReal.ofReal (frobSq (Matrix.of B) ^ (-c')))
      (genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1)
    rw [hpre] at hstep
    rw [show (∫⁻ A₀ in matBox (u + a) (u + b) 1,
          ENNReal.ofReal (frobSq (Matrix.of (matReindexEquiv er ec A₀)) ^ (-c')))
        = ∫⁻ A₀ in matBox (u + a) (u + b) 1, ENNReal.ofReal (frobSq (Matrix.of A₀) ^ (-c')) from
      setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A₀ _ => by rw [hfrob A₀])] at hstep
    exact hstep.symm
  -- (ii) pointwise Loewner-floor bound
  have hpt : ∀ B ∈ genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1,
      ENNReal.ofReal (frobSq (Matrix.of B * Q) ^ (-c'))
        ≤ ENNReal.ofReal ((ε ^ 2) ^ (-c')) * ENNReal.ofReal (frobSq (Matrix.of B) ^ (-c')) := by
    intro B _
    have hfloorB := frobSq_mul_ge_of_gramFloor (Matrix.of B) Q hshell
    rcases eq_or_lt_of_le (frobSq_nonneg (Matrix.of B)) with hz | hpos
    · -- `frobSq (of B) = 0 ⟹ of B = 0 ⟹ of B · Q = 0`
      have hBzero : Matrix.of B = 0 := by
        have hzz : (∑ I, ∑ J, ((Matrix.of B) I J) ^ 2) = 0 := hz.symm
        ext I J
        have h1 : ∑ J, ((Matrix.of B) I J) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun I _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mp hzz I (Finset.mem_univ I)
        have h2 : ((Matrix.of B) I J) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h1 J (Finset.mem_univ J)
        simpa using (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
      have hfz : frobSq (0 : Matrix (Fin u ⊕ Fin a) (Fin n) ℝ) = 0 := by simp [frobSq]
      rw [hBzero, Matrix.zero_mul, hfz, Real.zero_rpow (by linarith : (-c') ≠ 0),
        ENNReal.ofReal_zero]
      exact zero_le _
    · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2) _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ ε ^ 2) (frobSq_nonneg _)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hfloorB (by linarith)
  -- (iii) assemble
  calc (∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1,
          ENNReal.ofReal (frobSq (Matrix.of B * Q) ^ (-c')))
      ≤ ∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1,
          ENNReal.ofReal ((ε ^ 2) ^ (-c')) * ENNReal.ofReal (frobSq (Matrix.of B) ^ (-c')) :=
        setLIntegral_mono_ae' (measurableSet_genBox 1) (ae_of_all _ (fun B hB => hpt B hB))
    _ = ENNReal.ofReal ((ε ^ 2) ^ (-c'))
          * ∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1,
              ENNReal.ofReal (frobSq (Matrix.of B) ^ (-c')) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((ε ^ 2) ^ (-c'))
          * ∫⁻ A₀ in matBox (u + a) (u + b) 1, ENNReal.ofReal (frobSq (Matrix.of A₀) ^ (-c')) := by
        rw [hpure]

/-- **The block-front inner reassembly.** The `(P,B₁₂,C)×D` integral over `outerDom × genBox` is the
block-coordinate integral over the block box ∩ invertible-pivot locus: `blockSplitD` is measure-preserving
and `blockSplitD ⁻¹' (outerDom ×ˢ genBox) = genBox ∩ {IsUnit toBlocks₁₁}` (`blockSplitD_preimage_outerDom`);
the integrand is continuous (`frobSq (of B · Q)`), so `setLIntegral_prod`/`setLIntegral_comp_preimage_emb`
transport. -/
theorem blockFront_inner_eq {u a b n : ℕ} (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) (c' : ℝ) :
    (∫⁻ x in outerDom u a b 1,
        ∫⁻ D in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD u a b).symm (x, D)) * Q) ^ (-c')))
      = ∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1 ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal (frobSq (Matrix.of B * Q) ^ (-c')) := by
  set F : SJOuter u a b × (Fin a → Fin b → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD u a b).symm y) * Q) ^ (-c')) with hF
  have hFmeas : Measurable F := by
    rw [hF]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun r : ℝ => r ^ (-c')) (by fun_prop)
    have hof : Continuous (fun B : (Fin u ⊕ Fin a) → (Fin u ⊕ Fin b) → ℝ => (Matrix.of B)) :=
      continuous_matrix (fun I J => (continuous_apply J).comp (continuous_apply I))
    have hcont : Continuous (fun B : (Fin u ⊕ Fin a) → (Fin u ⊕ Fin b) → ℝ =>
        frobSq (Matrix.of B * Q)) := by
      have hmul := hof.matrix_mul (continuous_const (y := Q))
      unfold frobSq
      exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
        (fun j _ => ((hmul.matrix_elem i j).pow 2)))
    exact hcont.measurable.comp (blockSplitD u a b).symm.measurable
  have hmp := measurePreserving_blockSplitD u a b
  have hpre := hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (blockSplitD u a b)) F
    (outerDom u a b 1 ×ˢ genBox (Fin a) (Fin b) 1)
  rw [blockSplitD_preimage_outerDom] at hpre
  rw [show (∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1 ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
        F (blockSplitD u a b B))
      = ∫⁻ B in genBox (Fin u ⊕ Fin a) (Fin u ⊕ Fin b) 1 ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
        ENNReal.ofReal (frobSq (Matrix.of B * Q) ^ (-c')) from
      setLIntegral_congr_fun ((measurableSet_genBox 1).inter measurableSet_isUnit_toBlocks₁₁)
        (fun B _ => by rw [hF]; simp only [MeasurableEquiv.symm_apply_apply])] at hpre
  rw [hpre, Measure.volume_eq_prod (SJOuter u a b) (Fin a → Fin b → ℝ),
    setLIntegral_prod F hFmeas.aemeasurable]

/-- **The nat chain** `minAdm(redChain u M) + (M₀−u)(M₁−u) ≤ (u+(M₀−u))·(u+(M₁−u))` — the block-dimension
threshold `N = (u+a)(u+b)` dominates the comparator threshold, via `hpiv` (`minAdm ≤ u·tailMinWidth`),
`tailMinWidth ≤ M 1`, and `M₁−u ≤ u+(M₁−u)`. -/
theorem minAdm_add_peel_le (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) :
    minAdm (redChain u M) + (M 0 - u) * (M 1 - u) ≤ (u + (M 0 - u)) * (u + (M 1 - u)) := by
  have htw : tailMinWidth M ≤ M 1 := by
    have h := Finset.inf'_le (f := fun i : Fin (L + 1 + 1) => M i.succ)
      (Finset.mem_univ (0 : Fin (L + 1 + 1)))
    simpa [tailMinWidth] using h
  have h1 : u * tailMinWidth M ≤ u * (u + (M 1 - u)) :=
    Nat.mul_le_mul (le_refl u) (le_trans htw (by omega))
  have h2 : (M 0 - u) * (M 1 - u) ≤ (M 0 - u) * (u + (M 1 - u)) :=
    Nat.mul_le_mul (le_refl (M 0 - u)) (Nat.le_add_left _ _)
  calc minAdm (redChain u M) + (M 0 - u) * (M 1 - u)
      ≤ u * (u + (M 1 - u)) + (M 0 - u) * (u + (M 1 - u)) :=
        Nat.add_le_add (le_trans hpiv h1) h2
    _ = (u + (M 0 - u)) * (u + (M 1 - u)) := by ring

/-- **RHS positivity.** `pivotDomRHS ≠ 0` (in the `u ≥ 1` cut) — the comparator's decorated loss is `> 0`
a.e. (`deeperFlagCore_decLoss_pos_ae`), so the integrand is positive on a positive-measure set. -/
theorem pivotDomRHS_ne_zero_aux (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : 1 ≤ u) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) :
    pivotDomRHS M u c' Zf ≠ 0 := by
  sorry

/-- **The comparator diverges above the critical exponent.** For `(minAdm(redChain u M) + (M₀−u)(M₁−u))/2 ≤
c'`, the comparator RHS is `⊤`: restrict `v₀ ∈ (0,1)`, `|Γ| ≤ v₀`; on the a.e. set `decLoss > 0` the base is
`≤ K(z)·v₀²`, so the inner integral `≥ K(z)^{−c'}·v₀^{−2c'}·(2v₀)^{ab}`, and `∫₀¹ v₀^{(minAdm−1)+ab−2c'} = ⊤`.
Contrapositive: `RHS < ⊤ ⟹ 2c' < minAdm + (M₀−u)(M₁−u)`. -/
theorem pivotDomRHS_eq_top_of_critical (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : 1 ≤ u) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (hc : ((minAdm (redChain u M) + (M 0 - u) * (M 1 - u) : ℕ) : ℝ) / 2 ≤ c') :
    pivotDomRHS M u c' Zf = ⊤ := by
  sorry

/-- **The `0 < c'` finiteness** — the main content. Below the block-dimension threshold `c' < (u+a)(u+b)/2`,
the freed Schur-loss spine LHS is finite: fold to the block-front (`pivotDomLHS_eq_blockFront`), reassemble
the inner integral (`blockFront_inner_eq`), drop the invertible-pivot restriction, and bound each shell fibre
by the `Q`-uniform full-block constant (`shell_fullBlock_le` + `matBox_frobSq_neg_lintegral_lt_top`),
integrated against the finite `(z, A_cor)`-box volume. -/
theorem pivotDomLHS_lt_top_of_pos (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) {ε : ℝ} (hε : 0 < ε) {c' : ℝ}
    (hcpos : 0 < c') (hcN : c' < (((u + (M 0 - u)) * (u + (M 1 - u)) : ℕ) : ℝ) / 2)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) :
    pivotDomLHS M u ε c' Zf < ⊤ := by
  set K : ℝ≥0∞ := ENNReal.ofReal ((ε ^ 2) ^ (-c'))
      * ∫⁻ A₀ in matBox (u + (M 0 - u)) (u + (M 1 - u)) 1,
          ENNReal.ofReal (frobSq (Matrix.of A₀) ^ (-c')) with hKdef
  have hKfin : K < ⊤ := by
    rw [hKdef]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (matBox_frobSq_neg_lintegral_lt_top hcpos hcN)
  have hmatvol : volume (matBox (M 1 - u) (dropHead (redChain u M) 0) 1) < ⊤ := by
    rw [matBox_volume _ _ (by norm_num : (0 : ℝ) ≤ 1)]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hparamsvol : volume (paramsBoxM (redChain u M) 1) < ⊤ :=
    paramsBoxM_volume_lt_top (redChain u M) 1
  -- each shell fibre's block-front energy is bounded by the uniform constant `K`
  have hinner : ∀ (z : Params (redChain u M))
      (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ),
      A_cor ∈ matBox (M 1 - u) (dropHead (redChain u M) 0) 1 ∩ pivotShell M u ε Zf z →
      (∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
          ∫⁻ D in genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1,
            ENNReal.ofReal (frobSq (Matrix.of ((blockSplitD u (M 0 - u) (M 1 - u)).symm (x, D))
              * hsQ M u Zf z A_cor) ^ (-c'))) ≤ K := by
    intro z A_cor hA
    rw [blockFront_inner_eq (hsQ M u Zf z A_cor) c', hKdef]
    exact le_trans (lintegral_mono_set Set.inter_subset_left)
      (shell_fullBlock_le hε hcpos (hsQ M u Zf z A_cor) hA.2)
  rw [pivotDomLHS_eq_blockFront]
  refine lt_of_le_of_lt ?_
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hKfin hmatvol) hparamsvol)
  refine le_trans (lintegral_mono
    (fun z => setLIntegral_mono measurable_const (fun A_cor hA => hinner z A_cor hA))) ?_
  refine le_trans (lintegral_mono (fun z => lintegral_mono_set Set.inter_subset_left)) ?_
  refine le_of_eq ?_
  rw [lintegral_congr (fun z => by rw [setLIntegral_const]), setLIntegral_const]

/-- **The `c' ≤ 0` edge.** With a non-positive exponent the loss power is `frobSq^{|c'|}` (no singularity);
`RHS < ⊤` controls the deep-frame tail. NOT the application regime (the RLCT exponent is `≥ 0`). -/
theorem pivotDomLHS_lt_top_of_nonpos (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) {ε : ℝ} {c' : ℝ}
    (hcneg : c' ≤ 0)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    pivotDomLHS M u ε c' Zf < ⊤ := by
  sorry

/-- **The σ-coupled pivot-peel DOMINATION (the ISOLATED CRUX — scaffold + 1-sorry, standing decision 7).**
The freed Schur-loss spine LHS is dominated by a FINITE reorganisation constant times the comparator-core
RHS. This is exactly the conclusion of `RouteMSJHeadSplitDom.headSplit_pivotDom`; it carries the entire
head-split analytic crux and is left as the single `sorry` of this module. The block-front reduction
`pivotDomLHS_eq_blockFront` gives the concrete starting point.

**Internal decomposition** (the scaffold, to be built sorry-free around the one residual C-absorption):
* **Reformulation** (`freedSchurLoss_eq_frobSq_block`, LANDED): on `outerDom` (`IsUnit P`), `freedSchurLoss
  x Γ Q = frobSq(fromBlocks P B₁₂ C (Γ+schurShift x) · Q)` — the `P⁻¹` coupling cancels.
* **D-subst**: substitute `D := Γ + schurShift x` (translation, measure-preserving); the `(2,2)` block `D`
  ranges over `genBox`, giving the clean block-front integral `∫_{P,B₁₂,C box, D genBox} frobSq(B·Q_stack)^{−c'}`.
* **Row-split**: `frobSq(B·Q_stack) = frobSq((P|B₁₂)·Q_stack) + frobSq((C|D)·Q_stack)` — top rows = pivot
  `w`, bottom rows = corank.
* **D-A radial (top)**: `pivotBlock_radial_blowup` on `W = (P|B₁₂)` (Jacobian `r^{u·M₁−1}`); the direction
  `P̂` hits `Q_stack`, RETAINING the `σ_i(z,A_cor)`-dependence (a uniform pivot pull-out DIVERGES — archfin
  + Codex). `σ_i`-bounded-below directions give the uniform pivot capacity `uρ`, non-binding by `hpiv`.
* **S3 corank (bottom)** + **the σ-coupled C-ABSORPTION (the residual, ~65-75%-new, the RISKY piece)**:
  the LHS corank integrates over `C` (a×u, box) AND `D` (a×b, genBox) with the `C·Q_p` CROSS-TERM
  `frobSq(C·Q_p + D·Q_b)`, whereas S3 (`shell_corankOffSector_le_unif`) handles `∫_{A_cor,Γ}(w +
  frobSq(Ccross + Γ·(A_cor·Z)))^{−c'} ≤ Cunif·w^{−(c'−ab/2)}` with `Ccross` FIXED. The residual identifies
  `Ccross := C·Q_p` and absorbs `C` by S3's `Ccross`-UNIFORMITY (box-vol, NOT codim ⟹ corank charge `ab`,
  closing the `b>u` window) — the piece the certs flag needs the adapted chart-constant lemma. -/
theorem pivotPeel_domination (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ pivotDomLHS M u ε c' Zf ≤ C * pivotDomRHS M u c' Zf := by
  refine exists_finite_mul_of_finite_imp (pivotDomRHS_ne_zero_aux M u hu c' hnd Zf) (fun hRHS => ?_)
  -- extract `2c' < minAdm(redChain u M) + (M₀−u)(M₁−u)` from RHS finiteness (else RHS = ⊤)
  have hcrit : 2 * c' < ((minAdm (redChain u M) + (M 0 - u) * (M 1 - u) : ℕ) : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hle : ((minAdm (redChain u M) + (M 0 - u) * (M 1 - u) : ℕ) : ℝ) / 2 ≤ c' := by linarith
    rw [pivotDomRHS_eq_top_of_critical M u hu c' hnd Zf hZfMeas hle] at hRHS
    exact (lt_irrefl _ hRHS)
  -- the nat chain: comparator threshold ≤ the block dimension `N = (u+a)(u+b)`
  have hN : (minAdm (redChain u M) + (M 0 - u) * (M 1 - u) : ℕ)
      ≤ (u + (M 0 - u)) * (u + (M 1 - u)) := minAdm_add_peel_le M u hpiv
  have hcN : c' < (((u + (M 0 - u)) * (u + (M 1 - u)) : ℕ) : ℝ) / 2 := by
    have h2 : 2 * c' < (((u + (M 0 - u)) * (u + (M 1 - u)) : ℕ) : ℝ) :=
      lt_of_lt_of_le hcrit (by exact_mod_cast hN)
    linarith
  -- `LHS < ⊤`: the `0 < c'` clean full-block bound, else the non-positive edge
  by_cases hcpos : 0 < c'
  · exact pivotDomLHS_lt_top_of_pos M u hε hcpos hcN Zf
  · exact pivotDomLHS_lt_top_of_nonpos M u (not_lt.mp hcpos) Zf hRHS

/-- **The forward finiteness (Option B).** From the RHS finiteness `hRHS` and the σ-coupled domination
`pivotPeel_domination` (`LHS ≤ C·RHS`, `C < ⊤`), the freed Schur-loss spine LHS is finite:
`lt_of_le_of_lt` the domination against `C·RHS < ⊤` (`ENNReal.mul_lt_top`). -/
theorem forward_LHS_finiteness (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    pivotDomLHS M u ε c' Zf < ⊤ := by
  obtain ⟨C, hC, hle⟩ := pivotPeel_domination M u hu hε c' hnd hpiv hcvg hmM hε' Zf hZfMeas
    U_sf hUs hrank hfloor
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top hC hRHS)

/-- **The `u = 0` edge.** With a `0`-width pivot the front block vanishes and `decLoss = 0`, so
`pivotDomLHS ≤ pivotDomRHS` (`pivotDom_uzero`), hence finite from `hRHS`. -/
theorem pivotDom_finiteness_uzero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu0 : u = 0) {ε : ℝ} (c' : ℝ)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    pivotDomLHS M u ε c' Zf < ⊤ :=
  lt_of_le_of_lt (pivotDom_uzero M u hu0 c' hpiv Zf) hRHS

/-- **GLUE-2 finiteness (the isolated crux).** Verbatim statement of
`RouteMSJPivotDom.pivotDom_finiteness`; the controller wires the stub to it. `hRHS` is passed straight to
the forward finiteness (Option B — the σ-coupled domination), with the `u = 0` edge separate. -/
theorem pivotDom_finiteness_impl (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    pivotDomLHS M u ε c' Zf < ⊤ := by
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · exact pivotDom_finiteness_uzero M u hu0 c' hpiv Zf hRHS
  · exact forward_LHS_finiteness M u hupos hε c' hnd hpiv hcvg hmM hε' Zf hZfMeas U_sf hUs hrank hfloor
      hRHS

end DLNFibre.DLN.RLCT
