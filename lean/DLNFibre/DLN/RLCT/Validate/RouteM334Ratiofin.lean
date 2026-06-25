import DLNFibre.DLN.RLCT.Validate.RouteM334Hfin

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteM334Ratiofin` — the ratio-residual finiteness (`hratiofin`)

The last gap of the `(3,3,4)` per-chart finiteness `matBox334_chart_lt_top`: the ratio residual
`∫_{z∈[−1,1]^8} angA1Int c' p (e.symm (0,z)) < ⊤`, where (banked in `RouteM334Hfin`)

    angA1Int c' p y = ∫_{A1∈matBox 3 4 1} ofReal (frobSq (rmatMul (Rmat334 p y) A1) ^ (−c')),
    Rmat334 p y r c = (if e3 (r,c) = p then 1 else y (e3 (r,c)))  (e3 = finProdFinEquiv : Fin 3×Fin 3 ≃ Fin 9).

The route (pp-r1-genM-2 design; Codex `xhigh` VET, thread 29 `hratiofin-plan-answer.md`):

* **STEP 1 — per-pivot row/col permutation to the `(0,0)` normal form.** For pivot `p ↔ (r₀,c₀)`
  (`e3.symm p`), the row-swap `σr = swap r₀ 0` and col-swap `σc = swap c₀ 0` reorder `Rmat334 p y` to
  `R' r c = Rmat334 p y (σr r) (σc c)` with the pivot `1` at `(0,0)`. The induced A1-row permute is
  measure-preserving on the symmetric box (`matBox34_rowperm_lintegral`), and `frobSq` is invariant under
  the residual output row-perm (`frobSq_rmatMul_perm`, the `A1 ↦ Q⁻¹A1` orientation): so
  `angA1Int c' p y = ∫_{A1} frobSq(R'·A1)^{−c'}`. `R'` IS `angularR` with read-off entries
  (`angularR_reconstruct`, `R'(0,0)=1`), whose off-pivot ratios are `z`-components (`Rmat334norm_offpivot_le`),
  so `g² ≤ 1` and the BANKED `angularA1_integral_le` applies — the per-`z` pointwise bound.

* **STEP 2 — the outer integration (BANKED).** `ratioResidual_le_Jint`: integrate the per-`z` bound over
  `z∈[−1,1]^8` (`setLIntegral_mono_ae'`) and pull out the `(1/5)^{−c'}` constant, reducing `hratiofin`
  (`ratioResidual_lt_top`) to the resolved-form finiteness `resolvedZ_lt_top` (`∫_z Jint < ⊤`).

* **STEP 3 — the resolved-form change-of-variables.** STEP-3a (the `z`-pointwise inner `T`-peel:
  `row0↦T` MP translation, row-split + `prod_reorder`) is BANKED sorry-free (`step3a` / `Jint_le_Ginner`),
  reducing `resolvedZ_lt_top` to STEP-3b. STEP-3b (`ginnerZ_lt_top`, the ONE remaining `sorry`) is the
  outer `z`-CoV: the `raw↦Δ` translation per fixed `(g,b)` (`lintegral_translate_le`, banked) + the `(g,b)`
  finite vol-factor + `S` box-enlargement to `K = 3`, feeding the BANKED `resolved334_box_lt_top 3`. The
  residual gap is the per-`p` `z`-slot identification (which `z`-coords are `raw/g/b`) — see
  `ginnerZ_lt_top`'s docstring.

This file relocates the `(3,3,4)` hfin headline chain (`matBox334_blowup_lt_top` …
`routeMCore_M334_threshold_lt_top`) out of `RouteM334Hfin` (where `matBox334_chart_lt_top` now takes the
ratio-residual as a hypothesis), so the chain can consume the discharged `ratioResidual_lt_top` without an
import cycle. S2-hygiene: closing `resolvedZ_lt_top` makes `routeMCore_M334_threshold_lt_top` fully
`[propext, Classical.choice, Quot.sound]` (currently `+ sorryAx` from this lone gap, NO `monomial_rlct`).
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace DLNFibre.DLN.RLCT

/-- The `Fin 3 × Fin 3 ≃ Fin 9` flat reindex that `Rmat334`/`matToFlatEquiv 3 3` use entrywise
(`matToFlatEquiv 3 3 A i = A (e3.symm i).1 (e3.symm i).2`; `Rmat334 p y r c` reads `e3 (r,c)`). -/
noncomputable def e3 : Fin 3 × Fin 3 ≃ Fin 9 := finProdFinEquiv

/-- `Rmat334 p y r c` is the `e3`-indexed select: `1` at the pivot flat-index `p`, else `y (e3 (r,c))`. -/
theorem Rmat334_entry (p : Fin 9) (y : Fin 9 → ℝ) (r c : Fin 3) :
    Rmat334 p y r c = (if e3 (r, c) = p then (1 : ℝ) else y (e3 (r, c))) := rfl

/-! ## STEP 1 — the permutation atoms -/

/-- **The Frobenius row/col-permutation invariance** (Codex VET-3, the `A1 ↦ Q⁻¹A1` orientation). For
row/col permutations `σr, σc : Fin 3 ≃ Fin 3`, `frobSq(R·A1) = frobSq(R'·A1σc)` where
`R' r c = R (σr r) (σc c)` and `A1σc k j = A1 (σc k) j`: reindex the contraction sum by `σc` and the
output rows by `σr` (`frobSq`, a full `∑ᵢⱼ`, is row-permutation invariant). -/
theorem frobSq_rmatMul_perm (R : Fin 3 → Fin 3 → ℝ) (A1 : Fin 3 → Fin 4 → ℝ)
    (σr σc : Fin 3 ≃ Fin 3) :
    frobSq (rmatMul R A1)
      = frobSq (rmatMul (fun r c => R (σr r) (σc c)) (fun k j => A1 (σc k) j)) := by
  unfold frobSq rmatMul
  rw [← Equiv.sum_comp σr (fun r => ∑ j, (∑ k, R r k * A1 k j) ^ 2)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [← Equiv.sum_comp σc (fun k => R (σr r) k * A1 k j)]

/-- **The A1 row-permutation change of variables** on the symmetric box `matBox 3 4 1`. Permuting the
`Fin 3` row-index of `A1` by `σc` is measure-preserving (`volume_measurePreserving_piCongrLeft`) and the
box is `σc`-invariant, so `∫_{A1∈box} f A1 = ∫_{A1∈box} f (k ↦ A1 (σc k) ·)`. -/
theorem matBox34_rowperm_lintegral (σc : Fin 3 ≃ Fin 3)
    (f : (Fin 3 → Fin 4 → ℝ) → ℝ≥0∞) :
    (∫⁻ A1 in matBox 3 4 1, f A1)
      = ∫⁻ A1 in matBox 3 4 1, f (fun k j => A1 (σc k) j) := by
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => Fin 4 → ℝ) σc with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => Fin 4 → ℝ) σc).symm E
  have hpre : matBox 3 4 1 = E.symm ⁻¹' (matBox 3 4 1) := by
    ext A1
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (σc i) k
    · intro h i k
      have := h (σc.symm i) k
      rw [show E.symm A1 (σc.symm i) k = A1 i k from by
        show A1 (σc (σc.symm i)) k = A1 i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  have hms : MeasurableSet (matBox 3 4 1) := matBox_measurableSet 3 4 1
  have key := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f (matBox 3 4 1)
  have hrhs : (∫⁻ A1 in matBox 3 4 1, f (fun k j => A1 (σc k) j))
      = ∫⁻ A1 in matBox 3 4 1, f (E.symm A1) := rfl
  rw [hrhs]
  rw [← hpre] at key
  exact key.symm

/-- **`angularR` reconstruction from its entries.** Any `3×3` `R'` with `R' 0 0 = 1` equals `angularR`
with `b = (R' 0 1, R' 0 2)`, `g = (R' 1 0, R' 2 0)`, and the de-shifted lower-right
`d_ij = R'(i+1,j+1) − g_i·b_j` (the de-shift `d = raw − γβ` is built into `angularR`). -/
theorem angularR_reconstruct (R' : Fin 3 → Fin 3 → ℝ) (h00 : R' 0 0 = 1) :
    angularR (R' 0 1) (R' 0 2) (R' 1 0) (R' 2 0)
      (R' 1 1 - R' 1 0 * R' 0 1) (R' 1 2 - R' 1 0 * R' 0 2)
      (R' 2 1 - R' 2 0 * R' 0 1) (R' 2 2 - R' 2 0 * R' 0 2)
      = R' := by
  funext i j
  unfold angularR
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val', Fin.isValue, Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk] <;>
    first
      | exact h00.symm
      | rfl
      | ring

/-- The pivot-normalized angular matrix on chart `p`, ratios `z`: `R' r c = Rmat334 p (e.symm (0,z))
(σr r) (σc c)` with `σr = swap r₀ 0`, `σc = swap c₀ 0` and `(r₀,c₀) = e3.symm p`. Pivot `1` at `(0,0)`. -/
noncomputable def Rmat334norm (p : Fin 9) (z : Fin 8 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun r c => Rmat334 p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z))
    ((Equiv.swap (e3.symm p).1 0) r) ((Equiv.swap (e3.symm p).2 0) c)

/-- `Rmat334norm p z 0 0 = 1`: the `(0,0)` entry is the pivot (`σr 0 = r₀`, `σc 0 = c₀`, and
`e3 (r₀,c₀) = p`). -/
theorem Rmat334norm_pivot (p : Fin 9) (z : Fin 8 → ℝ) : Rmat334norm p z 0 0 = 1 := by
  unfold Rmat334norm
  rw [Equiv.swap_apply_right, Equiv.swap_apply_right, Rmat334_entry]
  rw [if_pos]
  change e3 ((e3.symm p).1, (e3.symm p).2) = p
  rw [show ((e3.symm p).1, (e3.symm p).2) = e3.symm p from rfl, Equiv.apply_symm_apply]

/-- Off-`(0,0)` entries of `Rmat334norm p z` are `z`-components, hence `|·| ≤ 1` on the box `[−1,1]^8`.
(For `(i,j) ≠ (0,0)`, the index `e3 (σr i, σc j) ≠ p` by swap-injectivity, so the entry is `y`-read at a
non-pivot flat-index, which is exactly some `z j` since `y = e.symm (0,z)`.) -/
theorem Rmat334norm_offpivot_le (p : Fin 9) (z : Fin 8 → ℝ)
    (hz : z ∈ Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1))
    (i j : Fin 3) (hij : ¬ (i = 0 ∧ j = 0)) :
    |Rmat334norm p z i j| ≤ 1 := by
  unfold Rmat334norm
  set r0 := (e3.symm p).1 with hr0
  set c0 := (e3.symm p).2 with hc0
  set σr := Equiv.swap r0 0 with hσr
  set σc := Equiv.swap c0 0 with hσc
  set y := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z) with hy
  have hσr0 : σr 0 = r0 := by rw [hσr, Equiv.swap_apply_right]
  have hσc0 : σc 0 = c0 := by rw [hσc, Equiv.swap_apply_right]
  have hpe : e3 (r0, c0) = p := by
    change e3 ((e3.symm p).1, (e3.symm p).2) = p
    rw [show ((e3.symm p).1, (e3.symm p).2) = e3.symm p from rfl, Equiv.apply_symm_apply]
  have hidx : e3 (σr i, σc j) ≠ p := by
    intro heq
    rw [← hpe] at heq
    have hpair := e3.injective heq
    rw [Prod.mk.injEq] at hpair
    obtain ⟨hi, hj⟩ := hpair
    rw [← hσr0] at hi; rw [← hσc0] at hj
    exact hij ⟨σr.injective hi, σc.injective hj⟩
  rw [Rmat334_entry, if_neg hidx]
  obtain ⟨jj, hjj⟩ := Fin.exists_succAbove_eq hidx
  rw [← hjj, show y (p.succAbove jj) = z jj from by rw [hy]; simp [MeasurableEquiv.piFinSuccAbove]]
  have := hz jj (Set.mem_univ jj)
  rw [Set.mem_Icc, ← abs_le] at this
  exact this

/-- **`angA1Int` in the pivot-normalized form.** `angA1Int c' p (e.symm (0,z)) = ∫_{A1} frobSq(R'·A1)^{−c'}`
with `R' = Rmat334norm p z` (the `(0,0)`-pivot reorder): apply `frobSq_rmatMul_perm` (reorder
`Rmat334 p y` by `σr,σc`, row-permute `A1` by `σc`) under the A1-row-permute change of variables
(`matBox34_rowperm_lintegral`). -/
theorem angA1Int_eq_norm (c' : ℝ) (p : Fin 9) (z : Fin 8 → ℝ) :
    angA1Int c' p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z))
      = ∫⁻ A1 in matBox 3 4 1,
          ENNReal.ofReal ((frobSq (rmatMul (Rmat334norm p z) A1)) ^ (-c')) := by
  set y := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z) with hy
  set σr := Equiv.swap (e3.symm p).1 0 with hσr
  set σc := Equiv.swap (e3.symm p).2 0 with hσc
  unfold angA1Int
  -- rewrite the RHS (the normalized integral) by the A1-row-permute CoV, matching the LHS pointwise.
  rw [matBox34_rowperm_lintegral σc
    (fun A1 => ENNReal.ofReal ((frobSq (rmatMul (Rmat334norm p z) A1)) ^ (-c')))]
  refine lintegral_congr (fun A1 => ?_)
  congr 2
  -- frobSq(R·A1) = frobSq(R'·A1σc) with R' = Rmat334norm p z (= R reordered by σr,σc).
  exact frobSq_rmatMul_perm (Rmat334 p y) A1 σr σc

/-- **The per-`z` pointwise resolved bound (STEP 1, the angular comparability feed).** For `z∈[−1,1]^8`
and `0 < c'`, the ratio residual at `z` is dominated by the resolved-form A1-integral:

    angA1Int c' p (e.symm (0,z))
      ≤ ofReal((1/5)^{−c'}) · ∫_{A1∈box34} ofReal((∑ⱼ Tⱼ² + frobSq(Δ·S))^{−c'}),

`Tⱼ = A1 0 j + (b0·A1 1 j + b1·A1 2 j)`, `Δ = !![d00,d01;d10,d11]` the de-shifted lower-right read off
`R' = Rmat334norm p z`, `S = A1` rows 1,2, `(b,g) = (R'(0,1),R'(0,2),R'(1,0),R'(2,0))`. Compose the
pivot-normalization (`angA1Int_eq_norm`), the `angularR` reconstruction (`angularR_reconstruct`,
`R'(0,0)=1`), and the BANKED `angularA1_integral_le` (the `g²≤1` from `Rmat334norm_offpivot_le`). -/
theorem angA1Int_le_resolved (c' : ℝ) (hc0 : 0 < c') (p : Fin 9) (z : Fin 8 → ℝ)
    (hz : z ∈ Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)) :
    angA1Int c' p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z))
      ≤ ENNReal.ofReal (((1 : ℝ) / 5) ^ (-c'))
        * ∫⁻ A1 in matBox 3 4 1,
            ENNReal.ofReal (((∑ jj, (A1 0 jj
                + (Rmat334norm p z 0 1 * A1 1 jj + Rmat334norm p z 0 2 * A1 2 jj)) ^ 2)
              + frobSq (rmatMul
                  (!![Rmat334norm p z 1 1 - Rmat334norm p z 1 0 * Rmat334norm p z 0 1,
                       Rmat334norm p z 1 2 - Rmat334norm p z 1 0 * Rmat334norm p z 0 2;
                      Rmat334norm p z 2 1 - Rmat334norm p z 2 0 * Rmat334norm p z 0 1,
                       Rmat334norm p z 2 2 - Rmat334norm p z 2 0 * Rmat334norm p z 0 2]
                    : Matrix (Fin 2) (Fin 2) ℝ)
                  (fun k jj => A1 (k.succ) jj))) ^ (-c')) := by
  rw [angA1Int_eq_norm]
  have hrecon := angularR_reconstruct (Rmat334norm p z) (Rmat334norm_pivot p z)
  have hg0 : (Rmat334norm p z 1 0) ^ 2 ≤ 1 := by
    have h := abs_le.1 (Rmat334norm_offpivot_le p z hz 1 0 (by simp))
    nlinarith [h.1, h.2]
  have hg1 : (Rmat334norm p z 2 0) ^ 2 ≤ 1 := by
    have h := abs_le.1 (Rmat334norm_offpivot_le p z hz 2 0 (by simp))
    nlinarith [h.1, h.2]
  calc (∫⁻ A1 in matBox 3 4 1, ENNReal.ofReal ((frobSq (rmatMul (Rmat334norm p z) A1)) ^ (-c')))
      = ∫⁻ A1 in matBox 3 4 1,
          ENNReal.ofReal ((frobSq (rmatMul (angularR (Rmat334norm p z 0 1) (Rmat334norm p z 0 2)
            (Rmat334norm p z 1 0) (Rmat334norm p z 2 0)
            (Rmat334norm p z 1 1 - Rmat334norm p z 1 0 * Rmat334norm p z 0 1)
            (Rmat334norm p z 1 2 - Rmat334norm p z 1 0 * Rmat334norm p z 0 2)
            (Rmat334norm p z 2 1 - Rmat334norm p z 2 0 * Rmat334norm p z 0 1)
            (Rmat334norm p z 2 2 - Rmat334norm p z 2 0 * Rmat334norm p z 0 2)) A1)) ^ (-c')) := by
        refine lintegral_congr (fun A1 => ?_); rw [hrecon]
    _ ≤ _ := angularA1_integral_le c' hc0 _ _ _ _ _ _ _ _ hg0 hg1

/-! ## STEP 2 — measurability + the outer reduction -/

/-- Each entry `Rmat334norm p · r c` is measurable in `z` (the `matToFlatEquiv 3 3`-`symm` ∘ the
`piFinSuccAbove p`-symm-select; an MP-equiv composite). -/
theorem measurable_Rmat334norm_entry (p : Fin 9) (r c : Fin 3) :
    Measurable (fun z : Fin 8 → ℝ => Rmat334norm p z r c) := by
  unfold Rmat334norm Rmat334
  have h2 : Measurable (fun z : Fin 9 → ℝ => (matToFlatEquiv 3 3).symm z) :=
    (matToFlatEquiv 3 3).symm.measurable
  have hsel : Measurable (fun z : Fin 8 → ℝ =>
      (fun i : Fin 9 => if i = p then (1 : ℝ)
        else (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z) i)) := by
    apply measurable_pi_lambda; intro i
    by_cases hi : i = p
    · simp only [hi, if_pos]; exact measurable_const
    · simp only [hi, if_neg, not_false_eq_true]
      have hpf : Measurable (fun z : Fin 8 → ℝ =>
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z)) := by fun_prop
      exact (measurable_pi_apply i).comp hpf
  exact (((h2.comp hsel).eval).eval)

/-- **The resolved-form A1-integral at ratios `z`** (`Jint`): the RHS A1-integral of the per-`z` bound,
`∫_{A1∈box34} ofReal((∑ⱼTⱼ² + frobSq(Δ·S))^{−c'})` with `T,Δ,S` read off `Rmat334norm p z`. The
ratio-side object whose `z`-integral feeds the resolved finiteness `resolved334_box_lt_top 3`. -/
noncomputable def Jint (c' : ℝ) (p : Fin 9) (z : Fin 8 → ℝ) : ℝ≥0∞ :=
  ∫⁻ A1 in matBox 3 4 1,
    ENNReal.ofReal (((∑ jj, (A1 0 jj
        + (Rmat334norm p z 0 1 * A1 1 jj + Rmat334norm p z 0 2 * A1 2 jj)) ^ 2)
      + frobSq (rmatMul
          (!![Rmat334norm p z 1 1 - Rmat334norm p z 1 0 * Rmat334norm p z 0 1,
               Rmat334norm p z 1 2 - Rmat334norm p z 1 0 * Rmat334norm p z 0 2;
              Rmat334norm p z 2 1 - Rmat334norm p z 2 0 * Rmat334norm p z 0 1,
               Rmat334norm p z 2 2 - Rmat334norm p z 2 0 * Rmat334norm p z 0 2]
            : Matrix (Fin 2) (Fin 2) ℝ)
          (fun k jj => A1 (k.succ) jj))) ^ (-c'))

/-- The joint `(z, A1)` resolved integrand is measurable (the `Rmat334norm` entries are measurable in
`z`, the `A1` entries in `A1`; the rest is `ofReal ∘ rpow ∘` a polynomial). -/
theorem measurable_Jint_integrand (c' : ℝ) (p : Fin 9) :
    Measurable (fun q : (Fin 8 → ℝ) × (Fin 3 → Fin 4 → ℝ) =>
      ENNReal.ofReal (((∑ jj, (q.2 0 jj
          + (Rmat334norm p q.1 0 1 * q.2 1 jj + Rmat334norm p q.1 0 2 * q.2 2 jj)) ^ 2)
        + frobSq (rmatMul
            (!![Rmat334norm p q.1 1 1 - Rmat334norm p q.1 1 0 * Rmat334norm p q.1 0 1,
                 Rmat334norm p q.1 1 2 - Rmat334norm p q.1 1 0 * Rmat334norm p q.1 0 2;
                Rmat334norm p q.1 2 1 - Rmat334norm p q.1 2 0 * Rmat334norm p q.1 0 1,
                 Rmat334norm p q.1 2 2 - Rmat334norm p q.1 2 0 * Rmat334norm p q.1 0 2]
              : Matrix (Fin 2) (Fin 2) ℝ)
            (fun k jj => q.2 (k.succ) jj))) ^ (-c'))) := by
  have hz : ∀ r c, Measurable (fun q : (Fin 8 → ℝ) × (Fin 3 → Fin 4 → ℝ) => Rmat334norm p q.1 r c) :=
    fun r c => (measurable_Rmat334norm_entry p r c).comp measurable_fst
  have hA : ∀ (a : Fin 3) (b : Fin 4),
      Measurable (fun q : (Fin 8 → ℝ) × (Fin 3 → Fin 4 → ℝ) => q.2 a b) :=
    fun a b => (measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd)
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  refine Measurable.add ?_ ?_
  · refine Finset.measurable_sum _ (fun jj _ => ?_)
    refine Measurable.pow_const ?_ 2
    exact (hA 0 jj).add ((hz 0 1).mul (hA 1 jj) |>.add ((hz 0 2).mul (hA 2 jj)))
  · unfold frobSq rmatMul
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.pow_const ?_ 2
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.mul ?_ (hA _ j)
    fin_cases i <;> fin_cases k <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
        Matrix.cons_val', Fin.isValue, Fin.mk_zero, Fin.mk_one] <;>
      exact (hz _ _).sub ((hz _ _).mul (hz _ _))

/-- `Jint c' p` is measurable in `z` (the A1-integral of the measurable joint integrand). -/
theorem measurable_Jint (c' : ℝ) (p : Fin 9) : Measurable (Jint c' p) := by
  unfold Jint
  exact Measurable.lintegral_prod_right (measurable_Jint_integrand c' p)

/-- **The ratio-residual ↔ resolved reduction (the per-`z` bound, integrated).** Over the box `[−1,1]^8`,
the ratio residual is dominated by the resolved-form integral:
`∫_z angA1Int c' p (e.symm (0,z)) ≤ ofReal((1/5)^{−c'}) · ∫_z Jint c' p z`. Integrate the per-`z`
pointwise bound `angA1Int_le_resolved` (`setLIntegral_mono_ae'` on the box), then pull the constant out. -/
theorem ratioResidual_le_Jint (c' : ℝ) (hc0 : 0 < c') (p : Fin 9) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
        angA1Int c' p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z)))
      ≤ ENNReal.ofReal (((1 : ℝ) / 5) ^ (-c'))
        * ∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)), Jint c' p z := by
  have hbox : MeasurableSet (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  calc (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
        angA1Int c' p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z)))
      ≤ ∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
          ENNReal.ofReal (((1 : ℝ) / 5) ^ (-c')) * Jint c' p z := by
        refine setLIntegral_mono_ae' hbox (ae_of_all _ (fun z hz => ?_))
        rw [Jint]
        exact angA1Int_le_resolved c' hc0 p z hz
    _ = ENNReal.ofReal (((1 : ℝ) / 5) ^ (-c'))
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)), Jint c' p z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ## STEP 3 — the resolved-form change of variables (the box-translation CoV) -/

/-- **The translation-and-enlargement atom.** For a shift `s : Fin n → ℝ` and a box-enlargement
`(· + s) '' B ⊆ BG`, the translated integral is dominated: `∫_{v∈B} f (v + s) ≤ ∫_{w∈BG} f w`
(`measurePreserving_add_right` MP-transports `∫_B f(·+s)` to `∫_{(·+s)''B} f`, then `lintegral_mono_set`
enlarges to `BG`). The MP shear that absorbs the `row0 ↦ T = row0 + β·S` and `raw ↦ Δ = raw − γβ`
translations into the resolved-form boxes. -/
theorem lintegral_translate_le (n : ℕ) (s : Fin n → ℝ)
    (B BG : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ≥0∞)
    (hsub : (fun v => v + s) '' B ⊆ BG) :
    (∫⁻ v in B, f (v + s)) ≤ ∫⁻ w in BG, f w := by
  set τ : (Fin n → ℝ) → (Fin n → ℝ) := fun v => v + s with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume s
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight s).measurableEmbedding
  have h1 : (∫⁻ v in B, f (τ v)) = ∫⁻ w in τ '' B, f w := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' B),
      Set.preimage_image_eq B hemb.injective]
  calc (∫⁻ v in B, f (v + s)) = ∫⁻ w in τ '' B, f w := h1
    _ ≤ ∫⁻ w in BG, f w := lintegral_mono_set hsub

/-- **The product-box reorder.** `∫_{morseBox 4 1 ×ˢ matBox 2 4 1} H = ∫_{S∈matBox} ∫_{row0∈morseBox} H`
(Tonelli `setLIntegral_prod` + `lintegral_lintegral_swap`); puts `S` outermost for the resolved form. -/
theorem prod_reorder (H : (Fin 4 → ℝ) × (Fin 2 → Fin 4 → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ q in (morseBox 4 1 ×ˢ matBox 2 4 1), H q)
      = ∫⁻ S in matBox 2 4 1, ∫⁻ row0 in morseBox 4 1, H (row0, S) := by
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hH.aemeasurable, lintegral_lintegral_swap]
  exact hH.aemeasurable

/-- **STEP-3a (the `z`-pointwise inner `T`-peel).** For FIXED `b0,b1` (`|·| ≤ 1`) and a fixed lower-right
block `S` of `A1`'s rows `1,2` (so `Δ`, `b` are constants), the `row0 ↦ T = row0 + β·S` translation peels
the spectator row: `∫_{row0∈morseBox 4 1} ofReal((∑ⱼ(row0 j + (b0·S 0 j + b1·S 1 j))² + frobSq(Δ·S))^{−c'})
≤ ∫_{T∈morseBox 4 3} ofReal((∑ⱼTⱼ² + frobSq(Δ·S))^{−c'})` (`lintegral_translate_le`, `|β·S| ≤ 2` so the box
enlarges `[−1,1]^4 → [−3,3]^4`). -/
theorem step3a_inner (c' : ℝ) (b0 b1 : ℝ) (hb0 : |b0| ≤ 1) (hb1 : |b1| ≤ 1)
    (Δ : Matrix (Fin 2) (Fin 2) ℝ) (S : Fin 2 → Fin 4 → ℝ) (hS : S ∈ matBox 2 4 1) :
    (∫⁻ row0 in morseBox 4 1,
      ENNReal.ofReal (((∑ jj, (row0 jj + (b0 * S 0 jj + b1 * S 1 jj)) ^ 2)
        + frobSq (rmatMul Δ S)) ^ (-c')))
      ≤ ∫⁻ T in morseBox 4 3,
          ENNReal.ofReal (((∑ jj, (T jj) ^ 2) + frobSq (rmatMul Δ S)) ^ (-c')) := by
  set shift : Fin 4 → ℝ := fun jj => b0 * S 0 jj + b1 * S 1 jj with hshift
  set f : (Fin 4 → ℝ) → ℝ≥0∞ := fun T =>
    ENNReal.ofReal (((∑ jj, (T jj) ^ 2) + frobSq (rmatMul Δ S)) ^ (-c')) with hf
  have hrw : ∀ row0 : Fin 4 → ℝ,
      ENNReal.ofReal (((∑ jj, (row0 jj + (b0 * S 0 jj + b1 * S 1 jj)) ^ 2)
        + frobSq (rmatMul Δ S)) ^ (-c')) = f (row0 + shift) := by
    intro row0; rw [hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_le 4 shift (morseBox 4 1) (morseBox 4 3) f ?_
  rintro T ⟨v, hv, rfl⟩
  simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro jj
  have hvj := Set.mem_Icc.1 (hv jj)
  have hb0' := abs_le.1 hb0
  have hb1' := abs_le.1 hb1
  have h0 := Set.mem_Icc.1 (hS 0 jj)
  have h1 := Set.mem_Icc.1 (hS 1 jj)
  have hp0 : -1 ≤ b0 * S 0 jj ∧ b0 * S 0 jj ≤ 1 := by
    constructor <;>
      nlinarith [hb0'.1, hb0'.2, h0.1, h0.2, sq_nonneg (b0 + S 0 jj), sq_nonneg (b0 - S 0 jj)]
  have hp1 : -1 ≤ b1 * S 1 jj ∧ b1 * S 1 jj ≤ 1 := by
    constructor <;>
      nlinarith [hb1'.1, hb1'.2, h1.1, h1.2, sq_nonneg (b1 + S 1 jj), sq_nonneg (b1 - S 1 jj)]
  rw [Set.mem_Icc, Pi.add_apply, hshift]
  constructor <;> [nlinarith [hvj.1, hp0.1, hp1.1]; nlinarith [hvj.2, hp0.2, hp1.2]]

/-- **STEP-3a (the inner `A1`-integral resolved bound).** For fixed `b0,b1` (`|·| ≤ 1`) and a fixed `2×2`
`Δ`, the `A1`-box integral is dominated by the `(S,T)` resolved-form integral:
`∫_{A1∈matBox 3 4 1} ofReal((∑ⱼ(A1 0 j + (b0·A1 1 j + b1·A1 2 j))² + frobSq(Δ·(A1 rows 1,2)))^{−c'})
≤ ∫_{S∈matBox 2 4 1}∫_{T∈morseBox 4 3} ofReal((∑ⱼTⱼ² + frobSq(Δ·S))^{−c'})`. Row-split `A1 = row0 × S`
(`piFinSuccAbove 0` on the row index, MP), reorder (`prod_reorder`), then `step3a_inner` per `S`. -/
theorem step3a (c' : ℝ) (b0 b1 : ℝ) (hb0 : |b0| ≤ 1) (hb1 : |b1| ≤ 1)
    (Δ : Matrix (Fin 2) (Fin 2) ℝ) :
    (∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal (((∑ jj, (A1 0 jj + (b0 * A1 1 jj + b1 * A1 2 jj)) ^ 2)
        + frobSq (rmatMul Δ (fun k jj => A1 (k.succ) jj))) ^ (-c')))
      ≤ ∫⁻ S in matBox 2 4 1, ∫⁻ T in morseBox 4 3,
          ENNReal.ofReal (((∑ jj, (T jj) ^ 2) + frobSq (rmatMul Δ S)) ^ (-c')) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Fin 4 → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => Fin 4 → ℝ) 0
  set H : (Fin 4 → ℝ) × (Fin 2 → Fin 4 → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ jj, (q.1 jj + (b0 * q.2 0 jj + b1 * q.2 1 jj)) ^ 2)
      + frobSq (rmatMul Δ q.2)) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun jj _ => ?_)
      refine Measurable.pow_const ?_ 2
      have h0 : Measurable (fun q : (Fin 4 → ℝ) × (Fin 2 → Fin 4 → ℝ) => q.1 jj) :=
        (measurable_pi_apply jj).comp measurable_fst
      have hS : ∀ a b, Measurable (fun q : (Fin 4 → ℝ) × (Fin 2 → Fin 4 → ℝ) => q.2 a b) :=
        fun a b => (measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd)
      exact h0.add ((measurable_const.mul (hS 0 jj)).add (measurable_const.mul (hS 1 jj)))
    · unfold frobSq rmatMul
      refine Finset.measurable_sum _ (fun i _ => ?_)
      refine Finset.measurable_sum _ (fun j _ => ?_)
      refine Measurable.pow_const ?_ 2
      refine Finset.measurable_sum _ (fun k _ => ?_)
      exact measurable_const.mul ((measurable_pi_apply j).comp
        ((measurable_pi_apply k).comp measurable_snd))
  have hsplit : matBox 3 4 1 = e ⁻¹' (morseBox 4 1 ×ˢ matBox 2 4 1) := by
    ext A1
    simp only [he, Set.mem_preimage, Set.mem_prod, matBox, morseBox, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h; exact ⟨fun j => h 0 j, fun i k => h i.succ k⟩
    · rintro ⟨h1, h2⟩ i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact h1 k
      · exact h2 i' k
  have hLHS : (∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal (((∑ jj, (A1 0 jj + (b0 * A1 1 jj + b1 * A1 2 jj)) ^ 2)
        + frobSq (rmatMul Δ (fun k jj => A1 (k.succ) jj))) ^ (-c')))
      = ∫⁻ q in (morseBox 4 1 ×ˢ matBox 2 4 1), H q := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        (morseBox 4 1 ×ˢ matBox 2 4 1)]
    refine setLIntegral_congr_fun ?_ (fun A1 _ => rfl)
    exact e.measurable
      (MeasurableSet.prod (morseBox_measurableSet 4 1) (matBox_measurableSet 2 4 1))
  rw [hLHS, prod_reorder H hHmeas]
  refine setLIntegral_mono_ae' (matBox_measurableSet 2 4 1) (ae_of_all _ (fun S hS => ?_))
  rw [lintegral_congr (fun row0 => (by rw [hHdef] : H (row0, S)
    = ENNReal.ofReal (((∑ jj, (row0 jj + (b0 * S 0 jj + b1 * S 1 jj)) ^ 2)
        + frobSq (rmatMul Δ S)) ^ (-c'))))]
  exact step3a_inner c' b0 b1 hb0 hb1 Δ S hS

/-- The resolved `(S,T)` inner integral at a fixed lower-right block `Δ`: `∫_{S∈matBox 2 4 1}∫_{T∈morseBox
4 3} ofReal((∑ⱼTⱼ² + frobSq(Δ·S))^{−c'})`. The `step3a` target; `∫_{Δ∈matBox 2 2 3} Ginner = the resolved
form` (`resolved334_box_lt_top 3` modulo box-radius enlargement of `S`). -/
noncomputable def Ginner (c' : ℝ) (Δ : Matrix (Fin 2) (Fin 2) ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox 2 4 1, ∫⁻ T in morseBox 4 3,
    ENNReal.ofReal (((∑ jj, (T jj) ^ 2) + frobSq (rmatMul Δ S)) ^ (-c'))

/-- The de-shifted lower-right `2×2` block `Δ = raw − γβ` read off `Rmat334norm p z` (the `angularR`
de-shift `d = raw − g·b`); each entry `R'(i+1,k+1) − g_i·b_k` of `z`-components. -/
noncomputable def Δof (p : Fin 9) (z : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Rmat334norm p z 1 1 - Rmat334norm p z 1 0 * Rmat334norm p z 0 1,
      Rmat334norm p z 1 2 - Rmat334norm p z 1 0 * Rmat334norm p z 0 2;
     Rmat334norm p z 2 1 - Rmat334norm p z 2 0 * Rmat334norm p z 0 1,
      Rmat334norm p z 2 2 - Rmat334norm p z 2 0 * Rmat334norm p z 0 2]

/-- **STEP-3a, applied at the ratios `z` (BANKED).** `Jint c' p z ≤ Ginner c' (Δof p z)` for `z∈[−1,1]^8`:
the inner `A1`-integral resolved bound `step3a` with `b = (R'(0,1),R'(0,2))` (`|b| ≤ 1` from
`Rmat334norm_offpivot_le`) and `Δ = Δof p z`. -/
theorem Jint_le_Ginner (c' : ℝ) (p : Fin 9) (z : Fin 8 → ℝ)
    (hz : z ∈ Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)) :
    Jint c' p z ≤ Ginner c' (Δof p z) := by
  unfold Jint Ginner Δof
  exact step3a c' (Rmat334norm p z 0 1) (Rmat334norm p z 0 2)
    (Rmat334norm_offpivot_le p z hz 0 1 (by simp)) (Rmat334norm_offpivot_le p z hz 0 2 (by simp)) _

/-- **STEP-3b (the outer `z`-change of variables — the ONE remaining `sorry`).** `∫_{z∈[−1,1]^8}
Ginner c' (Δof p z) < ⊤` for `2 < c' < 4`. Since `Ginner c' (Δof p z)` reads `z` only through the four
de-shifted entries `Δof p z = raw − γβ` (with `raw,g,b` eight DISTINCT `z`-components — the off-pivot
entries of `R' = Rmat334norm p z`), the `raw ↦ Δ` translation per fixed `(g,b)` (`lintegral_translate_le`,
`|γβ| ≤ 1` so `Δ∈[−2,2]^4 ⊆ matBox 2 2 3`) drops the `(g,b)` ratios to a finite vol-factor `vol([−1,1]^4)`
and bounds `∫_z Ginner(Δof) ≤ vol([−1,1]^4) · ∫_{Δ∈matBox 2 2 3} Ginner c' Δ`. The last integral is
`resolved334_box_lt_top 3` after enlarging `S : matBox 2 4 1 → matBox 2 4 3` (`lintegral_mono_set`).

GAP: the per-`p` identification of which `z`-slots are `raw/g/b` (the `(i,j) ↦
Fin.exists_succAbove_eq`-index relabeling, a coordinate permutation of `[−1,1]^8`), feeding the
`lintegral_translate_le` on the `raw`-subblock. Everything else — the resolved RHS, the translation atom,
the per-`z` `Ginner` reduction (`Jint_le_Ginner`) — is BANKED sorry-free. -/
theorem ginnerZ_lt_top (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) (p : Fin 9) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)), Ginner c' (Δof p z)) < ⊤ := by
  sorry

/-- **The resolved-form finiteness over the ratio box (STEP 3, the box-translation change of variables).**
`∫_{z∈[−1,1]^8} Jint c' p z < ⊤` for `2 < c' < 4`.

The `Jint` integrand is `(∑ⱼ Tⱼ² + frobSq(Δ·S))^{−c'}` with `Tⱼ = A1 0 j + (b0·A1 1 j + b1·A1 2 j)`,
`Δ_{ik} = R'(i+1,k+1) − g_i·b_k` (the de-shifted lower-right of `R' = Rmat334norm p z`), `S = A1` rows
`1,2`, and `(b,g,raw)` the eight `z`-components (the off-pivot entries of `R'`, each in `[−1,1]`). The
route (Codex `xhigh` VET, thread 29 `hratiofin-plan-answer.md`, order `b → g → raw → S → A0`):

1. peel `g` (a finite vol-factor: `g` enters only the de-shift, and the de-shifted `Δ`-coords are the
   integration variable after the `raw ↦ Δ` translation);
2. translate `row0 ↦ T = row0 + β·S` per fixed `(b,S)` (`lintegral_translate_le`, `|β·S| ≤ 2`, box
   `[−1,1]^4 → [−3,3]^4 = morseBox 4 3`); then `b` is a finite vol-factor;
3. translate the `raw`-subblock `raw ↦ Δ = raw − γβ` per fixed `(b,g)` (`lintegral_translate_le`,
   `|γβ| ≤ 1`, box `[−1,1]^4 → [−2,2]^4 ⊆ matBox 2 2 3`);
4. enlarge `S : matBox 2 4 1 → matBox 2 4 3` (`lintegral_mono_set`) and Fubini-reorder to `(Δ,S,T)`,
   feeding the BANKED `resolved334_box_lt_top 3` times the finite `(b,g)` vol-factor `vol([−1,1]^4)`.

GAP (`sorry`): this resolved-form joint `(z × A1)` change of variables. Everything feeding INTO it is
banked sorry-free — the per-`z` algebraic comparability (`angA1Int_le_resolved`), the pivot permutation
(`angA1Int_eq_norm`), the outer integration (`ratioResidual_le_Jint`); and the resolved RHS
`resolved334_box_lt_top 3` + the translation atom `lintegral_translate_le` are banked too. The cleanest
remaining decomposition (worked out, the two named sub-lemmas to add):

* **STEP-3a (the `z`-pointwise inner `T`-peel, the clean half).** For FIXED `z` (so `b0,b1,Δ` are
  constants), `Jint c' p z ≤ ∫_{S∈matBox 2 4 1}∫_{T∈morseBox 4 3} ofReal((∑ⱼTⱼ² + frobSq(Δ·S))^{−c'})`:
  row-split `A1 = row0 × S` (`piFinSuccAbove 0` on the row index, MP), Tonelli, translate
  `row0 ↦ T = row0 + β·S` per fixed `S` (`lintegral_translate_le`, `|β·S| ≤ 2` so `T∈[−3,3]^4`), enlarge.
* **STEP-3b (the outer `z`-CoV, the hard half — needs the per-`p` `z`-coordinate structure).** Bound the
  resulting `∫_z Ginner(Δ(z))` by `vol([−1,1]^4) · ∫_{Δ∈matBox 2 2 3} Ginner(Δ) = (16) ·
  resolved334_box_lt_top 3`, via the `raw ↦ Δ = raw − γβ` translation per fixed `(b,g)` (the `b,g,raw`
  are eight DISTINCT `z`-coords — the off-pivot entries of `R'` — so this is `lintegral_translate_le`
  on the `raw`-subblock with `b,g` held; identifying the raw/g/b coordinate slots per `p` is the
  bookkeeping pole, the `(i,j) ↦ Fin.exists_succAbove_eq`-index relabeling).

STEP-3a is now BANKED (`step3a`/`Jint_le_Ginner`); the lone remaining gap is STEP-3b (`ginnerZ_lt_top`). -/
theorem resolvedZ_lt_top (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) (p : Fin 9) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)), Jint c' p z) < ⊤ := by
  refine lt_of_le_of_lt ?_ (ginnerZ_lt_top c' hc2 hc4 p)
  refine setLIntegral_mono_ae' (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    (ae_of_all _ (fun z hz => ?_))
  exact Jint_le_Ginner c' p z hz

/-- **The ratio residual is finite (`hratiofin`).** `∫_{z∈[−1,1]^8} angA1Int c' p (e.symm (0,z)) < ⊤`
for `2 < c' < 4`. The per-`z` resolved bound (`ratioResidual_le_Jint`) caps it by
`ofReal((1/5)^{−c'}) · ∫_z Jint`, finite by `resolvedZ_lt_top`. The object the per-chart finiteness
`matBox334_chart_lt_top` consumes as `hratiofin`. -/
theorem ratioResidual_lt_top (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) (p : Fin 9) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
        angA1Int c' p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) p).symm (0, z))) < ⊤ := by
  refine lt_of_le_of_lt (ratioResidual_le_Jint c' (by linarith) p) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (resolvedZ_lt_top c' hc2 hc4 p)


/-! ## The 9-chart cover + the `(3,3,4)` hfin headline (relocated from `RouteM334Hfin`: they
consume the now-discharged `hratiofin` = `ratioResidual_lt_top`, so live here to avoid an import
cycle; all the cover/transport atoms they use stay in `RouteM334Hfin`). -/
/-- **The blow-up bridge, the `2 < c'` core.** `∫_{A0 box}∫_{A1 box} frobSq(A0·A1)^{−c'} < ⊤` for
`2 < c' < 4`. The full `0 < c' < 4` statement reduces to this via the exponent-bump
(`matBox334_blowup_lt_top`). The 9-chart A0-entry radial cover assembly: flatten A0 (`matToFlatEquiv 3 3`,
MP), cover the inner `A0`-integral by the 9 max-modulus-entry charts (`recStep` on `univ : Finset (Fin 9)`,
folding the box indicator), each chart finite (`matBox334_chart_lt_top`), summed by `ENNReal.sum_lt_top`.
The cover-to-sum is proven here; the per-chart finiteness is the named transport gap. -/
theorem matBox334_blowup_lt_top_gt2 (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) :
    ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) < ⊤ := by
  -- Reindex A0 to the flat `Fin 9` carrier (MP), then `recStep` (univ argmax-cover) splits the
  -- A0-integral into the 9 max-modulus-entry chart sum; each chart is finite, summed by `sum_lt_top`.
  rw [matBox334_outer_flat c']
  rw [recStep (Finset.univ : Finset (Fin 9)) 0 (Finset.mem_univ 0)
      flatBox334 flatBox334_measurableSet (gFlat334 c')]
  exact ENNReal.sum_lt_top.2 (fun p _ => matBox334_chart_lt_top c' hc2 hc4 p (ratioResidual_lt_top c' hc2 hc4 p))

theorem matBox334_blowup_lt_top (c' : ℝ) (hc0 : 0 < c') (hc4 : c' < 4) :
    ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) < ⊤ := by
  rcases le_or_gt c' 2 with hc2 | hc2
  · -- 0 < c' ≤ 2: bump the exponent to c'' = 3 ∈ (2,4) by the pointwise `F^{−c'} ≤ 1 + F^{−3}` bound.
    -- ∫∫ F^{−c'} ≤ ∫∫ 1 + ∫∫ F^{−3} = vol·vol + (the 2<c'' cover) < ⊤.
    have hbump : ∀ (A0 : Fin 3 → Fin 3 → ℝ) (A1 : Fin 3 → Fin 4 → ℝ),
        ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
        ≤ 1 + ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := by
      intro A0 A1
      have h := rpow_neg_le_one_add_rpow_neg (frobSq (rmatMul A0 A1)) (frobSq_nonneg _) c' 3 hc0
        (by linarith)
      calc ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
          ≤ ENNReal.ofReal (1 + (frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := ENNReal.ofReal_le_ofReal h
        _ = 1 + ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := by
            rw [ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg (frobSq_nonneg _) _),
              ENNReal.ofReal_one]
    -- the c'' = 3 cover
    have hcover3 := matBox334_blowup_lt_top_gt2 3 (by norm_num) (by norm_num)
    -- the constant-1 integral over the two boxes
    have hvolfin : ∀ p n : ℕ, volume (matBox p n 1) < ⊤ := by
      intro p n
      have hcpt : IsCompact (matBox p n (1 : ℝ)) := by
        have heq : matBox p n (1 : ℝ)
            = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hvol : ∫⁻ _A0 in matBox 3 3 1, ∫⁻ _A1 in matBox 3 4 1, (1 : ℝ≥0∞) < ⊤ := by
      rw [setLIntegral_const, setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.one_lt_top (hvolfin 3 4)) (hvolfin 3 3)
    -- the c'' = 3 inner-integral measurability (for `lintegral_add`)
    have hmeas3 : ∀ A0 : Fin 3 → Fin 3 → ℝ, Measurable (fun A1 : Fin 3 → Fin 4 → ℝ =>
        ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ)))) := by
      intro A0
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.comp (g := fun t : ℝ => t ^ (-(3 : ℝ))) (by fun_prop)
      unfold frobSq rmatMul; fun_prop
    -- combine
    calc ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
            ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c'))
        ≤ ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
            (1 + ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ)))) :=
          lintegral_mono fun A0 => lintegral_mono fun A1 => hbump A0 A1
      _ = (∫⁻ _A0 in matBox 3 3 1, ∫⁻ _A1 in matBox 3 4 1, (1 : ℝ≥0∞))
            + ∫⁻ A0 in matBox 3 3 1, ∫⁻ A1 in matBox 3 4 1,
                ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(3 : ℝ))) := by
          rw [← lintegral_add_left' (by
            exact (Measurable.lintegral_prod_right (measurable_const)).aemeasurable) _]
          refine setLIntegral_congr_fun (matBox_measurableSet 3 3 1) (fun A0 _ => ?_)
          rw [← lintegral_add_left' (measurable_const).aemeasurable]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hvol, hcover3⟩
  · exact matBox334_blowup_lt_top_gt2 c' hc2 hc4

/-- **The `(3,3,4)` hfin upper bound (the N4 depth-2 instance, GAP = the blow-up bridge ONLY).** For
`c' < ½·minAdm M334 = 4`, `∫⁻_{routeMBaseNbhd M334} |routeMCore M334 x|^{−c'} < ⊤`. The rank-stratified
analog of `routeMCore_M4422_threshold_lt_top`.

The additive-threshold composition `4 = 2 + 2` is **BUILT** (`resolved334_lt_top`, axiom-clean S2-free): the
`‖T‖²` Morse-spectator peel (`core_T_peel_le_ae`, threshold `2`) feeds the corank-2 core `frobSq (Δ·S)` at
the shifted exponent `c'' = c' − 2 < 2`, resolved by the S-first transpose-fibre route (`core334_lt_top`,
threshold `λ_{2,4} = 2`, avoiding the radial minor-pivot recursion). The core-`> 0`-a.e. fact the T-peel
rides on is BUILT (`frobSq_core334_ne_zero_ae`, via the polynomial `corePoly334` + the MP flatten
`flat334`).

GAP (`sorry`): the FRAME TRANSPORT alone — a measure-preserving cover-up-to-null of `routeMBaseNbhd M334 =
(−1,1)^21` bringing the flat `routeMCore M334 = frobSq(A0·A1)` (A0 3×3, A1 3×4) into the `‖T‖² ⊕ frobSq(Δ·S)`
normal form of `resolved334_lt_top`, via the Schur-frame blow-up `g5_pivotNode`/`recStep` atlas (the
`(2,2,2)` `myF222_threshold_lt_top'` analog at the `r²`-chart scale). The singularity binds at the
A1-rank-drop locus (nonlinear/rank-local — no elementary global reparametrization). The achiever chart
`chartParams334`/`Uval334` (`RouteMLayerCoverGEL2`) realises this transport on the lower-bound side; the
UPPER-bound full cover is the remaining measure-theoretic long pole. Everything DOWNSTREAM of the transport
(`resolved334_lt_top` + the T-peel + the core resolution + the null set) is BANKED sorry-free, axiom-clean. -/
theorem routeMCore_M334_threshold_lt_top (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm (![3, 3, 4] : Fin 3 → ℕ) : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd (![3, 3, 4] : Fin 3 → ℕ),
      ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) < ⊤ := by
  rw [minAdm_M334_eq] at hc'
  have hc4 : (c' : ℝ) < 4 := by linarith
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand is (·)^0 = 1, integral = volume(box) < ⊤.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hone : ∀ x, ENNReal.ofReal (|routeMCore (![3, 3, 4] : Fin 3 → ℕ) x| ^ (-(c' : ℝ))) = 1 := by
      intro x; rw [hzero]; simp [Real.rpow_zero]
    simp only [hone]
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.one_lt_top ?_
    rw [routeMBaseNbhd]
    have hopen_sub : flatOpenBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ))
        ⊆ cubeBox (routeMAmbient (![3, 3, 4] : Fin 3 → ℕ)) 1 := by
      intro x hx i _
      have := hx i (Set.mem_univ i); rw [Set.mem_Ioo] at this
      rw [Set.mem_Icc]; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
    refine lt_of_le_of_lt (measure_mono hopen_sub) ?_
    exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  · -- 0 < c' < 4: reduce to the two-matrix-box integral, then the blow-up bridge.
    exact lt_of_le_of_lt (routeMCore_M334_le_matBox (c' : ℝ) hc0)
      (matBox334_blowup_lt_top (c' : ℝ) hc0 hc4)

end DLNFibre.DLN.RLCT
