import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJShellSubset` — the head-split (a)/hstrict per-shell finiteness

**The re-scoped target (`genm-rescopefin`).** The head-split spine integrand at a legal cut `u = t★+j`
and flag level `j` is bounded — by a pure **subset** argument, NO domination constant — by the bare
full-chain layer-product box `routeMLayerBoxIntegral M c' 1`:

  `shellSpineIntegrand M u κ ε r jf c' ≤ routeMLayerBoxIntegral M c' 1`   (`shellSpineIntegrand_le_layerBox`).

The route is a composition of banked atomic reductions, per `(A' fixed)`:
* un-free the Schur loss to the front-block box: `chartInner_schurShearFree_eq` (EQUALITY, any `Q`) +
  `frobSq_schur_split_inv` (`schurLoss = frobSq(B·Q)` on `{IsUnit toBlocks₁₁}`);
* block-reindex the front-block box back to the raw front factor `A₀` over `matBox (M 0) (M 1)` intersect
  the pivot chart: `chartInner_blockReindex_eq_of_emb` (`ρ = castLEEmb`, `κ`);
* **drop** the pivot chart (`IsUnit P`) and the shell — both monotone (nonneg integrand);
* reassemble `(A₀, A')` to `Params M` via the head split `paramsHeadSplit` (MP) + `prod_headSplit`
  (`prod M A = rmatMul (A 0) (prod (dropHead M) (A∘succ))`).

Then the **finiteness** below the carrier threshold `T1 = ½·minAdm M` follows from the box finiteness:
* general `M`: `shellSpineIntegrand_lt_top_of_box`, given `RouteMBoxThresholdFinite M` (the named
  full-chain analytic gap — for `L ≥ 1` this is the recursion's own top-level goal, so the shell-`j`
  finiteness rests on it; NAMED here, not buried);
* **`L = 0` (3-width leaf): `shellSpineIntegrand_lt_top_leaf`, UNCONDITIONAL** via the banked
  `routeMBoxThresholdFinite_mnp`.

This targets `T1 = ½·minAdm M` throughout — NOT the per-cut comparator range `T2 = (minAdm(redChain u M)
+ ab)/2`, which is exactly the over-claim that made `frobSqBlockFull_lt_top` false (thresholdhunt). Dropping
`IsUnit P` is sound HERE (a null-set enlargement; the off-shell full box has RLCT `= T1`), whereas the
prior wall's divergence came from dropping the SHELL while chasing `T2` (shelljhunt, decorrelated-confirmed).

CAVEAT (soundness, next to the claim): this subset bound is CIRCULAR for the box-finiteness INDUCTION —
it bounds a peel-component of the chain-`M` box by the chain-`M` box itself, so it does NOT supply the
reduced-comparator domination the `L ≥ 1` recursion needs (that remains the strong-minor Brick D). It
closes the STATED per-shell finiteness target; it does not advance the capstone induction.

S2-FREE: banked matrix/measure plumbing only. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The inner reduction (per `A'`).** For a fixed tail parameter `A'`, the freed-Schur spine inner
double integral equals the raw front-factor chart integral over `matBox (M 0) (M 1) ∩ pivotChart`, then
is dominated by the full `matBox` integral. `Q = prod (tailChain M) A'` (row type `Fin (M 1)`); the
front block is reindexed by `castLEEmb : Fin u ↪ Fin (M 0)` (rows) and `blockSplitEquiv κ` (columns). -/
theorem shellSpine_inner_le_matBox (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (hu : u ≤ M 0) (c' : ℝ) (A' : Params (tailChain M)) :
    (∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ
            ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')))
      ≤ ∫⁻ A₀ in matBox (M 0) (M 1) 1,
          ENNReal.ofReal ((frobSq (rmatMul A₀ (prod (tailChain M) A'))) ^ (-c')) := by
  classical
  -- EQUALITY: the freed inner double integral equals the raw front-factor chart integral over
  -- `matBox ∩ pivotChart` (`chartInner_blockReindex_eq_of_emb` reindexes; `chartInner_schurShearFree_eq`
  -- + `frobSq_schur_split_inv` un-free the Schur loss). Then drop the pivot chart (monotone).
  have key :
      (∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')))
        = ∫⁻ A₀ in matBox (M 0) (M 1) 1 ∩ pivotChart (Fin.castLEEmb hu) κ,
            ENNReal.ofReal ((frobSq (rmatMul A₀ (prod (tailChain M) A'))) ^ (-c')) := by
    rw [chartInner_blockReindex_eq_of_emb (Fin.castLEEmb hu) κ (prod (tailChain M) A') c' 1,
      ← chartInner_schurShearFree_eq ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id) c' 1]
    refine setLIntegral_congr_fun
      ((measurableSet_genBox 1).inter measurableSet_isUnit_toBlocks₁₁) (fun B hB => ?_)
    exact congrArg (fun s : ℝ => ENNReal.ofReal (s ^ (-c')))
      (frobSq_schur_split_inv (Matrix.of B) hB.2
        ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)).symm
  rw [key]
  -- drop the pivot chart (`IsUnit P`): monotone.
  exact lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl

/-- **The head-split reassembly of the bare box.** The double integral (tail `A'` outer, front `A₀`
inner) of `frobSq(rmatMul A₀ (prod (tailChain M) A'))^{−c'}` over `paramsBoxM (tailChain M) 1 ×
matBox (M 0) (M 1) 1` equals the full-chain layer-product box `routeMLayerBoxIntegral M c' 1`. -/
theorem tailFront_box_eq_layerBox (M : Fin (L + 1 + 1 + 1) → ℕ) (c' : ℝ) :
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ A₀ in matBox (M 0) (M 1) 1,
          ENNReal.ofReal ((frobSq (rmatMul A₀ (prod (tailChain M) A'))) ^ (-c')))
      = routeMLayerBoxIntegral M c' 1 := by
  classical
  -- the tail-first head-split equiv `Params M ≃ᵐ Params (dropHead M) × (front block)`.
  set e : Params M ≃ᵐ Params (dropHead M) × (Fin (M 0) → Fin (M 1) → ℝ) :=
    (paramsHeadSplit M).trans MeasurableEquiv.prodComm with he
  have hmp : MeasurePreserving e (volume : Measure (Params M)) volume :=
    (paramsHeadSplit_mp M).trans
      (by rw [Measure.volume_eq_prod]; exact Measure.measurePreserving_swap)
  -- preimage of the tail × front box under `e` is `paramsBoxM M 1`.
  have hswap : (MeasurableEquiv.prodComm ⁻¹'
        (paramsBoxM (dropHead M) 1 ×ˢ matBox (M 0) (M 1) 1) :
        Set ((Fin (M 0) → Fin (M 1) → ℝ) × Params (dropHead M)))
      = matBox (M 0) (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1 := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  have hpre : e ⁻¹' (paramsBoxM (dropHead M) 1 ×ˢ matBox (M 0) (M 1) 1) = paramsBoxM M 1 := by
    rw [he]
    show paramsHeadSplit M ⁻¹'
        (MeasurableEquiv.prodComm ⁻¹' (paramsBoxM (dropHead M) 1 ×ˢ matBox (M 0) (M 1) 1))
      = paramsBoxM M 1
    rw [hswap]
    exact paramsHeadSplit_preimage_box M
  -- the transported integrand is measurable (frobSq continuous ∘ prod continuous ∘ e.symm measurable).
  have hgmeas : Measurable (fun y : Params (dropHead M) × (Fin (M 0) → Fin (M 1) → ℝ) =>
      ENNReal.ofReal ((frobSq (prod M (e.symm y))) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun r : ℝ => r ^ (-c')) (by fun_prop)
    exact ((continuous_frobSq.comp (continuous_prod M)).measurable).comp e.symm.measurable
  -- transport `routeMLayerBoxIntegral` through `e` (MP) to the product box.
  have htrans : routeMLayerBoxIntegral M c' 1
      = ∫⁻ y in paramsBoxM (dropHead M) 1 ×ˢ matBox (M 0) (M 1) 1,
          ENNReal.ofReal ((frobSq (prod M (e.symm y))) ^ (-c')) := by
    rw [routeMLayerBoxIntegral]
    have hcomp := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding e)
      (fun y => ENNReal.ofReal ((frobSq (prod M (e.symm y))) ^ (-c')))
      (paramsBoxM (dropHead M) 1 ×ˢ matBox (M 0) (M 1) 1)
    rw [hpre] at hcomp
    rw [← hcomp]
    refine setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans, Measure.volume_eq_prod (Params (dropHead M)) (Fin (M 0) → Fin (M 1) → ℝ),
    setLIntegral_prod _ hgmeas.aemeasurable]
  -- Fubini: tail outer, front inner; then rewrite the joined product by `prod_headSplit`.
  refine setLIntegral_congr_fun (measurableSet_paramsBoxM (dropHead M) 1) (fun A' _ => ?_)
  refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A₀ _ => ?_)
  -- the head-split of `e.symm (A', A₀)`: layer 0 is `A₀`, deeper layers are `A'`.
  have happ : e.symm (A', A₀) = (paramsHeadSplit M).symm (A₀, A') := by rw [he]; rfl
  have hround : paramsHeadSplit M ((paramsHeadSplit M).symm (A₀, A')) = (A₀, A') :=
    (paramsHeadSplit M).apply_symm_apply (A₀, A')
  have h0 : (e.symm (A', A₀)) 0 = A₀ := by
    rw [happ]
    have h := paramsHeadSplit_fst M ((paramsHeadSplit M).symm (A₀, A'))
    rw [hround] at h; exact h.symm
  have hsucc : (fun j : Fin (L + 1) => (e.symm (A', A₀)) j.succ) = A' := by
    funext j
    rw [happ]
    have h := paramsHeadSplit_snd M ((paramsHeadSplit M).symm (A₀, A')) j
    rw [hround] at h; exact h.symm
  rw [prod_headSplit M (e.symm (A', A₀)), h0, hsucc]
  -- `prod (dropHead M) A' = prod (tailChain M) A'` (both `fun i ↦ M i.succ`, defeq).
  rfl

/-- **The head-split per-shell finiteness bound (subset route).** At a legal cut `u = t★+j ≤ M 0`, the
head-split spine integrand at ANY flag level (`ε, r, jf` free) is bounded by the bare full-chain
layer-product box `routeMLayerBoxIntegral M c' 1` — a pure subset argument, no domination constant. -/
theorem shellSpineIntegrand_le_layerBox (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (hu : u ≤ M 0) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ) :
    shellSpineIntegrand M u κ ε r jf c' ≤ routeMLayerBoxIntegral M c' 1 := by
  classical
  rw [shellSpineIntegrand]
  -- per-`A'` inner reduction, then drop the shell, then reassemble the bare box.
  refine le_trans (lintegral_mono (fun A' => shellSpine_inner_le_matBox M u κ hu c' A')) ?_
  refine le_trans
    (lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl) ?_
  exact le_of_eq (tailFront_box_eq_layerBox M c')

/-- **The head-split per-shell finiteness, given the full-chain box finiteness.** For `0 ≤ c' <
carrierThreshold M = ½·minAdm M` and `RouteMBoxThresholdFinite M` (the named full-chain analytic gap;
for `L ≥ 1` this is the recursion's own goal — the shell finiteness rests on it), the head-split spine
integrand is finite. -/
theorem shellSpineIntegrand_lt_top_of_box (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (hu : u ≤ M 0) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ)
    (hc0 : 0 ≤ c') (hc' : c' < carrierThreshold M) (hbox : RouteMBoxThresholdFinite M) :
    shellSpineIntegrand M u κ ε r jf c' < ⊤ := by
  refine lt_of_le_of_lt (shellSpineIntegrand_le_layerBox M u κ hu ε r jf c') ?_
  have hlt : ((⟨c', hc0⟩ : NNReal) : ℝ) < (minAdm M : ℝ) / 2 := by
    rw [carrierThreshold] at hc'; exact hc'
  exact hbox ⟨c', hc0⟩ hlt

/-- **The head-split per-shell finiteness at the 3-width leaf (`L = 0`), UNCONDITIONAL.** For a 3-width
chain `M = (M 0, M 1, M 2)` and `0 ≤ c' < carrierThreshold M = ½·minAdm M`, the head-split spine
integrand is finite — the full-chain box finiteness is the banked `routeMBoxThresholdFinite_mnp`. -/
theorem shellSpineIntegrand_lt_top_leaf (M : Fin (0 + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (hu : u ≤ M 0) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ)
    (hc0 : 0 ≤ c') (hc' : c' < carrierThreshold M) :
    shellSpineIntegrand M u κ ε r jf c' < ⊤ := by
  have hMeq : M = ![M 0, M 1, M 2] := by
    funext i; fin_cases i <;> rfl
  have hbox : RouteMBoxThresholdFinite M := hMeq ▸ routeMBoxThresholdFinite_mnp (M 0) (M 1) (M 2)
  exact shellSpineIntegrand_lt_top_of_box M u κ hu ε r jf c' hc0 hc' hbox

end DLNFibre.DLN.RLCT
