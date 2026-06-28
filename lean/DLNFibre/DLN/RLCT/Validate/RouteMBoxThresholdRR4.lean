import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral

/-!
# `RouteMBoxThresholdRR4` — the binding-p=4 `(r,r,4)` family `hbox` discharge

The carve-based discharge of the named gap `RouteMBoxThresholdFinite M` for the **depth-2 `(r,r,4)`
family** — generalising the `(3,3,4)` anchor (`r=3`) to ALL `r`. This is the only family that reaches
the geometric threshold `½·minAdm` through the `p=4` SchurCore chain: `prod (![r,r,4]) A = A0·A1` with
`A0 : r×r`, `A1 : r×4`, which is *exactly* the `SchurCore 4 r` shape (`Δ` square `r×r`, `S` the `r×4`
free block) — no front-peel, no shape massage.

## Why only `(r,r,4)` (the honest scope)

The broad "binding-p=4 family" is a **research wall** (decorrelated-Codex `xhigh`-confirmed,
`spec-front-peel-bridge.md`): (1) for depth `≥ 3` the iterated-fibre front-peel caps at `min_s M_s/2`,
strictly below `½·minAdm` (which is the SUM over the binding rank path); (2) off the `(r,r,4)` tail the
residual two-matrix core is not the square-`Δ` × `r×4` `SchurCore 4 r` shape. So the depth-`≥3`
arbitrary-`M` hfin is the L-layer JOINT rank resolution — left as the precisely-named gap
`RouteMBoxThresholdFinite` for general `M`. The depth-2 `(r,r,p)` ∀p extension is a *different* carve
(`SchurCore p r`), scoped separately.

## The threshold match (verified)

`minAdm (![r,r,4]) = 4r−4 = 2·schurLambda r` (the `t`-min of `(r−t)²+4t` over the real `minAdmRec`
recursion; numerically exact r=0..7), so `½·minAdm = schurLambda r` — the gate fires up to EXACTLY the
SchurCore chain's threshold, non-vacuous ∀r.

## S2-hygiene
The `SchurCore` chain is S2-free (`RouteMSchurFiring` header); the discharge rides only the `hstep :
SchurRecStep 4 schurLambda` hypothesis (the carve, now landed + certified) — no `monomial_rlct`, no new
axiom. `minAdm_rr4_eq` is pure `ℕ`/`inf'` arithmetic.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## D1 — the threshold arithmetic `minAdm (![r,r,4]) = 4r−4 = 2·schurLambda r` -/

/-- `4s ≤ s²+4` over `ℕ` (the `(s−2)² ≥ 0` core). `s < 2` by `interval_cases`; `s ≥ 2` (write
`s = u+2`) by `ring_nf`/`omega`. The kernel of the corank-recursion `inf'` lower bound. -/
theorem four_mul_le_sq_add_four (s : ℕ) : 4 * s ≤ s * s + 4 := by
  rcases Nat.lt_or_ge s 2 with h | h
  · interval_cases s <;> omega
  · obtain ⟨u, hu⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
    subst hu; ring_nf; omega

/-- The per-leaf term lower bound `4r−4 ≤ (r−t)²+4t` for `t ≤ r` (the binding codim is `4r−4`, attained
at `t = r−2`). Via `r = t+s`, reduces to `four_mul_le_sq_add_four s`. -/
theorem rr4_term_ge (r t : ℕ) (hle : t ≤ r) : 4 * r - 4 ≤ (r - t) * (r - t) + t * 4 := by
  obtain ⟨s, hs⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
  subst hs
  rw [Nat.add_sub_cancel_left]
  have key := four_mul_le_sq_add_four s
  omega

/-- **The corank-recursion value at `(r,r,4)`** (`r ≥ 2`): `minAdmRec (![r,r,4]) = 4r−4`. The layer-peel
`inf'_{t≤r} ((r−t)²+4t)` is `4r−4`: `le` via the witness `t = r−2`, `ge` via `rr4_term_ge`. The
`(![r,r,4]) 0/1 = r` reductions are handled in the leaf goals (never rewritten under the `inf'`
dependent-nonempty motive). -/
theorem minAdmRec_rr4_ge2 (r : ℕ) (hr : 2 ≤ r) :
    minAdmRec (![r, r, 4] : Fin 3 → ℕ) = 4 * r - 4 := by
  rw [minAdmRec_succ_succ]
  have hterm : ∀ t : ℕ, ((![r, r, 4] : Fin 3 → ℕ) 0 - t) * ((![r, r, 4] : Fin 3 → ℕ) 1 - t)
      + minAdmRec (redChain t (![r, r, 4] : Fin 3 → ℕ)) = (r - t) * (r - t) + t * 4 := by
    intro t
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [minAdmRec_leaf]; simp [redChain]
  apply le_antisymm
  · refine Finset.inf'_le_of_le _ (b := r - 2)
      (Finset.mem_range.mpr (by show r - 2 < min r r + 1; rw [min_self]; omega)) ?_
    rw [hterm (r - 2)]
    have hsub : r - (r - 2) = 2 := by omega
    rw [hsub]; omega
  · refine Finset.le_inf' _ _ (fun t ht => ?_)
    rw [Finset.mem_range] at ht
    have hmin : min ((![r, r, 4] : Fin 3 → ℕ) 0) ((![r, r, 4] : Fin 3 → ℕ) 1) = r := by
      show min r r = r; exact min_self r
    rw [hmin] at ht
    rw [hterm t]
    exact rr4_term_ge r t (by omega)

/-- **D1 — `minAdm_rr4_eq`.** `½·minAdm (![r,r,4]) = schurLambda r` for all `r`. For `r ≥ 2` both sides
are `2r−2` (`minAdm = minAdmRec = 4r−4`, `schurLambda r = 2r−2`); `r = 0,1` are the `0, ½` leaves. The
threshold-match keystone: the `(r,r,4)` gate fires up to exactly the SchurCore chain's `schurLambda r`. -/
theorem minAdm_rr4_eq (r : ℕ) : (minAdm (![r, r, 4] : Fin 3 → ℕ) : ℝ) / 2 = schurLambda r := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · -- r = 0 or r = 1: minAdm = minAdmRec, compute by `decide`.
    interval_cases r
    · have : minAdm (![0, 0, 4] : Fin 3 → ℕ) = 0 := by rw [← minAdmRec_eq_minAdm]; decide
      rw [this, schurLambda_zero]; norm_num
    · have : minAdm (![1, 1, 4] : Fin 3 → ℕ) = 1 := by rw [← minAdmRec_eq_minAdm]; decide
      rw [this, schurLambda_one]; norm_num
  · -- r ≥ 2: minAdm = 4r−4, schurLambda r = 2r−2.
    rw [← minAdmRec_eq_minAdm, minAdmRec_rr4_ge2 r hr, schurLambda_eq_of_ge_two hr]
    have h4 : (4 : ℕ) ≤ 4 * r := by omega
    rw [Nat.cast_sub h4]
    push_cast
    ring

/-! ## D2 — the depth-2 layer reshape `eParamsRR4 r` -/

/-- The `Fin 1` tail family after peeling layer `0` (the layer-`1` fiber `r×4`) of `(![r,r,4])`. -/
abbrev TailFamRR4 (r : ℕ) : Fin 1 → Type :=
  fun s : Fin 1 => Fin ((![r, r, 4] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).castSucc) →
    Fin ((![r, r, 4] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).succ) → ℝ

/-- **The `Params (![r,r,4])` split into the two layer matrix boxes, in `(A0, A1)` order.** Peel layer
`0` (the `r×r` A0) then collapse the singleton `Fin 1` tail (the `r×4` A1) via `piUnique`. An MP reshape
with components `(eParamsRR4 r A).1 = A 0`, `.2 = A 1` (both definitional). The ∀r generalisation of
`eParams334`. -/
noncomputable def eParamsRR4 (r : ℕ) :
    Params (![r, r, 4] : Fin 3 → ℕ) ≃ᵐ (Fin r → Fin r → ℝ) × (Fin r → Fin 4 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun s : Fin 2 => Fin ((![r, r, 4] : Fin 3 → ℕ) s.castSucc) →
        Fin ((![r, r, 4] : Fin 3 → ℕ) s.succ) → ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piUnique (TailFamRR4 r)))

theorem measurePreserving_eParamsRR4 (r : ℕ) :
    MeasurePreserving (eParamsRR4 r) (volume : Measure (Params (![r, r, 4] : Fin 3 → ℕ))) volume := by
  unfold eParamsRR4
  refine (volume_preserving_piFinSuccAbove _ 0).trans ?_
  have hp := (MeasurePreserving.id (volume : Measure (Fin r → Fin r → ℝ))).prod
    (volume_preserving_piUnique (TailFamRR4 r))
  rw [show (volume : Measure ((Fin r → Fin r → ℝ) × (Fin r → Fin 4 → ℝ)))
    = volume.prod volume from rfl]
  exact hp

/-- `eParamsRR4 r ⁻¹' (matBox r r 1 ×ˢ matBox r 4 1) = paramsBoxM (![r,r,4]) 1` (the two layer boxes
pull back to the all-entries-bounded `Params` box; `fin_cases` on the layer index). -/
theorem eParamsRR4_preimage_box (r : ℕ) :
    eParamsRR4 r ⁻¹' (matBox r r 1 ×ˢ matBox r 4 1) = paramsBoxM (![r, r, 4] : Fin 3 → ℕ) 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1⟩ s i j
    fin_cases s
    · exact h0 i j
    · exact h1 i j
  · intro h
    exact ⟨fun i j => h 0 i j, fun i j => h 1 i j⟩

/-- **Generic `L = 2` layer-product entry form** `(prod M A) i j = ∑ₖ A₀ᵢₖ·A₁ₖⱼ` (re-derived locally
to avoid importing the `RouteM334` Hfin file; the same `prodAux` dependent-`Fin`-cast closer). -/
theorem prod_two_layer_rr4 (M : Fin 3 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 2)) :
    prod M A i j = ∑ k : Fin (M 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

/-- The integrand identity: `frobSq (prod (![r,r,4]) A) = frobSq (rmatMul A0 A1)` read off the
`eParamsRR4` components (`A0, A1` are `(eParamsRR4 r A).1, .2`). Via `prod_two_layer_rr4`. -/
theorem frobSq_prod_eq_eParamsRR4 (r : ℕ) (A : Params (![r, r, 4] : Fin 3 → ℕ)) :
    frobSq (prod (![r, r, 4] : Fin 3 → ℕ) A)
      = frobSq (rmatMul (eParamsRR4 r A).1 (eParamsRR4 r A).2) := by
  change frobSq (prod (![r, r, 4] : Fin 3 → ℕ) A) = frobSq (rmatMul (A 0) (A 1))
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show prod (![r, r, 4] : Fin 3 → ℕ) A i j
      = rmatMul (fun i k => A 0 i k) (fun k j => A 1 k j) i j from by
    rw [prod_two_layer_rr4 (![r, r, 4] : Fin 3 → ℕ) A i j]; rfl]

theorem measurableSet_paramsBoxM_rr4 (r : ℕ) :
    MeasurableSet (paramsBoxM (![r, r, 4] : Fin 3 → ℕ) 1) :=
  measurableSet_paramsBoxM (![r, r, 4] : Fin 3 → ℕ) 1

/-! ## D3 — the reshape identity `routeMLayerBoxIntegral (r,r,4) = ∫∫ frobSq(A0·A1)` -/

/-- **D3 — `routeMLayerBoxIntegral_rr4_eq`.** `routeMLayerBoxIntegral (![r,r,4]) c' 1 = ∫_{A0∈matBox r r
1}∫_{A1∈matBox r 4 1} frobSq(A0·A1)^{−c'}` — the layer-product box integral reshaped (via `eParamsRR4`
MP + Tonelli) to the two per-layer matrix boxes. The ∀r generalisation of
`routeMLayerBoxIntegral_M334_eq`. -/
theorem routeMLayerBoxIntegral_rr4_eq (r : ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral (![r, r, 4] : Fin 3 → ℕ) c' 1
      = ∫⁻ A0 in matBox r r 1, ∫⁻ A1 in matBox r 4 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) := by
  rw [routeMLayerBoxIntegral]
  have hmpP := measurePreserving_eParamsRR4 r
  have hstep3 : ∫⁻ A in paramsBoxM (![r, r, 4] : Fin 3 → ℕ) 1,
        ENNReal.ofReal (frobSq (prod (![r, r, 4] : Fin 3 → ℕ) A) ^ (-c'))
      = ∫⁻ p in (matBox r r 1 ×ˢ matBox r 4 1),
          ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')) := by
    have hpre := hmpP.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding (eParamsRR4 r))
      (fun p : (Fin r → Fin r → ℝ) × (Fin r → Fin 4 → ℝ) =>
        ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')))
      (matBox r r 1 ×ˢ matBox r 4 1)
    calc ∫⁻ A in paramsBoxM (![r, r, 4] : Fin 3 → ℕ) 1,
            ENNReal.ofReal (frobSq (prod (![r, r, 4] : Fin 3 → ℕ) A) ^ (-c'))
        = ∫⁻ A in eParamsRR4 r ⁻¹' (matBox r r 1 ×ˢ matBox r 4 1),
            ENNReal.ofReal ((frobSq (rmatMul (eParamsRR4 r A).1 (eParamsRR4 r A).2)) ^ (-c')) := by
          rw [eParamsRR4_preimage_box]
          refine setLIntegral_congr_fun (measurableSet_paramsBoxM_rr4 r) (fun A _ => ?_)
          rw [frobSq_prod_eq_eParamsRR4 r A]
      _ = ∫⁻ p in (matBox r r 1 ×ˢ matBox r 4 1),
            ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c')) := hpre
  rw [hstep3]
  have hmeas : Measurable (fun p : (Fin r → Fin r → ℝ) × (Fin r → Fin 4 → ℝ) =>
      ENNReal.ofReal ((frobSq (rmatMul p.1 p.2)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  rw [Measure.volume_eq_prod (Fin r → Fin r → ℝ) (Fin r → Fin 4 → ℝ),
    setLIntegral_prod _ hmeas.aemeasurable]

/-! ## D4 — the `(r,r,4)` `hbox` discharge (gated on the carve) -/

/-- **D4 — `routeMBoxThresholdFinite_rr4_of_schurRecStep`.** GIVEN the carve `hstep : SchurRecStep 4
schurLambda`, the named gap `RouteMBoxThresholdFinite (![r,r,4])` holds — the layer-product box integral
is finite below `½·minAdm = schurLambda r` for ALL `r`. The carve-based discharge of the binding-p=4
`(r,r,4)` family, generalising the M334 anchor (`routeMBoxThresholdFinite_M334`) to all `r`. Assembly:
the threshold match `minAdm_rr4_eq` (D1) + the reshape `routeMLayerBoxIntegral_rr4_eq` (D3) to the
`SchurCore 4 r` two-matrix box, finite by `schurGen_lt_top_modulo_recStep hstep r`; `c' = 0` volume
bound. Carries `hstep` until the carve merges into this branch. -/
theorem routeMBoxThresholdFinite_rr4_of_schurRecStep
    (hstep : SchurRecStep 4 schurLambda) (r : ℕ) :
    RouteMBoxThresholdFinite (![r, r, 4] : Fin 3 → ℕ) := by
  intro c' hc'
  -- `½·minAdm (![r,r,4]) = schurLambda r`, so `c' < schurLambda r`.
  rw [minAdm_rr4_eq r] at hc'
  rw [routeMLayerBoxIntegral_rr4_eq r]
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand ^0 = 1, box volume finite.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hmatvol : ∀ p n : ℕ, (volume (matBox p n 1) : ℝ≥0∞) < ⊤ := by
      intro p n
      have hcpt : IsCompact (matBox p n 1) := by
        have heq : matBox p n 1 = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n =>
            Set.Icc (-(1 : ℝ)) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hcalc : ∫⁻ A0 in matBox r r 1, ∫⁻ A1 in matBox r 4 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
        = volume (matBox r r 1) * volume (matBox r 4 1) := by
      calc ∫⁻ A0 in matBox r r 1, ∫⁻ A1 in matBox r 4 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
          = ∫⁻ _A0 in matBox r r 1, ∫⁻ _A1 in matBox r 4 1, (1 : ℝ≥0∞) := by
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A1 _ => ?_)
            rw [hzero]; simp [Real.rpow_zero]
        _ = volume (matBox r r 1) * volume (matBox r 4 1) := by
            simp only [setLIntegral_const, one_mul]; rw [mul_comm]
    rw [hcalc]
    exact ENNReal.mul_lt_top (hmatvol r r) (hmatvol r 4)
  · -- 0 < c' < schurLambda r: the integral IS `SchurCore 4 r c' 1`, finite by the carve.
    have hsc : SchurCore 4 r (c' : ℝ) 1 :=
      schurGen_lt_top_modulo_recStep hstep r (c' : ℝ) hc0 hc' 1 one_pos
    rw [SchurCore] at hsc
    exact hsc

end DLNFibre.DLN.RLCT
