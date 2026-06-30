import DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverHfin

/-!
# `RouteMSchurRect` — the RECTANGULAR Schur recursion SPEC (the general-`(M0,M1,M2)` UPPER leg)

SPEC-FIRST scaffold for the asymmetric (`M0 ≠ M1`) generalisation of the banked square Schur recursion
(`RouteMSchurGeneral.SchurCore`/`core_schurGen_lt_top`). The square family `(![r,r,p])` is a genuine
SUBFAMILY — its `cover_le` UPPER leg is CLOSED (`RouteMLayerCoverLeRRP.routeMLayerCover_coverLe_rrp`),
riding `routeMBoxThresholdFinite_rrp` whose `SchurCore p r` is hardcoded to a SQUARE `Δ : matBox r r`.
General `L=2` chains `(M0,M1,M2)` (and the DLN deepest-core widths `M_s = H_s − r` are generically
UNEQUAL) need the RECTANGULAR core `Δ : matBox M0 M1` with the asymmetric threshold strata
`(M0−t)(M1−t) + t·M2` — a genuinely larger threshold than the square `(r−t)²` one
(`minAdm(2,3,4) = 6 ≠ 4 = minAdm(2,2,4)`, `#eval`-verified). This is BOUNDED work (a rectangular
generalisation of the SAME machinery — no new wall), DISTINCT from the L≥3 multi-matrix-product wall.

## The SPEC's shape (mirrors `RouteMSchurGeneral` faithfully)

DETERMINED / SORRY-FREE here (the scaffold + the value side):
- `RectSchurCore m n p c' T` — the asymmetric box-finiteness predicate (`Δ : matBox m n`, `S : matBox n p`).
- `RectSchurThreshold` / `RectSchurLowerIH` / `RectSchurRecStep` — the asymmetric contract, joint-core IH,
  and the deferred per-step (the `min(m,n)`-measured analog of `SchurThreshold`/…/`SchurRecStep`).
- `rectCore_schurGen_lt_top` — the WellFounded-on-`min(m,n)` wrapper (the determined part; PROVED).
- `minAdm_mnp_eq_inf` + `minAdm_mnp_le_mul` + `minAdm_mnp_subadd` — the asymmetric threshold arithmetic.
- `rectSchurLambda` + `rectSchurLambda_satisfies_threshold` — the threshold witness `½·minAdm(![m,n,p])`
  satisfies the contract (the value side, PROVED — the contract is inhabited in-Lean).
- `eParamsMNP` + `routeMLayerBoxIntegral_mnp_eq` — the general-`(m,n,p)` layer reshape (PROVED, MP plumbing).

DEFERRED (the single analytic `sorry`, the dedicated deep-fill tide — NOT this SPEC):
- `rectSchurRecStep_stub` — the per-step analytic content: the radial-`Δ` cover (`mn`-chart blow-up,
  Jacobian `|a|^{mn−1}`) + the rectangular minor-pivot Schur split (N2b at a `t×t` invertible pivot of the
  RECTANGULAR `Δ`, residual Schur complement `Sc : (m−t)×(n−t)`) + the `M22 ↦ Sc` translation-domination
  (O2 cert, adjudicated sound for general corank) + the shifted-exponent Morse peel, recursing on the JOINT
  lower core. The rectangular analog of `schurRecStep4_stub`; the HIGH-risk long pole.

GATED on the stub (the deliverable shape, typechecking — these CLOSE once `rectSchurRecStep_stub` lands):
- `routeMBoxThresholdFinite_mnp` — the general-`(M0,M1,M2)` `hbox` (the analog of `routeMBoxThresholdFinite_rrp`).
- `routeMLayerCover_coverLe_mnp` — the general-`(M0,M1,M2)` `cover_le` UPPER leg (the analog of
  `routeMLayerCover_coverLe_rrp`), composing `routeMLayerCover_hfin` ∘ `routeMBoxThresholdFinite_mnp`.

## Validation

The asymmetric anchor `(2,3,4)` (`minAdm = 6`, threshold `3`, `M0 ≠ M1`) and the square reduction-check
`minAdm(2,3,4) = 6 ≠ 4 = minAdm(2,2,4)` are `#eval`-pinned (the square SchurCore does NOT reach the larger
asymmetric threshold). The wrapper + threshold witness reuse the square-case proof patterns verbatim
(`minAdm_rrp_eq_inf`/`minAdm_rrp_subadd`/`core_schurGen_lt_top`), confirming the asymmetric scaffold is a
faithful generalisation, not a new design.

## S2-hygiene

The scaffold + threshold + reshape are S2-FREE. The deferred `rectSchurRecStep_stub` is the analytic
content (Morse leaves / a-divisor / Tonelli / Schur splits) — S2-FREE when proven, as in the square case.
`monomial_rlct` enters only the `hfin` leaf-sum side (via `routeMLayerCover_hfin`), the same S2 use the
headline already rides. No new axiom.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The asymmetric corank finiteness predicate -/

/-- **The rectangular Schur core finiteness predicate.** `RectSchurCore m n p c' T` asserts the free-box
core integral `∫_{Δ∈matBox m n T} ∫_{S∈matBox n p T} frobSq(Δ·S)^{−c'}` is finite, with `Δ : m×n`
RECTANGULAR (the asymmetric generalisation of `SchurCore p r`, which is the `m = n = r` square case). -/
def RectSchurCore (m n p : ℕ) (c' T : ℝ) : Prop :=
  (∫⁻ Δ in matBox m n T, ∫⁻ S in matBox n p T,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))) < ⊤

/-- The square case `m = n = r` IS the banked `SchurCore p r` (the load-bearing shape-pin). -/
theorem rectSchurCore_square (p r : ℕ) (c' T : ℝ) :
    RectSchurCore r r p c' T ↔ SchurCore p r c' T := Iff.rfl

/-! ## The asymmetric threshold contract -/

/-- **The rectangular corank-recursion threshold contract.** `lam : ℕ → ℕ → ℝ` is a `RectSchurThreshold`
when it satisfies the asymmetric inequalities the wrapper consumes:
* `lambda0_left`/`lambda0_right` — a corank-0 leaf (`m = 0` OR `n = 0`) carries no binding threshold;
* `radial_le` — the radial-divisor cap `lam m n ≤ (m·n)/2` (the `mn`-dim blow-up Jacobian, generalising
  `r²/2`);
* `peel_le` — the additive peel bound `lam m n ≤ jp/2 + lam (m−j) (n−j)` for `1 ≤ j ≤ m, n` (the top
  `jp`-dim Morse block contributes `jp/2`, the rectangular lower core `lam (m−j) (n−j)`). -/
structure RectSchurThreshold (p : ℕ) (lam : ℕ → ℕ → ℝ) : Prop where
  lambda0_left : ∀ {n : ℕ}, lam 0 n = 0
  lambda0_right : ∀ {m : ℕ}, lam m 0 = 0
  radial_le : ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → lam m n ≤ ((m : ℝ) * (n : ℝ)) / 2
  peel_le : ∀ {m n j : ℕ}, 1 ≤ j → j ≤ m → j ≤ n →
    lam m n ≤ ((j : ℝ) * (p : ℝ)) / 2 + lam (m - j) (n - j)

/-- **The rectangular joint-core IH.** At dims `(m,n)`, after the `j`-block peel the residual is the JOINT
free-box rectangular `(m−j)×(n−j)` core at the SHIFTED exponent `c'' = c' − jp/2`. The asymmetric analog of
`SchurLowerIH` (the cert's `(W,V,Sc)` carrier, `Sc : (m−j)×(n−j)` rectangular). -/
def RectSchurLowerIH (p : ℕ) (lam : ℕ → ℕ → ℝ) (m n : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ m → j ≤ n →
    ∀ c'' : ℝ, 0 < c'' → c'' < lam (m - j) (n - j) →
      ∀ T'' : ℝ, 0 < T'' → RectSchurCore (m - j) (n - j) p c'' T''

/-- **The deferred per-step (the contract, NOT proved here).** Given the threshold contract and the
lower-dim IH, the `(m,n)` core is finite below `lam m n`. The genuine analytic content: the radial-`Δ`
cover (`mn`-chart blow-up) + the RECTANGULAR minor-pivot Schur split (pivot `t×t` minor of `Δ : m×n`,
residual `Sc : (m−t)×(n−t)`) + the `M22 ↦ Sc` translation-domination (O2 cert) + shifted Morse peel +
recursion on the joint lower core. The wrapper takes it as a HYPOTHESIS — scaffold sorry-free, content
named. The asymmetric analog of `SchurRecStep`. -/
def RectSchurRecStep (p : ℕ) (lam : ℕ → ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, RectSchurThreshold p lam → RectSchurLowerIH p lam m n →
    ∀ c' : ℝ, 0 < c' → c' < lam m n →
      ∀ T : ℝ, 0 < T → RectSchurCore m n p c' T

/-! ## The WellFounded-on-`min(m,n)` wrapper (the determined part — PROVED, sorry-free) -/

/-- **The ∀-`(m,n)` rectangular finiteness, GIVEN the per-step `recStep`.** Strong induction on the
measure `k = min(m,n)` (the peel drops `(m,n) → (m−j, n−j)` with `j ≥ 1`, so `min(m−j,n−j) < min(m,n)`).
No analytic content lives here — the per-step work is the `hstep` hypothesis, deferred. The asymmetric
analog of `core_schurGen_lt_top`; axiom-clean (`hstep` a hypothesis). -/
theorem rectCore_schurGen_lt_top
    (p : ℕ) (lam : ℕ → ℕ → ℝ)
    (hlam : RectSchurThreshold p lam)
    (hstep : RectSchurRecStep p lam) :
    ∀ m n : ℕ, ∀ c' : ℝ, 0 < c' → c' < lam m n →
      ∀ T : ℝ, 0 < T → RectSchurCore m n p c' T := by
  suffices H : ∀ k : ℕ, ∀ m n : ℕ, min m n = k → ∀ c' : ℝ, 0 < c' → c' < lam m n →
      ∀ T : ℝ, 0 < T → RectSchurCore m n p c' T by
    intro m n; exact H (min m n) m n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m n hk c' hc0 hclt T hT
    refine hstep m n hlam ?_ c' hc0 hclt T hT
    intro j hj0 hjm hjn c'' hc0' hclam T'' hT''
    exact ih (min (m - j) (n - j)) (by omega) (m - j) (n - j) rfl c'' hc0' hclam T'' hT''

/-! ## The asymmetric threshold arithmetic (PROVED, the value side) -/

/-- **`minAdm(![m,n,p]) = inf'_{t≤min(m,n)}[(m−t)(n−t) + t·p]`** (the general 3-width layer-peel, the
asymmetric analog of `minAdm_rrp_eq_inf` without the `M0=M1` collapse). -/
theorem minAdm_mnp_eq_inf (m n p : ℕ) :
    minAdm (![m, n, p] : Fin 3 → ℕ)
      = (Finset.range (min m n + 1)).inf' (by simp) (fun t => (m - t) * (n - t) + t * p) := by
  rw [← minAdmRec_eq_minAdm, minAdmRec_succ_succ]
  have hbody : ∀ t : ℕ, ((![m, n, p] : Fin 3 → ℕ) 0 - t) * ((![m, n, p] : Fin 3 → ℕ) 1 - t)
      + minAdmRec (redChain t (![m, n, p] : Fin 3 → ℕ)) = (m - t) * (n - t) + t * p := fun t => by
    rw [show minAdmRec (redChain t (![m, n, p] : Fin 3 → ℕ)) = t * p by
      rw [minAdmRec_leaf]; simp [redChain]]
    rfl
  refine le_antisymm
    (Finset.le_inf' _ _ (fun t ht => Finset.inf'_le_of_le _ ht (le_of_eq (hbody t))))
    (Finset.le_inf' _ _ (fun t ht => Finset.inf'_le_of_le _ ht (le_of_eq (hbody t).symm)))

/-- **The radial cap `minAdm(![m,n,p]) ≤ m·n`** (the `t = 0` stratum `(m−0)(n−0) + 0·p = m·n`). -/
theorem minAdm_mnp_le_mul (m n p : ℕ) : minAdm (![m, n, p] : Fin 3 → ℕ) ≤ m * n := by
  rw [minAdm_mnp_eq_inf]
  refine le_trans (Finset.inf'_le _ (by simp : (0 : ℕ) ∈ Finset.range (min m n + 1))) ?_
  simp

/-- **The codim subadditivity `minAdm(![m,n,p]) ≤ jp + minAdm(![m−j,n−j,p])`** (`j ≤ m, n`), via the
stratum-lift `t' ↦ t'+j`. The asymmetric analog of `minAdm_rrp_subadd`. -/
theorem minAdm_mnp_subadd (p : ℕ) {m n j : ℕ} (hjm : j ≤ m) (hjn : j ≤ n) :
    minAdm (![m, n, p] : Fin 3 → ℕ) ≤ j * p + minAdm (![m - j, n - j, p] : Fin 3 → ℕ) := by
  rw [minAdm_mnp_eq_inf, minAdm_mnp_eq_inf]
  obtain ⟨t', ht'mem, ht'eq⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.range (min (m - j) (n - j) + 1)) (H := by simp)
    (f := fun t => (m - j - t) * (n - j - t) + t * p)
  rw [ht'eq]
  have ht'le : t' ≤ min (m - j) (n - j) := by rw [Finset.mem_range] at ht'mem; omega
  have hmem : t' + j ∈ Finset.range (min m n + 1) := by rw [Finset.mem_range]; omega
  refine le_trans (Finset.inf'_le _ hmem) ?_
  have hexp : (m - (t' + j)) * (n - (t' + j)) + (t' + j) * p
      = j * p + ((m - j - t') * (n - j - t') + t' * p) := by
    have e1 : m - (t' + j) = m - j - t' := by omega
    have e2 : n - (t' + j) = n - j - t' := by omega
    rw [e1, e2]; ring
  rw [hexp]

/-! ## The threshold WITNESS (the contract is inhabited in-Lean — PROVED) -/

/-- **The rectangular threshold `rectSchurLambda p m n := ½·minAdm(![m,n,p])`** — the depth-2 general
`(m,n,p)` geometric threshold. The asymmetric analog of `schurLambdaP`. -/
noncomputable def rectSchurLambda (p m n : ℕ) : ℝ := (minAdm (![m, n, p] : Fin 3 → ℕ) : ℝ) / 2

/-- **`rectSchurLambda p` satisfies `RectSchurThreshold p`** (the contract is inhabited — the value side,
PROVED). `lambda0` from `minAdm_mnp_eq_inf` (`m=0` or `n=0` ⟹ the `t=0` stratum is `0`); `radial_le` from
`minAdm_mnp_le_mul`; `peel_le` from `minAdm_mnp_subadd`. -/
theorem rectSchurLambda_satisfies_threshold (p : ℕ) :
    RectSchurThreshold p (rectSchurLambda p) where
  lambda0_left := by
    intro n; rw [rectSchurLambda]
    rw [show minAdm (![0, n, p] : Fin 3 → ℕ) = 0 by rw [minAdm_mnp_eq_inf]; simp]
    simp
  lambda0_right := by
    intro m; rw [rectSchurLambda]
    rw [show minAdm (![m, 0, p] : Fin 3 → ℕ) = 0 by
      rw [minAdm_mnp_eq_inf]
      refine le_antisymm ?_ (Nat.zero_le _)
      refine le_trans (Finset.inf'_le _ (by simp : (0 : ℕ) ∈ Finset.range (min m 0 + 1))) ?_
      simp]
    simp
  radial_le := by
    intro m n _ _
    rw [rectSchurLambda]
    have h := minAdm_mnp_le_mul m n p
    have : ((minAdm (![m, n, p] : Fin 3 → ℕ) : ℝ)) ≤ (m : ℝ) * (n : ℝ) := by
      rw [show (m : ℝ) * (n : ℝ) = ((m * n : ℕ) : ℝ) by push_cast; ring]
      exact_mod_cast h
    linarith
  peel_le := by
    intro m n j _ hjm hjn
    rw [rectSchurLambda, rectSchurLambda]
    have h := minAdm_mnp_subadd p hjm hjn
    have hR : ((minAdm (![m, n, p] : Fin 3 → ℕ) : ℝ))
        ≤ (j : ℝ) * (p : ℝ) + ((minAdm (![m - j, n - j, p] : Fin 3 → ℕ) : ℝ)) := by
      rw [show (j : ℝ) * (p : ℝ) = ((j * p : ℕ) : ℝ) by push_cast; ring]
      exact_mod_cast h
    linarith

/-! ## The general-`(m,n,p)` layer reshape (PROVED, MP plumbing) -/

/-- The `Fin 1` tail family after peeling layer `0` of `(![m,n,p])` (the `n×p` layer-`1` fiber). -/
abbrev TailFamMNP (m n p : ℕ) : Fin 1 → Type :=
  fun s : Fin 1 => Fin ((![m, n, p] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).castSucc) →
    Fin ((![m, n, p] : Fin 3 → ℕ) ((0 : Fin 2).succAbove s).succ) → ℝ

/-- **The `Params (![m,n,p])` split into the two layer matrix boxes `(A0 : m×n, A1 : n×p)`.** Peel layer
`0` then collapse the singleton tail — an MP reshape, the width-agnostic generalisation of `eParamsRRP`. -/
noncomputable def eParamsMNP (m n p : ℕ) :
    Params (![m, n, p] : Fin 3 → ℕ) ≃ᵐ (Fin m → Fin n → ℝ) × (Fin n → Fin p → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun s : Fin 2 => Fin ((![m, n, p] : Fin 3 → ℕ) s.castSucc) →
        Fin ((![m, n, p] : Fin 3 → ℕ) s.succ) → ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piUnique (TailFamMNP m n p)))

theorem measurePreserving_eParamsMNP (m n p : ℕ) :
    MeasurePreserving (eParamsMNP m n p)
      (volume : Measure (Params (![m, n, p] : Fin 3 → ℕ))) volume := by
  unfold eParamsMNP
  refine (volume_preserving_piFinSuccAbove _ 0).trans ?_
  have hp := (MeasurePreserving.id (volume : Measure (Fin m → Fin n → ℝ))).prod
    (volume_preserving_piUnique (TailFamMNP m n p))
  rw [show (volume : Measure ((Fin m → Fin n → ℝ) × (Fin n → Fin p → ℝ)))
    = volume.prod volume from rfl]
  exact hp

/-- `eParamsMNP m n p ⁻¹' (matBox m n 1 ×ˢ matBox n p 1) = paramsBoxM (![m,n,p]) 1`. -/
theorem eParamsMNP_preimage_box (m n p : ℕ) :
    eParamsMNP m n p ⁻¹' (matBox m n 1 ×ˢ matBox n p 1)
      = paramsBoxM (![m, n, p] : Fin 3 → ℕ) 1 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBoxM, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1⟩ s i j; fin_cases s
    · exact h0 i j
    · exact h1 i j
  · intro h; exact ⟨fun i j => h 0 i j, fun i j => h 1 i j⟩

/-- **Generic `L=2` layer-product entry form** `(prod (![m,n,p]) A) i j = ∑ₖ A₀ᵢₖ·A₁ₖⱼ` (the local
`prodAux` cast closer, width-agnostic generalisation of `prod_two_layer_rrp`). -/
theorem prod_two_layer_mnp (m n p : ℕ) (A : Params (![m, n, p] : Fin 3 → ℕ))
    (i : Fin ((![m, n, p] : Fin 3 → ℕ) 0)) (j : Fin ((![m, n, p] : Fin 3 → ℕ) 2)) :
    prod (![m, n, p] : Fin 3 → ℕ) A i j
      = ∑ k : Fin ((![m, n, p] : Fin 3 → ℕ) 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

/-- The integrand identity `frobSq (prod (![m,n,p]) A) = frobSq (rmatMul A0 A1)` (the `eParamsMNP`
decode, generalising `frobSq_prod_eq_eParamsRRP`). -/
theorem frobSq_prod_eq_eParamsMNP (m n p : ℕ) (A : Params (![m, n, p] : Fin 3 → ℕ)) :
    frobSq (prod (![m, n, p] : Fin 3 → ℕ) A)
      = frobSq (rmatMul (eParamsMNP m n p A).1 (eParamsMNP m n p A).2) := by
  change frobSq (prod (![m, n, p] : Fin 3 → ℕ) A) = frobSq (rmatMul (A 0) (A 1))
  unfold frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show prod (![m, n, p] : Fin 3 → ℕ) A i j
      = rmatMul (fun i k => A 0 i k) (fun k j => A 1 k j) i j from by
    rw [prod_two_layer_mnp m n p A i j]; rfl]

/-- **The reshape identity** `routeMLayerBoxIntegral (![m,n,p]) c' 1 = ∫_{A0∈matBox m n 1}∫_{A1∈matBox n p
1} frobSq(A0·A1)^{−c'}` (the width-agnostic generalisation of `routeMLayerBoxIntegral_rrp_eq`). -/
theorem routeMLayerBoxIntegral_mnp_eq (m n p : ℕ) (c' : ℝ) :
    routeMLayerBoxIntegral (![m, n, p] : Fin 3 → ℕ) c' 1
      = ∫⁻ A0 in matBox m n 1, ∫⁻ A1 in matBox n p 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-c')) := by
  rw [routeMLayerBoxIntegral]
  have hmpP := measurePreserving_eParamsMNP m n p
  have hstep3 : ∫⁻ A in paramsBoxM (![m, n, p] : Fin 3 → ℕ) 1,
        ENNReal.ofReal (frobSq (prod (![m, n, p] : Fin 3 → ℕ) A) ^ (-c'))
      = ∫⁻ q in (matBox m n 1 ×ˢ matBox n p 1),
          ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c')) := by
    have hpre := hmpP.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding (eParamsMNP m n p))
      (fun q : (Fin m → Fin n → ℝ) × (Fin n → Fin p → ℝ) =>
        ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c')))
      (matBox m n 1 ×ˢ matBox n p 1)
    calc ∫⁻ A in paramsBoxM (![m, n, p] : Fin 3 → ℕ) 1,
            ENNReal.ofReal (frobSq (prod (![m, n, p] : Fin 3 → ℕ) A) ^ (-c'))
        = ∫⁻ A in eParamsMNP m n p ⁻¹' (matBox m n 1 ×ˢ matBox n p 1),
            ENNReal.ofReal ((frobSq (rmatMul (eParamsMNP m n p A).1 (eParamsMNP m n p A).2)) ^ (-c')) := by
          rw [eParamsMNP_preimage_box]
          refine setLIntegral_congr_fun (measurableSet_paramsBoxM (![m, n, p] : Fin 3 → ℕ) 1)
            (fun A _ => ?_)
          rw [frobSq_prod_eq_eParamsMNP m n p A]
      _ = ∫⁻ q in (matBox m n 1 ×ˢ matBox n p 1),
            ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c')) := hpre
  rw [hstep3]
  have hmeas : Measurable (fun q : (Fin m → Fin n → ℝ) × (Fin n → Fin p → ℝ) =>
      ENNReal.ofReal ((frobSq (rmatMul q.1 q.2)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  rw [Measure.volume_eq_prod (Fin m → Fin n → ℝ) (Fin n → Fin p → ℝ),
    setLIntegral_prod _ hmeas.aemeasurable]

/-! ## The single DEFERRED analytic stub (the dedicated deep-fill tide — marked `sorry`) -/

/-- **STUB — the deferred rectangular per-step (the genuine analytic wall).** `RectSchurRecStep p
(rectSchurLambda p)` — the SOLE remaining input to the general-`(m,n,p)` finiteness. The asymmetric analog
of `schurRecStep_p`: the radial-`Δ` (`mn`-chart) blow-up cover + the RECTANGULAR minor-pivot Schur split
(pivot `t×t` minor of `Δ : m×n`, residual `Sc : (m−t)×(n−t)`) + the `M22 ↦ Sc` translation-domination (O2
cert, sound for general corank) + shifted-exponent Morse peel + recursion on the JOINT lower core
(`rectCore_schurGen_lt_top` via the IH). Marked `sorry` ON PURPOSE; the dedicated deep-fill tide replaces
it — that closes the general-`(M0,M1,M2)` UPPER leg. (HIGH-risk long pole; the square `schurRecStep_p` is
the proven template — the rectangular generalisation tracks `(m−t)(n−t)` strata, NOT square `(r−t)²`.) -/
theorem rectSchurRecStep_stub (p : ℕ) : RectSchurRecStep p (rectSchurLambda p) := by
  sorry

/-! ## The GATED deliverable shape (CLOSES once `rectSchurRecStep_stub` lands) -/

/-- **The general-`(M0,M1,M2)` `hbox` (GATED on the stub).** `RouteMBoxThresholdFinite (![m,n,p])` for ALL
`m, n, p` — the asymmetric analog of `routeMBoxThresholdFinite_rrp`. Assembly: the threshold match
(`rectSchurLambda p m n = ½·minAdm`, `rfl`) + the reshape (`routeMLayerBoxIntegral_mnp_eq`) to the
rectangular two-matrix box, finite by `rectCore_schurGen_lt_top p (rectSchurLambda p)
(rectSchurLambda_satisfies_threshold p) (rectSchurRecStep_stub p)`; the `c' = 0` branch is the box-volume
bound. Currently rides the `sorry` stub; CLEAN once the stub lands. -/
theorem routeMBoxThresholdFinite_mnp (m n p : ℕ) :
    RouteMBoxThresholdFinite (![m, n, p] : Fin 3 → ℕ) := by
  intro c' hc'
  rw [routeMLayerBoxIntegral_mnp_eq m n p]
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand ^0 = 1, box volume finite.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hmatvol : ∀ a b : ℕ, (volume (matBox a b 1) : ℝ≥0∞) < ⊤ := by
      intro a b
      have hcpt : IsCompact (matBox a b (1 : ℝ)) := by
        have heq : matBox a b (1 : ℝ)
            = Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => Set.Icc (-(1 : ℝ)) 1)) := by
          ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
        rw [heq]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      exact hcpt.measure_lt_top
    have hcalc : ∫⁻ A0 in matBox m n 1, ∫⁻ A1 in matBox n p 1,
          ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
        = volume (matBox m n 1) * volume (matBox n p 1) := by
      calc ∫⁻ A0 in matBox m n 1, ∫⁻ A1 in matBox n p 1,
              ENNReal.ofReal ((frobSq (rmatMul A0 A1)) ^ (-(c' : ℝ)))
          = ∫⁻ _A0 in matBox m n 1, ∫⁻ _A1 in matBox n p 1, (1 : ℝ≥0∞) := by
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
            refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A1 _ => ?_)
            rw [hzero]; simp [Real.rpow_zero]
        _ = volume (matBox m n 1) * volume (matBox n p 1) := by
            simp only [setLIntegral_const, one_mul]; rw [mul_comm]
    rw [hcalc]
    exact ENNReal.mul_lt_top (hmatvol m n) (hmatvol n p)
  · -- 0 < c' < ½·minAdm = rectSchurLambda p m n: the rectangular core finiteness.
    have hlt : (c' : ℝ) < rectSchurLambda p m n := by rw [rectSchurLambda]; exact hc'
    have hrc : RectSchurCore m n p (c' : ℝ) 1 :=
      rectCore_schurGen_lt_top p (rectSchurLambda p) (rectSchurLambda_satisfies_threshold p)
        (rectSchurRecStep_stub p) m n (c' : ℝ) hc0 hlt 1 one_pos
    rw [RectSchurCore] at hrc
    exact hrc

/-- **The general-`(M0,M1,M2)` `cover_le` UPPER leg (GATED on the stub).** The `IsRouteMCover.cover_le`
field for `(![m,n,p])` (`1 ≤ minAdm`), the asymmetric analog of `routeMLayerCover_coverLe_rrp`: compose
`routeMLayerCover_hfin` (whose `hbox` is `routeMBoxThresholdFinite_mnp`) + the banked RHS positivity
`layerCover_rhs_ne_zero`, via `routeM_coverLe_of_finiteness`. CLEAN once `rectSchurRecStep_stub` lands —
this is the general-`L=2` UPPER deliverable. -/
theorem routeMLayerCover_coverLe_mnp (m n p : ℕ) (hpos : 1 ≤ minAdm (![m, n, p] : Fin 3 → ℕ)) :
    ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in routeMBaseNbhd (![m, n, p] : Fin 3 → ℕ),
          ENNReal.ofReal (|routeMCore (![m, n, p] : Fin 3 → ℕ) x| ^ (-(c' : ℝ)))
        ≤ C * ∑ i : (routeLayerAtlas (![m, n, p] : Fin 3 → ℕ)).ι,
            ∫⁻ y in unitBox (layerD (![m, n, p] : Fin 3 → ℕ) i),
              ENNReal.ofReal (monomialIntegrand (layerD (![m, n, p] : Fin 3 → ℕ) i)
                (layerK (![m, n, p] : Fin 3 → ℕ) i)
                (layerH (![m, n, p] : Fin 3 → ℕ) i) (c' : ℝ) y) :=
  routeM_coverLe_of_finiteness (routeMCore (![m, n, p] : Fin 3 → ℕ))
    (routeMBaseNbhd (![m, n, p] : Fin 3 → ℕ))
    (layerD (![m, n, p] : Fin 3 → ℕ)) (layerK (![m, n, p] : Fin 3 → ℕ))
    (layerH (![m, n, p] : Fin 3 → ℕ))
    (layerCover_rhs_ne_zero (![m, n, p] : Fin 3 → ℕ))
    (routeMLayerCover_hfin (![m, n, p] : Fin 3 → ℕ) hpos (routeMBoxThresholdFinite_mnp m n p))

end DLNFibre.DLN.RLCT
