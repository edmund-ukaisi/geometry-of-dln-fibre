import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotDom` — GLUE-2: the coupled pivot→`decLoss` domination

**Thread `genm-sj5` (aoyagi-full Stage 2), the analytic CRUX of the head-split (GLUE-2).**
`headSplit_pivotDom_impl` reproduces the `RouteMSJHeadSplitDom.headSplit_pivotDom` stub signature
VERBATIM (referencing the imported `hsQ`); the controller wires the stub to it.

## Architecture (locked with the controller, 2026-07-13): finiteness / ratio

The RHS is EXISTENTIAL in `C_hle`, and `C_hle` may depend on everything held fixed (`M, u, c', Zf, …`) —
just not on the integration variables. So `∃ C_hle < ⊤, LHS ≤ C_hle · RHS` is a **finiteness
comparison**, not a tight domination:
* `RHS = ⊤` → `C_hle := 1` (trivial);
* `RHS < ⊤` (and `RHS ≠ 0`) → `C_hle := LHS / RHS` works iff `LHS < ⊤` (`ENNReal.div_mul_cancel`).

So the genuine content is `pivotDom_finiteness : RHS < ⊤ → LHS < ⊤`, isolated as the ONE crux sorry.

**Soundness note (verified numerically, 2026-07-13).** The finiteness `LHS < ⊤` genuinely needs the
freed-loss's CORANK term kept: dropping it (`freedSchurLoss ≥ pivot`) over-estimates `LHS` to `⊤` in the
regime `c' ∈ (u·ρ/2, (minAdm(M)/2))` — the pure-pivot `∫_W frobSq(W·Q̂)^(-c')` has D-B threshold `u·ρ/2`,
but the true `LHS` (and `RHS`) converge to `minAdm(M)/2 = minAdm(redChain u M)/2 + ab/2`, because the
corank's `ab/2` shift (S3) regularizes the pivot's zero-locus (witness `(3,3,3)`, `u=2`: pure-pivot
threshold `3`, true threshold `3.5`; `hpiv` gives only `u·ρ/2 ≥ minAdm(redChain u M)/2`, short by exactly
the `ab/2`). Hence `pivotDom_finiteness` keeps the corank and follows the cert mechanism: D-A P-radial
blow-up of the pivot → `commonDivisor²·frobSq(Q_p) = decLoss` after the angular/`B₁₂` integration (the
non-pointwise cross-term drop) → S3 (`shell_corankOffSector_le_unif`) on the corank, det-Gram convergence
via `hcvg`. It is commissioned as a dedicated tide (design: `s1-Chle-angular-integrability-cert`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The GLUE-2 LHS integral** — the freed Schur-loss spine integrand at `Q = hsQ` (pivot rows
`prod(redChain u M) z`, corank rows `A_cor·Zf z`), integrated over `(z, A_cor, x=(P,B₁₂,C), Γ)`. This is
the exact left-hand side of `RouteMSJHeadSplitDom.headSplit_pivotDom`. -/
noncomputable def pivotDomLHS (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paramsBoxM (redChain u M) 1,
    ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1,
      ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c'))

/-- **The GLUE-2 RHS integrand** — `deeperFlagCoreIntegrand` at the clean comparator data `k = ![1]`,
`jc = ![minAdm(redChain u M) − 1]`, `Ccrossf = 0`, `sΓf = genBox`. Abbreviation for readability. -/
noncomputable def pivotDomRHS (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) : ℝ≥0∞ :=
  deeperFlagCoreIntegrand M u (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) Zf
    (fun _ => 0) (fun _ => genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1) c'

/-- **The GLUE-2 finiteness (the genuine analytic content — the ISOLATED CRUX).** Whenever the
comparator-core RHS is finite, the freed Schur-loss spine LHS is finite. Mechanism (cert
`s1-Chle-angular-integrability-cert` + `s1-spine-headsplit-cert` §A): keeping the corank (load-bearing —
see the soundness note in the module header), the D-A P-radial blow-up of the pivot block `W = (P|B₁₂)`
factors the pivot energy to `commonDivisor(v)²·frobSq(Q_p) = decLoss` after the angular/`B₁₂` integration
(the non-pointwise cross-term drop), and S3 (`shell_corankOffSector_le_unif`) integrates the corank with
the `ab/2` shift; finiteness is the codim-`u·ρ` singularity (D-B
`lintegral_cube_frobSq_neg_of_finrank_range`) with the det-Gram outer convergence (`hcvg`, `a < m − b + 1`),
threshold-covered by `hpiv`. Commissioned as a dedicated fresh tide. -/
theorem pivotDom_finiteness (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
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
    pivotDomLHS M u c' Zf < ⊤ := by
  sorry

/-! ### Elementary helpers for the RHS-nonvanishing (`pivotDom_RHS_ne_zero`) -/

/-- Frobenius submultiplicativity `frobSq (A·B) ≤ frobSq A · frobSq B` (per-entry Cauchy–Schwarz). -/
private theorem frobSq_submul {p n q : ℕ} (A : Matrix (Fin p) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin q) ℝ) : frobSq (A * B) ≤ frobSq A * frobSq B := by
  have hCS : ∀ i j, ((A * B) i j) ^ 2 ≤ (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => A i k) (fun k => B k j)
  calc frobSq (A * B) = ∑ i, ∑ j, ((A * B) i j) ^ 2 := rfl
    _ ≤ ∑ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hCS i j))
    _ = ∑ i, (∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.mul_sum]
    _ = (∑ i, ∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by rw [Finset.sum_mul]
    _ = frobSq A * frobSq B := by rw [frobSq, frobSq]; congr 1; exact Finset.sum_comm

/-- `matBox p n 1` has positive volume. -/
private theorem matBox_volume_pos (p n : ℕ) : 0 < volume (matBox p n 1) := by
  have heq : matBox p n 1
      = Set.univ.pi (fun _ : Fin p => Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
    ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [heq, volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _; rw [volume_pi_pi, Finset.prod_ne_zero_iff]; intro j _; rw [Real.volume_Icc]; simp

/-- `genBox (Fin a) (Fin b) 1` has positive volume. -/
private theorem genBox_volume_pos (a b : ℕ) : 0 < volume (genBox (Fin a) (Fin b) 1) := by
  have heq : genBox (Fin a) (Fin b) 1
      = Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => Set.Icc (-1 : ℝ) 1)) := by
    ext X; simp only [genBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [heq, volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _; rw [volume_pi_pi, Finset.prod_ne_zero_iff]; intro j _; rw [Real.volume_Icc]; simp

/-- `unitBox 1` has volume `1`. -/
private theorem unitBox_one_volume : volume (unitBox 1) = 1 := by
  rw [unitBox, volume_pi_pi]; simp [Real.volume_Icc]

/-- On `0 < a ≤ x ≤ b`, the rpow value at `x` dominates the smaller endpoint value. -/
private theorem rpow_min_endpoint_le {a x b e : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    min (a ^ e) (b ^ e) ≤ x ^ e := by
  rcases le_total 0 e with he | he
  · exact le_trans (min_le_left _ _) (Real.rpow_le_rpow ha.le hax he)
  · have hxpos : 0 < x := lt_of_lt_of_le ha hax
    exact le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_nonpos hxpos hxb he)

/-- `frobSq` of a `matBox`-radius-1 matrix is at most the entry count. -/
private theorem frobSq_matBox_le {p n : ℕ} {X : Fin p → Fin n → ℝ} (hX : X ∈ matBox p n 1) :
    frobSq X ≤ (p : ℝ) * n := by
  rw [frobSq]
  calc ∑ i, ∑ j, (X i j) ^ 2 ≤ ∑ _i : Fin p, ∑ _j : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        have h := hX i j; rw [Set.mem_Icc] at h; nlinarith [h.1, h.2]
    _ = (p : ℝ) * n := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `frobSq` of a `genBox`-radius-1 matrix is at most the entry count. -/
private theorem frobSq_genBox_le {a b : ℕ} {X : Fin a → Fin b → ℝ}
    (hX : X ∈ genBox (Fin a) (Fin b) 1) : frobSq X ≤ (a : ℝ) * b := by
  rw [frobSq]
  calc ∑ i, ∑ j, (X i j) ^ 2 ≤ ∑ _i : Fin a, ∑ _j : Fin b, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        have h := hX i j; rw [Set.mem_Icc] at h; nlinarith [h.1, h.2]
    _ = (a : ℝ) * b := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Closed form of the comparator's decorated loss at the clean data (`u ≥ 1`, `ι` nonempty):
`decLoss v z = |v 0|² · frobSq (prod (redChain u M) z)`. -/
private theorem cornerComparator_decLoss_closed (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : 1 ≤ u) (hnd : ∀ i, 1 ≤ M i) (z : Params (redChain u M)) (v : Fin 1 → ℝ) :
    (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).decLoss v z
      = |v 0| ^ 2 * frobSq (prod (redChain u M) z) := by
  have hu1 : 0 < redChain u M 0 := by rw [redChain_zero]; omega
  have hlastw : redChain u M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) := by
    rw [← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]
  have hlast1 : 0 < redChain u M (Fin.last (L + 1)) := by rw [hlastw]; exact hnd _
  set i₀ : Fin (redChain u M 0) × Fin (redChain u M (Fin.last (L + 1)))
      := (⟨0, hu1⟩, ⟨0, hlast1⟩) with hi₀
  letI := (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).fι
  letI := (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).fν
  haveI : Nonempty (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).ι := ⟨i₀⟩
  rw [cornerComparator_decLoss (redChain u M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) i₀ v z]
  have hcd : commonDivisor (cornerComparator (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ)).carrier.supp v = |v 0| := by
    rw [commonDivisor, cornerComparator_sharedDivisorExp (redChain u M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) i₀]
    simp only [Matrix.cons_val_fin_one, pow_one]
    exact Fin.prod_univ_one fun x => |v x|
  rw [hcd]

/-- A nonneg measurable integrand that is a.e. positive on a positive-measure set has nonzero
integral. -/
private theorem setLIntegral_ne_zero_of_ae_pos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (hf : Measurable f) (hμs : μ s ≠ 0)
    (hpos : ∀ᵐ x ∂μ, x ∈ s → 0 < f x) : ∫⁻ x in s, f x ∂μ ≠ 0 := by
  intro hzeroInt
  rw [setLIntegral_eq_zero_iff hs hf] at hzeroInt
  have hae : ∀ᵐ x ∂μ, x ∉ s := by
    filter_upwards [hzeroInt, hpos] with x hx0 hxp
    intro hxs; exact (hxp hxs).ne' (hx0 hxs)
  exact hμs (by simpa using ae_iff.mp hae)

/-- `paramsBoxM M' 1` has positive volume (measure-preserving pullback of the flat cube box). -/
private theorem paramsBoxM_volume_pos {L' : ℕ} (M' : Fin (L' + 1) → ℕ) :
    0 < volume (paramsBoxM M' 1) := by
  have hcubeMeas : MeasurableSet (cubeBox (flatDim M') 1) := by
    rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hvol : volume (paramsBoxM M' 1) = volume (cubeBox (flatDim M') 1) := by
    rw [← paramsEquivFlat_preimage_paramsBoxM M' 1]
    exact (measurePreserving_paramsEquivFlat M').measure_preimage hcubeMeas.nullMeasurableSet
  rw [hvol, cubeBox, volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _; rw [Real.volume_Icc]; simp

/-- **The simple minorant integrand** for `pivotDom_RHS_ne_zero`: the reduced-comparator monomial
`∏|v_ℓ|^{jc_ℓ}` times the min-endpoint rpow bound of the pivot energy, times the fixed box volume `Vol`.
It lower-bounds the RHS integrand once the `(A_cor, Γ)`-integrals are collapsed to `Vol`. -/
private noncomputable def pivotSsimp (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' Dconst : ℝ)
    (Vol : ℝ≥0∞) (jc : Fin 1 → ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M)) (v : Fin 1 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
    * (ENNReal.ofReal (min ((|v 0| ^ 2 * frobSq (prod (redChain u M) z)) ^ (-c'))
        ((|v 0| ^ 2 * frobSq (prod (redChain u M) z) + Dconst * frobSq (Zf z)) ^ (-c'))) * Vol)

/-- Joint measurability of the simple minorant integrand. -/
private theorem pivotSsimp_measurable (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' Dconst : ℝ)
    (Vol : ℝ≥0∞) (jc : Fin 1 → ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) :
    Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) => pivotSsimp M u c' Dconst Vol jc Zf p.1 p.2) := by
  haveI hopens : OpensMeasurableSpace (Params (redChain u M)) :=
    inferInstanceAs (OpensMeasurableSpace
      (∀ s : Fin (L + 1), Fin (redChain u M s.castSucc) → Fin (redChain u M s.succ) → ℝ))
  have hw : Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) =>
      frobSq (prod (redChain u M) p.1)) := by
    have hfc : Continuous (fun M' : Matrix (Fin (redChain u M 0))
        (Fin (redChain u M (Fin.last (L + 1)))) ℝ => frobSq M') := by unfold frobSq; fun_prop
    exact (hfc.comp (continuous_prod (redChain u M))).measurable.comp measurable_fst
  have hZf : Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) => frobSq (Zf p.1)) := by
    unfold frobSq
    apply Finset.measurable_sum; intro i _
    apply Finset.measurable_sum; intro j _
    exact (((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (hZfMeas.comp measurable_fst)))).pow_const 2
  have hv0 : Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) => |p.2 0|) :=
    ((measurable_pi_apply 0).comp measurable_snd).abs
  have hdecL : Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) =>
      |p.2 0| ^ 2 * frobSq (prod (redChain u M) p.1)) := (hv0.pow_const 2).mul hw
  have hmono : Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) =>
      ENNReal.ofReal (∏ ℓ, |p.2 ℓ| ^ (jc ℓ))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Finset.measurable_prod; intro ℓ _
    exact (((measurable_pi_apply ℓ).comp measurable_snd).abs).pow_const (jc ℓ)
  have hminpart : Measurable (fun p : Params (redChain u M) × (Fin 1 → ℝ) =>
      ENNReal.ofReal (min ((|p.2 0| ^ 2 * frobSq (prod (redChain u M) p.1)) ^ (-c'))
        ((|p.2 0| ^ 2 * frobSq (prod (redChain u M) p.1)
            + Dconst * frobSq (Zf p.1)) ^ (-c')))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.min
    · exact (Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop) hdecL)
    · exact (Measurable.comp (g := fun t : ℝ => t ^ (-c'))
        (by fun_prop) (hdecL.add (measurable_const.mul hZf)))
  exact hmono.mul (hminpart.mul measurable_const)

/-- **The GLUE-2 RHS is nonzero (in the operative `u ≥ 1` cut).** `decLoss =
commonDivisor(v)²·frobSq(prod(redChain u M) z)` is `> 0` a.e. on `paramsBoxM × unitBox` (the deep-tail
product is a nonzero polynomial ⟹ null zero set; `v 0 ≠ 0` a.e.), so the RHS integrand `|v 0|^{minAdm-1}·
∫∫(decLoss + …)^(-c')` is positive on a positive-measure set. Uses the banked
`deeperFlagCore_decLoss_pos_ae` (at `t = u`, `j = 0`). -/
theorem pivotDom_RHS_ne_zero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : 1 ≤ u) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) :
    pivotDomRHS M u c' Zf ≠ 0 := by
  classical
  set Dconst : ℝ := ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ)
    * (((M 1 - u : ℕ) : ℝ) * ((dropHead (redChain u M) 0 : ℕ) : ℝ)) with hDconstdef
  set Vol : ℝ≥0∞ := volume (genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1)
    * volume (matBox (M 1 - u) (dropHead (redChain u M) 0) 1) with hVoldef
  set jc : Fin 1 → ℕ := ![minAdm (redChain u M) - 1] with hjcdef
  -- the a.e. positivity of the comparator loss, in closed form (aligned to `redChain u M`)
  have hae : ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
      ∀ᵐ v ∂(volume.restrict (unitBox 1)),
        0 < |v 0| ^ 2 * frobSq (prod (redChain u M) z) := by
    have h := deeperFlagCore_decLoss_pos_ae M u 0 hu hnd
    simp only [Nat.add_zero] at h
    filter_upwards [h] with z hz
    filter_upwards [hz] with v hv
    rw [← cornerComparator_decLoss_closed M u hu hnd z v]; exact hv
  -- the pivotSsimp lower-bound integral is positive
  have hVolpos : Vol ≠ 0 :=
    mul_ne_zero (genBox_volume_pos _ _).ne' (matBox_volume_pos _ _).ne'
  have hSmeas := pivotSsimp_measurable M u c' Dconst Vol jc Zf hZfMeas
  -- pointwise positivity of pivotSsimp from `decL > 0`
  have hSpos : ∀ z v, 0 < |v 0| ^ 2 * frobSq (prod (redChain u M) z) →
      0 < pivotSsimp M u c' Dconst Vol jc Zf z v := by
    intro z v hdecL
    rw [pivotSsimp, pos_iff_ne_zero]
    have hv0 : 0 < |v 0| := by
      rcases (abs_nonneg (v 0)).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hdecL; simp at hdecL
    have hmono : 0 < ∏ ℓ, |v ℓ| ^ (jc ℓ) :=
      Finset.prod_pos (fun ℓ _ => by rw [Subsingleton.elim ℓ 0]; exact pow_pos hv0 _)
    have hfrobZ : 0 ≤ Dconst * frobSq (Zf z) :=
      mul_nonneg (by rw [hDconstdef]; positivity) (frobSq_nonneg _)
    have hmin : 0 < min ((|v 0| ^ 2 * frobSq (prod (redChain u M) z)) ^ (-c'))
        ((|v 0| ^ 2 * frobSq (prod (redChain u M) z) + Dconst * frobSq (Zf z)) ^ (-c')) :=
      lt_min (Real.rpow_pos_of_pos hdecL _) (Real.rpow_pos_of_pos (by linarith) _)
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hmono).ne'
      (mul_ne_zero (ENNReal.ofReal_pos.mpr hmin).ne' hVolpos)
  -- LB ≠ 0
  have hLB : (∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox 1,
      pivotSsimp M u c' Dconst Vol jc Zf z v) ≠ 0 := by
    have hhmeas : Measurable (fun z => ∫⁻ v in unitBox 1, pivotSsimp M u c' Dconst Vol jc Zf z v) :=
      hSmeas.lintegral_prod_right
    refine setLIntegral_ne_zero_of_ae_pos (measurableSet_paramsBoxM (redChain u M) 1) hhmeas
      (paramsBoxM_volume_pos (redChain u M)).ne' ?_
    rw [← ae_restrict_iff' (measurableSet_paramsBoxM (redChain u M) 1)]
    filter_upwards [hae] with z hz
    have hUBmeas : MeasurableSet (unitBox 1) :=
      MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have hsec : Measurable (fun v => pivotSsimp M u c' Dconst Vol jc Zf z v) :=
      hSmeas.of_uncurry_left
    refine pos_iff_ne_zero.mpr ?_
    refine setLIntegral_ne_zero_of_ae_pos hUBmeas hsec
      (by rw [unitBox_one_volume]; exact one_ne_zero) ?_
    rw [← ae_restrict_iff' hUBmeas]
    filter_upwards [hz] with v hv
    exact hSpos z v hv
  -- LB ≤ RHS, so RHS > 0
  refine (?_ : 0 < pivotDomRHS M u c' Zf).ne'
  rw [pivotDomRHS, deeperFlagCoreIntegrand]
  refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hLB) ?_
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with z hzv
  refine lintegral_mono_ae ?_
  filter_upwards [hzv] with v hv
  rw [pivotSsimp]
  refine mul_le_mul_left' ?_ _
  -- ofReal(min) * Vol ≤ Inner
  have hconst : (∫⁻ _A in matBox (M 1 - u) (dropHead (redChain u M) 0) 1,
        ∫⁻ _Γ in genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1,
        ENNReal.ofReal (min ((|v 0| ^ 2 * frobSq (prod (redChain u M) z)) ^ (-c'))
          ((|v 0| ^ 2 * frobSq (prod (redChain u M) z) + Dconst * frobSq (Zf z)) ^ (-c'))))
      = ENNReal.ofReal (min ((|v 0| ^ 2 * frobSq (prod (redChain u M) z)) ^ (-c'))
          ((|v 0| ^ 2 * frobSq (prod (redChain u M) z) + Dconst * frobSq (Zf z)) ^ (-c'))) * Vol := by
    simp_rw [setLIntegral_const]
    rw [hVoldef]; ring
  rw [← hconst]
  refine setLIntegral_mono_ae' (matBox_measurableSet (M 1 - u) (dropHead (redChain u M) 0) 1)
    (ae_of_all _ (fun A_cor hA => ?_))
  refine setLIntegral_mono_ae' (measurableSet_genBox 1) (ae_of_all _ (fun Γ hΓ => ?_))
  -- pointwise: ofReal(min) ≤ ofReal((decLoss + frobSq(0 + Γ·A·Zf z))^(-c'))
  rw [cornerComparator_decLoss_closed M u hu hnd z v, zero_add]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbub : frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z)) ≤ Dconst * frobSq (Zf z) := by
    calc frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z))
          ≤ frobSq (Matrix.of Γ) * frobSq (Matrix.of A_cor * Zf z) := frobSq_submul _ _
      _ ≤ frobSq (Matrix.of Γ) * (frobSq (Matrix.of A_cor) * frobSq (Zf z)) :=
          mul_le_mul_of_nonneg_left (frobSq_submul _ _) (frobSq_nonneg _)
      _ ≤ (((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ))
            * (((M 1 - u : ℕ) : ℝ) * ((dropHead (redChain u M) 0 : ℕ) : ℝ) * frobSq (Zf z)) := by
          refine mul_le_mul (frobSq_genBox_le hΓ) ?_ ?_ ?_
          · exact mul_le_mul_of_nonneg_right (frobSq_matBox_le hA) (frobSq_nonneg _)
          · exact mul_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
          · positivity
      _ = Dconst * frobSq (Zf z) := by rw [hDconstdef]; ring
  refine rpow_min_endpoint_le hv (by nlinarith [frobSq_nonneg (Matrix.of Γ * (Matrix.of A_cor * Zf z))]) ?_
  linarith [hbub]

/-! ### Elementary helpers for the degenerate `u = 0` edge (`pivotDom_uzero`) -/

/-- At `u = 0` the comparator's active index `ι = Fin 0 × …` is empty, so its decorated loss vanishes. -/
private theorem pivotUzero_decLoss_zero (M : Fin (L + 1 + 1 + 1) → ℕ) (v : Fin 1 → ℝ)
    (z : Params (redChain 0 M)) :
    (cornerComparator (redChain 0 M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ)).decLoss v z = 0 := by
  haveI : IsEmpty (cornerComparator (redChain 0 M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ)).ι := by
    show IsEmpty (Fin (redChain 0 M 0) × Fin (redChain 0 M (Fin.last (L + 1))))
    rw [redChain_zero]; infer_instance
  letI := (cornerComparator (redChain 0 M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ)).fι
  letI := (cornerComparator (redChain 0 M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ)).fν
  unfold SJDecoration.decLoss SJLinGenState.loss
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- At `t = 0` the block shift `schurShift` (with a `Fin 0`-inner product) vanishes. -/
private theorem pivotUzero_schurShift_zero {a b : ℕ} (x : SJOuter 0 a b) : schurShift x = 0 := by
  funext i j
  simp only [schurShift, Pi.zero_apply]
  rw [Matrix.mul_apply]; simp

/-- At `t = 0` the freed Schur loss keeps only the corank energy (pivot rows are `Fin 0`). -/
private theorem pivotUzero_freedSchurLoss {a b q : ℕ} (x : SJOuter 0 a b) (Γ : Fin a → Fin b → ℝ)
    (Q : Matrix (Fin 0 ⊕ Fin b) (Fin q) ℝ) :
    freedSchurLoss x Γ Q = frobSq (Matrix.of Γ * Q.submatrix Sum.inr id) := by
  unfold freedSchurLoss
  have h1 : frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
      + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)) = 0 := by simp [frobSq]
  have h2 : Matrix.of x.2 * (Q.submatrix Sum.inl id
      + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id) = 0 := by
    ext i j; rw [Matrix.mul_apply]; simp
  rw [h1, h2, zero_add, zero_add]

/-- The `(P, B₁₂, C)` outer domain at `t = 0` is the whole (single-point) space. -/
private theorem pivotUzero_outerDom_univ (a b : ℕ) : outerDom 0 a b 1 = Set.univ := by
  ext x
  simp only [outerDom, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i j => Fin.elim0 j, ?_⟩
  have : Matrix.of x.1.1 = 1 := Subsingleton.elim _ _
  rw [this]; exact isUnit_one

/-- The `t = 0` outer domain has volume `1` (a probability-space singleton). -/
private theorem pivotUzero_outerDom_volume (a b : ℕ) : volume (outerDom 0 a b 1) = 1 := by
  rw [pivotUzero_outerDom_univ]
  haveI hp0 : IsProbabilityMeasure (volume : Measure (Fin 0 → ℝ)) :=
    ⟨by rw [volume_pi]; exact Measure.pi_empty_univ _⟩
  haveI : IsProbabilityMeasure (volume : Measure (Fin 0 → Fin 0 → ℝ)) :=
    ⟨by rw [volume_pi]; exact Measure.pi_empty_univ _⟩
  haveI : IsProbabilityMeasure (volume : Measure (Fin 0 → Fin b → ℝ)) :=
    ⟨by rw [volume_pi]; exact Measure.pi_empty_univ _⟩
  haveI : IsProbabilityMeasure (volume : Measure (Fin a → Fin 0 → ℝ)) := by infer_instance
  haveI : IsProbabilityMeasure (volume : Measure (SJOuter 0 a b)) := by
    unfold SJOuter; infer_instance
  exact measure_univ

/-- `hsQ`'s bottom (`Sum.inr`) block is the corank rows `A_cor · Zf z`. -/
private theorem hsQ_submatrix_inr (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M)) (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :
    (hsQ M u Zf z A_cor).submatrix Sum.inr id = Matrix.of A_cor * Zf z := by
  ext i j
  rw [hsQ]; simp [Matrix.submatrix_apply, Matrix.fromRows_apply_inr]

/-- **The degenerate `u = 0` edge.** With a `0`-width pivot the front block vanishes
(`freedSchurLoss = frobSq(Γ·Q_b)`, the `(P,B₁₂,C)`-integral is over a singleton), and `hpiv` forces
`minAdm(redChain 0 M) = 0` so the RHS Jacobian monomial is `|v 0|^0 = 1`; a Tonelli factorisation of the
`v`-integral gives `LHS = RHS`. NOT the analytic crux (no pivot energy). -/
theorem pivotDom_uzero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu0 : u = 0) (c' : ℝ)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) :
    pivotDomLHS M u c' Zf ≤ pivotDomRHS M u c' Zf := by
  subst hu0
  have hpiv0 : minAdm (redChain 0 M) = 0 := by
    have : minAdm (redChain 0 M) ≤ 0 := by simpa using hpiv
    omega
  apply le_of_eq
  rw [pivotDomLHS, pivotDomRHS, deeperFlagCoreIntegrand]
  refine lintegral_congr (fun z => ?_)
  -- the common inner integral (corank energy only)
  refine Eq.trans ?_ (?_ : (∫⁻ A_cor in matBox (M 1 - 0) (dropHead (redChain 0 M) 0) 1,
      ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
        ENNReal.ofReal ((frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c'))) = _)
  · -- LHS side = common
    refine lintegral_congr (fun A_cor => ?_)
    have hx : ∀ x : SJOuter 0 (M 0 - 0) (M 1 - 0),
        (∫⁻ Γ in {Γ : Fin (M 0 - 0) → Fin (M 1 - 0) → ℝ
            | Γ + schurShift x ∈ genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M 0 Zf z A_cor)) ^ (-c')))
        = ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
            ENNReal.ofReal ((frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c')) := by
      intro x
      have hset : {Γ : Fin (M 0 - 0) → Fin (M 1 - 0) → ℝ
          | Γ + schurShift x ∈ genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1}
          = genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1 := by
        rw [pivotUzero_schurShift_zero x]; ext Γ; simp
      rw [hset]
      refine lintegral_congr (fun Γ => ?_)
      rw [pivotUzero_freedSchurLoss x Γ (hsQ M 0 Zf z A_cor), hsQ_submatrix_inr]
    rw [setLIntegral_congr_fun (measurableSet_outerDom 0 (M 0 - 0) (M 1 - 0) 1)
      (fun x _ => hx x), setLIntegral_const, pivotUzero_outerDom_volume, mul_one]
  · -- common = RHS side
    symm
    have hpt : ∀ v : Fin 1 → ℝ,
        ENNReal.ofReal (∏ ℓ, |v ℓ| ^ ((![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ) ℓ))
          * (∫⁻ A_cor in matBox (M 1 - 0) (dropHead (redChain 0 M) 0) 1,
              ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
                ENNReal.ofReal
                  (((cornerComparator (redChain 0 M) (![1] : Fin 1 → ℕ)
                      (![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ)).decLoss v z
                      + frobSq ((fun _ => 0) z + Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c')))
          = ∫⁻ A_cor in matBox (M 1 - 0) (dropHead (redChain 0 M) 0) 1,
              ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
                ENNReal.ofReal ((frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c')) := by
      intro v
      have hmono1 : ENNReal.ofReal (∏ ℓ, |v ℓ| ^ ((![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ) ℓ))
          = 1 := by simp [hpiv0, Fin.prod_univ_one]
      rw [hmono1, one_mul]
      refine lintegral_congr (fun A_cor => ?_)
      refine lintegral_congr (fun Γ => ?_)
      rw [pivotUzero_decLoss_zero M v z, zero_add]
      exact congrArg (fun m => ENNReal.ofReal (frobSq m ^ (-c')))
        (zero_add (Matrix.of Γ * (Matrix.of A_cor * Zf z)))
    calc (∫⁻ v in unitBox 1,
            ENNReal.ofReal (∏ ℓ, |v ℓ| ^ ((![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ) ℓ))
              * (∫⁻ A_cor in matBox (M 1 - 0) (dropHead (redChain 0 M) 0) 1,
                  ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
                    ENNReal.ofReal
                      (((cornerComparator (redChain 0 M) (![1] : Fin 1 → ℕ)
                          (![minAdm (redChain 0 M) - 1] : Fin 1 → ℕ)).decLoss v z
                          + frobSq ((fun _ => 0) z
                              + Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c'))))
        = ∫⁻ _v in unitBox 1, ∫⁻ A_cor in matBox (M 1 - 0) (dropHead (redChain 0 M) 0) 1,
            ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
              ENNReal.ofReal ((frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c')) :=
          lintegral_congr (fun v => hpt v)
      _ = (∫⁻ A_cor in matBox (M 1 - 0) (dropHead (redChain 0 M) 0) 1,
            ∫⁻ Γ in genBox (Fin (M 0 - 0)) (Fin (M 1 - 0)) 1,
              ENNReal.ofReal ((frobSq (Matrix.of Γ * (Matrix.of A_cor * Zf z))) ^ (-c')))
            * volume (unitBox 1) := setLIntegral_const _ _
      _ = _ := by rw [unitBox_one_volume, mul_one]

/-- **GLUE-2 — the coupled pivot→`decLoss` domination (the analytic crux).** Verbatim statement of the
`RouteMSJHeadSplitDom.headSplit_pivotDom` stub; the controller wires the stub to it. Ratio wiring:
`RHS = ⊤ → C_hle := 1`; else `C_hle := LHS/RHS` (finite by `pivotDom_finiteness`, nonzero denominator by
`pivotDom_RHS_ne_zero`), closing via `ENNReal.div_mul_cancel`; the degenerate `u = 0` cut via
`pivotDom_uzero`. -/
theorem headSplit_pivotDom_impl (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
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
    ∃ (C_hle : ℝ≥0∞), C_hle < ⊤
      ∧ (∫⁻ z in paramsBoxM (redChain u M) 1,
            ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1,
              ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
                ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
                    Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
                  ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c')))
          ≤ C_hle * deeperFlagCoreIntegrand M u (![1] : Fin 1 → ℕ)
              (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) Zf
              (fun _ => 0) (fun _ => genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1) c' := by
  -- fold LHS/RHS to the named abbreviations (defeq)
  change ∃ (C_hle : ℝ≥0∞), C_hle < ⊤ ∧ pivotDomLHS M u c' Zf ≤ C_hle * pivotDomRHS M u c' Zf
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · -- degenerate `u = 0`: `LHS ≤ RHS`, `C_hle := 1`
    exact ⟨1, ENNReal.one_lt_top,
      by rw [one_mul]; exact pivotDom_uzero M u hu0 c' hpiv Zf⟩
  · -- `u ≥ 1`: ratio trick
    by_cases htop : pivotDomRHS M u c' Zf = ⊤
    · exact ⟨1, ENNReal.one_lt_top, by rw [one_mul, htop]; exact le_top⟩
    · have hRlt : pivotDomRHS M u c' Zf < ⊤ := lt_top_iff_ne_top.mpr htop
      have hne : pivotDomRHS M u c' Zf ≠ 0 := pivotDom_RHS_ne_zero M u hupos c' hnd Zf hZfMeas
      have hfin : pivotDomLHS M u c' Zf < ⊤ :=
        pivotDom_finiteness M u hε c' hnd hpiv hcvg hmM hε' Zf hZfMeas U_sf hUs hrank hfloor hRlt
      exact ⟨pivotDomLHS M u c' Zf / pivotDomRHS M u c' Zf,
        ENNReal.div_lt_top hfin.ne hne,
        by rw [ENNReal.div_mul_cancel hne htop]⟩

end DLNFibre.DLN.RLCT
