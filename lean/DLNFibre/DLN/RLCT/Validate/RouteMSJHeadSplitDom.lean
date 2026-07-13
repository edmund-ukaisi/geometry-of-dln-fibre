import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotBlowup
import DLNFibre.DLN.RLCT.Validate.RouteMSJRankRCodim
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellContain
import DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex
import DLNFibre.DLN.RLCT.Validate.RouteMSJRowSplit
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepFactor
import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplit

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom` — Brick D join: the head-split domination

**Isolated Brick D** (`s1-spine-headsplit-cert` Part A + `s1-Chle-angular-integrability-cert`): the
head-split domination with a FINITE reorganization constant. `headSplit_domination_impl` reproduces the
`headSplit_domination` stub signature VERBATIM; the controller wires the stub to it.

The frame data `(Zf, U_sf, hZfMeas, hUsMeas, hUs, hrank, hfloor, hagree)` are HYPOTHESES (Brick F provides
them). This module lands the MECHANICAL reduction (head/row split, the shell⊆good rewrite, the witnesses
`Ccrossf = 0` / `sΓf = genBox`) sorry-free, isolating the GENUINE analytic crux as the single sorry
`headSplit_pivotDom` — the coupled pivot→`decLoss` domination (dropping the `B₁₂·Q_b` cross-coupling),
commissioned as a dedicated 7th brick (design: D-A `pivotBlock_radial_blowup` + D-B
`lintegral_cube_frobSq_neg_of_finrank_range` + `s1-Chle-angular-integrability-cert`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- Column-width bridge `dropHead (redChain u M) (Fin.last L) = redChain u M (Fin.last (L+1))` (both are
`M (Fin.last (L+1+1))`, the input width). -/
theorem dropHead_last_eq_redChain_last (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    dropHead (redChain u M) (Fin.last L) = redChain u M (Fin.last (L + 1)) := by
  have h2 : redChain u M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) := by
    rw [← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]
  rw [dropHead_redChain_last, h2]

/-- **The reassembled front-factor block product** `Q = [ prod(redChain u M) z ; A_cor·Zf z ]`
(pivot rows `Q_p = prod(redChain u M) z`, corank rows `Q_b = A_cor·Zf z`), with `prod`'s columns cast to
match `Zf`'s column type `Fin (dropHead (redChain u M) (Fin.last L))`. The `Q` fed to `freedSchurLoss` on
the head-split spine. -/
noncomputable def hsQ (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M))
    (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :
    Matrix (Fin u ⊕ Fin (M 1 - u)) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ :=
  Matrix.fromRows
    ((prod (redChain u M) z).submatrix (finCongr (redChain_zero u M).symm)
      (finCongr (dropHead_last_eq_redChain_last M u)))
    (Matrix.of A_cor * Zf z)

/-- **GLUE-2 — the coupled pivot→`decLoss` domination (the analytic crux, ISOLATED as the 7th brick).**
On the `(z, A_cor)`-box, the freed Schur-loss spine integrand (pivot rows `prod(redChain u M) z`, corank
rows `A_cor·Zf z`) is dominated by a FINITE constant times the comparator-core integrand at the clean data
`k = ![1]`, `jc = ![minAdm(redChain u M) − 1]`, `Ccrossf = 0`, `sΓf = genBox`.

CONTENT (NOT a mechanical brick compose — the `B₁₂·Q_b` cross-term drop is non-pointwise): the P-radial
blow-up (D-A `pivotBlock_radial_blowup`) of `frobSq(P·Q_p + B₁₂·Q_b)` exposes `commonDivisor(v)²·frobSq
(Q_p) = decLoss` + the Jacobian monomial `r^{u·M₁−1}`; the drop to the comparator's `r^{minAdm−1}` is an
on-`[0,1]` power domination (via `hpiv`: `ρ ≤ M₁ ⟹ u·M₁ ≥ minAdm`); the absorbed P-angular/`B₁₂`-box/`C`
directions integrate to the finite `C_hle`, finite as a CONSTANT via the codim-`u·ρ` integrable singularity
(D-B `lintegral_cube_frobSq_neg_of_finrank_range`, `c'' < u·ρ/2` in-regime; det-Gram convergence via `hcvg`,
`a < m − b + 1`). Outside the operative `ab/2 < c' < carrierThreshold` regime both sides are `⊤`, so the
bound is trivial there. Design: `s1-Chle-angular-integrability-cert`. -/
theorem headSplit_pivotDom (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
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
  sorry

/-- **The head/row split equiv** `Params (tailChain M) ≃ᵐ Params (redChain u M) × corankRows` — peel the
leading tail layer (`paramsHeadSplit`), row-split it into pivot rows (`κ`'s image, → the leading layer of
`redChain u M`) and corank rows (`rowSplitEquiv κ`), reassociate, and re-glue the pivot rows onto the deep
layers as `Params (redChain u M)` (`paramsHeadSplit (redChain u M)`.symm). -/
noncomputable def hsSplit (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1)) :
    Params (tailChain M) ≃ᵐ
      Params (redChain u M) × (Fin (M 1 - u) → Fin (M 2) → ℝ) :=
  (paramsHeadSplit (tailChain M)).trans <|
    (((rowSplitEquiv κ (M 2)).prodCongr
        (MeasurableEquiv.refl (Params (dropHead (tailChain M))))).trans <|
      ((MeasurableEquiv.prodAssoc.trans
          (((MeasurableEquiv.refl (Fin u → Fin (M 2) → ℝ)).prodCongr
              MeasurableEquiv.prodComm).trans
            MeasurableEquiv.prodAssoc.symm)).trans <|
        ((paramsHeadSplit (redChain u M)).symm.prodCongr
          (MeasurableEquiv.refl (Fin (M 1 - u) → Fin (M 2) → ℝ)))))

/-- `hsSplit` is measure-preserving. -/
theorem measurePreserving_hsSplit (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1)) :
    MeasurePreserving (hsSplit M u κ) (volume : Measure (Params (tailChain M))) volume := by
  unfold hsSplit
  refine (paramsHeadSplit_mp (tailChain M)).trans ?_
  refine ((measurePreserving_rowSplitEquiv κ (M 2)).prod
    (MeasurePreserving.id (volume : Measure (Params (dropHead (tailChain M)))))).trans ?_
  refine (MeasureTheory.volume_preserving_prodAssoc.trans
    (((MeasurePreserving.id (volume : Measure (Fin u → Fin (M 2) → ℝ))).prod
        MeasureTheory.Measure.measurePreserving_swap).trans
      MeasureTheory.volume_preserving_prodAssoc.symm)).trans ?_
  exact ((paramsHeadSplit_mp (redChain u M)).symm).prod
    (MeasurePreserving.id (volume : Measure (Fin (M 1 - u) → Fin (M 2) → ℝ)))

/-- Forward action of `hsSplit` on the corank factor: the corank rows of the leading layer. -/
theorem hsSplit_snd (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1))
    (A' : Params (tailChain M)) :
    (hsSplit M u κ A').2 = fun i => A' 0 (blockSplitEquiv κ (Sum.inr i)) := rfl

/-- Forward action of `hsSplit` on the pivot layer (index `0`) of the reduced params. -/
theorem hsSplit_fst_zero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1))
    (A' : Params (tailChain M)) :
    (hsSplit M u κ A').1 0 = fun i => A' 0 (blockSplitEquiv κ (Sum.inl i)) := rfl

/-- Forward action of `hsSplit` on the deep layers (index `s.succ`): unchanged from `A'`. -/
theorem hsSplit_fst_succ (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (κ : Fin u ↪ Fin (M 1))
    (A' : Params (tailChain M)) (s : Fin L) :
    (hsSplit M u κ A').1 s.succ = A' s.succ := rfl

/-- `freedSchurLoss` reads `Q` only through its two row-blocks `Q.submatrix Sum.inl/inr id`; equal blocks
give equal loss. -/
theorem freedSchurLoss_submatrix_congr {t a b q : ℕ} (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (Q1 Q2 : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ)
    (h1 : Q1.submatrix Sum.inl id = Q2.submatrix Sum.inl id)
    (h2 : Q1.submatrix Sum.inr id = Q2.submatrix Sum.inr id) :
    freedSchurLoss x Γ Q1 = freedSchurLoss x Γ Q2 := by
  unfold freedSchurLoss
  rw [h1, h2]

/-- **The integrand identity (step 1).** For a point `(z, A_cor)` in the good set (`Zf z = Z_deep`), the
freed-loss at the reassembled `Q = Q1(hsSplit.symm (z,A_cor))` equals the freed-loss at `hsQ z A_cor`:
`Q1`'s pivot rows are `prod(redChain u M) z` and corank rows `A_cor·Z_deep = A_cor·Zf z` (via forward
action + `prod_headSplit` + `hgood`). Reads only the two row-blocks (`freedSchurLoss_submatrix_congr`). -/
theorem hsSplit_freedSchur_symm_eq {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (z : Params (redChain (t + j) M))
    (A_cor : Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ)
    (hgood : Zf z = deeperFlagZdeep M (t + j) z)
    (x : SJOuter (t + j) (M 0 - (t + j)) (M 1 - (t + j)))
    (Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ) :
    freedSchurLoss x Γ
        ((prod (tailChain M) ((hsSplit M (t + j) κ).symm (z, A_cor))).submatrix
          (blockSplitEquiv κ) id)
      = freedSchurLoss x Γ (hsQ M (t + j) Zf z A_cor) := by
  set A' := (hsSplit M (t + j) κ).symm (z, A_cor) with hA'def
  have hps : hsSplit M (t + j) κ A' = (z, A_cor) := (hsSplit M (t + j) κ).apply_symm_apply (z, A_cor)
  have hz0 : (fun i => A' 0 (blockSplitEquiv κ (Sum.inl i))) = z 0 := by
    rw [← hsSplit_fst_zero M (t + j) κ A', hps]
  have hAcor : (fun i => A' 0 (blockSplitEquiv κ (Sum.inr i))) = A_cor := by
    rw [← hsSplit_snd M (t + j) κ A', hps]
  have hsucc : ∀ s : Fin L, A' s.succ = z s.succ := by
    intro s; rw [← hsSplit_fst_succ M (t + j) κ A' s, hps]
  -- `deeperFlagZdeep M u z = prod (dropHead (tailChain M)) (A'∘succ)` (chains defeq by rfl; arg by hsucc).
  have hZd : deeperFlagZdeep M (t + j) z
      = prod (dropHead (tailChain M)) (fun (s : Fin L) => A' s.succ) := by
    have harg : (fun (s : Fin L) => (paramsHeadSplit (redChain (t + j) M) z).2 s)
        = fun (s : Fin L) => A' s.succ := by funext s; exact (hsucc s).symm
    show prod (dropHead (tailChain M)) (fun (s : Fin L) => (paramsHeadSplit (redChain (t + j) M) z).2 s)
        = prod (dropHead (tailChain M)) (fun (s : Fin L) => A' s.succ)
    rw [harg]
  -- `Zd = prod (dropHead (redChain u M)) (z∘succ)` (the pivot-block deep factor, both defeq forms).
  have hZd2 : (prod (dropHead (tailChain M)) (fun (s : Fin L) => A' s.succ))
      = prod (dropHead (redChain (t + j) M)) (fun (s : Fin L) => z s.succ) :=
    hZd.symm.trans rfl
  refine freedSchurLoss_submatrix_congr x Γ _ _ ?_ ?_
  · -- pivot: `Q1.submatrix inl id = hsQ.submatrix inl id`
    ext i col
    rw [hsQ, prod_headSplit (tailChain M) A']
    simp only [Matrix.submatrix_apply, id_eq, Matrix.fromRows_apply_inl, Matrix.submatrix_apply]
    rw [blockSplitEquiv_inl]
    show rmatMul (A' 0) (prod (dropHead (tailChain M)) (fun s => A' s.succ)) (κ i) col
        = (prod (redChain (t + j) M) z) (finCongr (redChain_zero (t + j) M).symm i)
            (finCongr (dropHead_last_eq_redChain_last M (t + j)) col)
    have hA0 : A' 0 (κ i) = z 0 i := by
      rw [← blockSplitEquiv_inl κ i]; exact congrFun hz0 i
    have hrow : finCongr (redChain_zero (t + j) M).symm i = i := Fin.ext (finCongr_apply_coe _ i)
    have hcolc : finCongr (dropHead_last_eq_redChain_last M (t + j)) col = col :=
      Fin.ext (finCongr_apply_coe _ col)
    rw [hrow, hcolc, prod_headSplit (redChain (t + j) M) z, hZd2]
    simp only [rmatMul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [congrFun hA0 k]
  · -- corank: `Q1.submatrix inr id = hsQ.submatrix inr id`
    ext i col
    rw [hsQ]
    simp only [Matrix.submatrix_apply, id_eq, Matrix.fromRows_apply_inr]
    rw [hgood, prod_headSplit (tailChain M) A']
    simp only [rmatMul, Matrix.mul_apply, Matrix.of_apply]
    rw [← hZd]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [congrFun hAcor i]

/-- `weakEigCount` is monotone in the threshold: a smaller `ε` counts no more small eigenvalues. -/
theorem weakEigCount_mono {M₂ nn : ℕ} {ε₁ ε₂ : ℝ} (h0 : 0 ≤ ε₁) (h : ε₁ ≤ ε₂)
    (Z : Matrix (Fin M₂) (Fin nn) ℝ) :
    weakEigCount ε₁ Z ≤ weakEigCount ε₂ Z := by
  unfold weakEigCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  nlinarith [hi, sq_nonneg ε₁]

/-- **The shell⊆good-set containment (step 5, D-C).** On the shell (`prod (tailChain M) A'` has `j` small
singular values) with `A'` in the entry-box, the deep factor `Z_deep = deeperFlagZdeep M u (hsSplit A').1`
has few small eigenvalues at the rescaled floor `ε' ≤ ε/√(M₁M₂)` — the good-set condition `hagree`
consumes. `deeperFlagZdeep M u (hsSplit A').1 = prod (dropHead (tailChain M)) (A'∘succ)` (forward action);
`prod (tailChain M) A' = A'₀·Z_deep` (`prod_headSplit`); then D-C `shell_subset_goodSet` +
`weakEigCount_mono` at `ε' ≤ ε/√(M₁M₂)`. -/
theorem hsSplit_good_of_shell {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (A' : Params (tailChain M))
    (hA'box : A' ∈ paramsBoxM (tailChain M) 1)
    (hA'shell : prod (tailChain M) A'
        ∈ singularShell ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩) :
    weakEigCount ε' (deeperFlagZdeep M (t + j) ((hsSplit M (t + j) κ A').1))
      ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j) := by
  set Zd := prod (dropHead (tailChain M)) (fun s => A' s.succ) with hZddef
  have hbox : ∀ i k, |A' 0 i k| ≤ 1 := by
    intro i k
    have h := hA'box 0 i k
    rw [abs_le]; exact ⟨h.1, h.2⟩
  rw [prod_headSplit (tailChain M) A'] at hA'shell
  -- `hA'shell : rmatMul (A' 0) Zd ∈ singularShell` (defeq to `(A' 0) * Zd`, D-C's form)
  have hdc := shell_subset_goodSet hε ⟨j, Nat.lt_succ_of_le hj⟩ hjr (A' 0) Zd hbox hA'shell
  -- `deeperFlagZdeep M u (hsSplit A').1` is defeq `Zd` (`hsSplit_fst_succ`, `paramsHeadSplit_snd`, both rfl;
  -- the `dropHead (redChain u M)` vs `dropHead (tailChain M)` chains are defeq).
  exact le_trans (weakEigCount_mono hε'.le hε'le Zd) hdc

/-- **Measurability of the freed-loss inner double-integral in `(z, A_cor)`** (the AEMeasurable gate for
the Tonelli split in `shellSpine_le_hsQ_box`). Per `(z, A_cor)` the inner `∫x∫Γ` collapses to a single
`B`-box integral of the CONTINUOUS chart form `frobSq(B·Q)` on `{IsUnit toBlocks₁₁}`
(`chartInner_schurShearFree_eq` + `frobSq_schur_split_inv`), whose integrand is jointly measurable in
`(p, B)` via `Zf` measurability (`hZfMeas`) and `prod`-continuity; `Measurable.lintegral_prod_right`
integrates out `B`. -/
theorem measurable_hsQ_freedLoss_integral {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ) (c' : ℝ)
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) :
    Measurable (fun p : Params (redChain (t + j) M)
        × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ) =>
      ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf p.1 p.2)) ^ (-c'))) := by
  classical
  -- per-`p` collapse of the inner double integral to a single `B`-box integral of the frobSq chart form
  have hkey : ∀ p : Params (redChain (t + j) M)
        × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ),
      (∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf p.1 p.2)) ^ (-c')))
        = ∫⁻ B in genBox (Fin (t + j) ⊕ Fin (M 0 - (t + j)))
              (Fin (t + j) ⊕ Fin (M 1 - (t + j))) 1 ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
            ENNReal.ofReal ((frobSq (Matrix.of B * hsQ M (t + j) Zf p.1 p.2)) ^ (-c')) := by
    intro p
    rw [← chartInner_schurShearFree_eq (t := t + j) (a := M 0 - (t + j)) (b := M 1 - (t + j))
      (hsQ M (t + j) Zf p.1 p.2) c' 1]
    refine setLIntegral_congr_fun
      ((measurableSet_genBox 1).inter measurableSet_isUnit_toBlocks₁₁) (fun B hB => ?_)
    rw [frobSq_schur_split_inv (Matrix.of B) hB.2 (hsQ M (t + j) Zf p.1 p.2)]
  simp only [hkey]
  -- the per-`p` entrywise measurability of the reassembled `hsQ`
  have hsQmeas : ∀ (k : Fin (t + j) ⊕ Fin (M 1 - (t + j)))
      (jj : Fin (dropHead (redChain (t + j) M) (Fin.last L))),
      Measurable (fun p : Params (redChain (t + j) M)
          × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ) =>
        hsQ M (t + j) Zf p.1 p.2 k jj) := by
    intro k jj
    rcases k with i | i
    · simp only [hsQ, Matrix.fromRows_apply_inl, Matrix.submatrix_apply]
      exact ((continuous_prod (redChain (t + j) M)).matrix_elem _ _).measurable.comp measurable_fst
    · simp only [hsQ, Matrix.fromRows_apply_inr, Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ (fun ℓ _ => (?_ : Measurable _).mul ?_)
      · exact (measurable_pi_apply ℓ).comp ((measurable_pi_apply i).comp measurable_snd)
      · exact (measurable_pi_apply jj).comp
          ((measurable_pi_apply ℓ).comp (hZfMeas.comp measurable_fst))
  -- integrate out `B`; the integrand is jointly measurable in `(p, B)`
  refine Measurable.lintegral_prod_right
    (f := fun (p : Params (redChain (t + j) M)
        × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ))
        (B : (Fin (t + j) ⊕ Fin (M 0 - (t + j))) → (Fin (t + j) ⊕ Fin (M 1 - (t + j))) → ℝ) =>
      ENNReal.ofReal ((frobSq (Matrix.of B * hsQ M (t + j) Zf p.1 p.2)) ^ (-c'))) ?_
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun r : ℝ => r ^ (-c')) (by fun_prop)
  unfold frobSq
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun jj _ => ?_))
  refine Measurable.pow_const ?_ 2
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ (fun k _ => (?_ : Measurable _).mul ?_)
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)
  · exact (hsQmeas k jj).comp measurable_fst

/-- **The mechanical head/row-split domination** (steps 1,2,5,6 — banked plumbing): the literal
shell-restricted spine integrand is dominated by the `(z, A_cor)`-box freed-loss integrand at `Q = hsQ`
(pivot rows `prod(redChain u M) z`, corank rows `A_cor·Zf z`). Route: head split (`paramsHeadSplit` +
`prod_headSplit`, MP), the shell⊆good-set rewrite `Zf z = Z_deep` on the shell (D-C `shell_subset_goodSet`
+ `hagree`), drop the shell indicator (`≥ 0`), Tonelli, row split (`rowSplit_lintegral_eq`), recombine
`(z0, A'tail) ↝ z`. NO analytic content — pure measure reorganization onto `GLUE-2`'s LHS shape. -/
theorem shellSpine_le_hsQ_box {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z)
    (hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
        weakEigCount ε' (deeperFlagZdeep M (t + j) z)
          ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)}) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ z in paramsBoxM (redChain (t + j) M) 1,
          ∫⁻ A_cor in matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1,
            ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
              ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
                  Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
                ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf z A_cor)) ^ (-c')) := by
  -- ASSEMBLY (#2, banked plumbing, route mapped): transport via `measurePreserving_hsSplit`
  -- (`setLIntegral_comp_emb`) → drop the shell to `(G ∩ Zbox) ×ˢ Abox` (`hsSplit_good_of_shell` +
  -- box, `Measure.restrict_mono`) → rewrite the integrand `Q₁ ↦ hsQ` on the good set
  -- (`hsSplit_freedSchur_symm_eq`, needs the set measurable via `hGmeas`) → drop `G`
  -- (`restrict_mono`) → Tonelli `∫_{Zbox×ˢAbox} = ∫z ∫A_cor` (`setLIntegral_prod`, whose AEMeasurability
  -- of the freed-loss product integrand is the one genuinely-new obligation, via `hZfMeas` + `P⁻¹`
  -- continuity-on-units + `prod`/`frobSq` continuity). All ingredients landed above.
  classical
  rw [shellSpineIntegrand]
  set Zbox := paramsBoxM (redChain (t + j) M) 1 with hZbox
  set Abox := matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1 with hAbox
  set Ggood : Set (Params (redChain (t + j) M)) :=
    {z | weakEigCount ε' (deeperFlagZdeep M (t + j) z)
      ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)} with hGgood
  -- the transported integrand (on the head-split codomain) and the target integrand
  set Gfun : Params (redChain (t + j) M)
        × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ) → ℝ≥0∞ :=
    fun y => ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
      ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
        ENNReal.ofReal ((freedSchurLoss x Γ
          ((prod (tailChain M) ((hsSplit M (t + j) κ).symm y)).submatrix (blockSplitEquiv κ) id))
          ^ (-c')) with hGfun
  set hfun : Params (redChain (t + j) M)
        × (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ) → ℝ≥0∞ :=
    fun p => ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
      ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
        ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf p.1 p.2)) ^ (-c')) with hhfun
  have hmeas : Measurable hfun := measurable_hsQ_freedLoss_integral M t j c' Zf hZfMeas
  have hBoxMeas : MeasurableSet ((Ggood ∩ Zbox) ×ˢ Abox) :=
    (hGmeas.inter (measurableSet_paramsBoxM (redChain (t + j) M) 1)).prod
      (matBox_measurableSet _ _ _)
  -- image containment: the box-∩-shell maps into `(Ggood ∩ Zbox) ×ˢ Abox`
  have himg : (hsSplit M (t + j) κ) ''
      (paramsBoxM (tailChain M) 1
        ∩ {A' | prod (tailChain M) A'
            ∈ singularShell ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩})
      ⊆ (Ggood ∩ Zbox) ×ˢ Abox := by
    rw [Set.image_subset_iff]
    intro A' hA'
    have hbox := hA'.1
    have hshell := hA'.2
    refine ⟨⟨hsSplit_good_of_shell M t j κ hε hj hjr hε' hε'le A' hbox hshell, ?_⟩, ?_⟩
    · intro layer i k
      rcases Fin.eq_zero_or_eq_succ layer with rfl | ⟨s', rfl⟩
      · rw [hsSplit_fst_zero]; exact hbox 0 (blockSplitEquiv κ (Sum.inl i)) k
      · rw [hsSplit_fst_succ]; exact hbox s'.succ i k
    · intro i k
      rw [hsSplit_snd]; exact hbox 0 (blockSplitEquiv κ (Sum.inr i)) k
  calc
    (∫⁻ A' in paramsBoxM (tailChain M) 1
        ∩ {A' | prod (tailChain M) A'
            ∈ singularShell ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩},
      ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ
            ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')))
        = ∫⁻ y in (hsSplit M (t + j) κ) ''
            (paramsBoxM (tailChain M) 1
              ∩ {A' | prod (tailChain M) A'
                  ∈ singularShell ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩}),
            Gfun y := by
          rw [← (measurePreserving_hsSplit M (t + j) κ).setLIntegral_comp_emb
                (hsSplit M (t + j) κ).measurableEmbedding Gfun _]
          refine lintegral_congr (fun A' => ?_)
          simp only [hGfun, MeasurableEquiv.symm_apply_apply]
      _ ≤ ∫⁻ y in (Ggood ∩ Zbox) ×ˢ Abox, Gfun y :=
          lintegral_mono' (Measure.restrict_mono himg le_rfl) le_rfl
      _ = ∫⁻ y in (Ggood ∩ Zbox) ×ˢ Abox, hfun y := by
          refine setLIntegral_congr_fun hBoxMeas (fun y hy => ?_)
          obtain ⟨z, A_cor⟩ := y
          simp only [hGfun, hhfun]
          refine lintegral_congr (fun x => ?_)
          refine lintegral_congr (fun Γ => ?_)
          exact congrArg (fun r : ℝ => ENNReal.ofReal (r ^ (-c')))
            (hsSplit_freedSchur_symm_eq M t j κ Zf z A_cor (hagree z hy.1.1) x Γ)
      _ ≤ ∫⁻ y in Zbox ×ˢ Abox, hfun y :=
          lintegral_mono'
            (Measure.restrict_mono (Set.prod_mono Set.inter_subset_right (le_refl _)) le_rfl) le_rfl
      _ = ∫⁻ z in Zbox, ∫⁻ A_cor in Abox, hfun (z, A_cor) := by
          rw [Measure.volume_eq_prod (Params (redChain (t + j) M))
                (Fin (M 1 - (t + j)) → Fin (dropHead (redChain (t + j) M) 0) → ℝ),
            setLIntegral_prod hfun hmeas.aemeasurable]

/-- **Brick D (isolated): the head-split domination with a FINITE reorganization constant.** Verbatim
signature of the `headSplit_domination` stub; the controller wires the stub to it. -/
theorem headSplit_domination_impl {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (min (M 1) (M (Fin.last (L + 1 + 1))) - j)) ℝ)
    (hZfMeas : Measurable Zf) (hUsMeas : Measurable U_sf)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, (min (M 1) (M (Fin.last (L + 1 + 1))) - j) ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z)
    (hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
        weakEigCount ε' (deeperFlagZdeep M (t + j) z)
          ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)}) :
    ∃ (Ccrossf : Params (redChain (t + j) M)
          → Matrix (Fin (M 0 - (t + j))) (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
        (sΓf : Params (redChain (t + j) M)
          → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
        (C_hle : ℝ≥0∞),
      C_hle < ⊤
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf Ccrossf sΓf c' := by
  -- witnesses: `Ccrossf = 0`, `sΓf = genBox`
  refine ⟨fun _ => 0, fun _ => genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1, ?_⟩
  -- `m ≤ M₂ = dropHead (redChain u M) 0` from `hrange`
  have hmM : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ dropHead (redChain (t + j) M) 0 := by
    rw [dropHead_redChain_zero]; exact hrange
  -- GLUE-2: the coupled pivot→decLoss domination (the isolated 7th brick)
  obtain ⟨C_hle, hfin, hle⟩ :=
    headSplit_pivotDom M (t + j) hε c' hnd hpiv (m := min (M 1) (M (Fin.last (L + 1 + 1))) - j)
      hcvg hmM hε' Zf hZfMeas U_sf hUs hrank hfloor
  refine ⟨C_hle, hfin, ?_⟩
  -- mechanical head/row split, then GLUE-2
  exact le_trans
    (shellSpine_le_hsQ_box M t j κ hε c' ht hj hjr ht1 hnd hrange hε' hε'le Zf hZfMeas hagree hGmeas)
    hle

end DLNFibre.DLN.RLCT
