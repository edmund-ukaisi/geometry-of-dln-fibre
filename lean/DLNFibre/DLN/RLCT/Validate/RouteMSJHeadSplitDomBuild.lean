import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom

set_option linter.style.longLine false

/-!
# `RouteMSJHeadSplitDomBuild` — Brick D (route α, EASY shells): corrected structured decomposition

**Thread `genm-brickd` (aoyagi-full Stage 2).** Builds `headSplit_domination` (`RouteMSJDeeperFlagCore:550`)
for the **easy interior shells** via route α, on the CORRECTED geometry satred pinned (2026-07-16) after the
draft's `pivotShell(ε)` domain was found FALSE for `j≥1` (`hsQ` shares singular values with
`prod(tailChain)A'`, so the shell-`j` mass sits OUTSIDE `pivotShell`; decorrelated-Codex-confirmed).

## Corrected geometry (vs the false draft `pivotShell`)

* **Domain** `shellCondSet` — `{A_cor | weakEigCount ε (hsQ) ≤ j}` (≤ `j` small singular values of the
  reassembled `hsQ` ⟺ `σ_{M₁−j}(hsQ) ≥ ε`), NOT `pivotShell(ε) = {weakEigCount ε (hsQ) = 0}` (false for
  `j≥1`), NOT full `matBox` (non-uniform: `t^{−2c''}` blowup at `0`). The shell-`j` support
  (`weakEigCount = j`) `⊆ {≤ j}`, so this domain ⊇ the LHS support and the conditioning `σ_{M₁−j}(hsQ) ≥ ε`
  holds UNIFORMLY on it. `hsQ` (row type `Fin u ⊕ Fin(M₁−u)`) is reindexed to `Fin(u+(M₁−u))` for
  `weakEigCount` (`finSumFinEquiv`); `measurableSet_weakEigCount_le` gives the domain measurable.
* **Threshold** `u(M₁−j)/2` (the shell conditions the top-`(M₁−j)` frame of `hsQ`), NOT the drafted `uρ/2`.
* **Easy-shell guard** `minAdm M ≤ (M₀−u)·(M₁−u) + u·(M₁−j)` (`= ab + u(M₁−j)`): the exact scope where the
  `u(M₁−j)/2` bare-constant reaches `½·minAdm M`. The `6090/76832` interior shells that FAIL it are the HARD
  shells — routed to satred's unified joint-rank-sector mechanism, NOT this leaf.

The shell↦conditioning is the LOAD-BEARING analytic step (leaf-1 is NOT "mechanical"); the crux's front
bound is uniform over the fresh per-`(z,A_cor)` top-`(M₁−j)` spectral projection `Π` of `hsQ·hsQᵀ`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-- **The good set `{z | weakEigCount ε (Z z) ≤ K}` is measurable** for a measurable matrix family `Z`.
`weakEigCount ε (Z z) = ∑ᵢ 𝟙[λᵢ(Z z · (Z z)ᴴ) < ε²]` is a measurable `ℕ`-valued function (the sorted
eigenvalues are measurable in `z` by Brick F's `measurableEigenvalues₀`), so its `Iic K` preimage is
measurable. Discharges the `hGmeas` hypothesis of the head-split domination internally. -/
theorem measurableSet_weakEigCount_le {X : Type*} [MeasurableSpace X] {M₂ n : ℕ} {ε : ℝ} (K : ℕ)
    (Z : X → Matrix (Fin M₂) (Fin n) ℝ) (hZ : Measurable Z) :
    MeasurableSet {z | weakEigCount ε (Z z) ≤ K} := by
  classical
  have hAmeas : Measurable (fun z => Z z * (Z z)ᴴ) := by
    refine measurable_matrix_iff.mpr (fun i j => ?_)
    have hEnt : (fun z => (Z z * (Z z)ᴴ) i j) = fun z => ∑ k, Z z i k * Z z j k := by
      funext z
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    rw [hEnt]
    exact Finset.measurable_sum _ (fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hZ)).mul
        ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hZ)))
  have hherm : ∀ z, (Z z * (Z z)ᴴ).IsHermitian :=
    fun z => (Matrix.posSemidef_self_mul_conjTranspose (Z z)).isHermitian
  have heig : Measurable (fun z => (hherm z).eigenvalues₀) :=
    measurableEigenvalues₀ (fun z => Z z * (Z z)ᴴ) hAmeas hherm
  have hcount : Measurable (fun z => weakEigCount ε (Z z)) := by
    have hrw : (fun z => weakEigCount ε (Z z))
        = fun z => ∑ i, (if (hherm z).eigenvalues₀ i < ε ^ 2 then (1 : ℕ) else 0) := by
      funext z
      rw [weakEigCount, Finset.card_filter]
    rw [hrw]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.ite (measurableSet_lt ?_ measurable_const) measurable_const measurable_const
    exact (measurable_pi_apply i).comp heig
  exact hcount measurableSet_Iic

variable {L : ℕ}

/-- **The reindexed reassembled block product** `hsQ` with its `Fin u ⊕ Fin(M₁−u)` rows flattened to
`Fin (u + (M₁−u))`, so `weakEigCount` (which wants `Fin M₂` rows) applies. Row-reindexing is orthogonal
conjugation, so its `weakEigCount` equals that of `hsQ`. -/
noncomputable def hsQflat (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M))
    (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :
    Matrix (Fin (u + (M 1 - u))) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ :=
  (hsQ M u Zf z A_cor).submatrix (⇑finSumFinEquiv.symm) id

/-- **The shell-conditioned domain** (replaces the false-for-`j≥1` `pivotShell`): `A_cor` with at most `j`
small singular values of the reassembled `hsQ`, i.e. `σ_{M₁−j}(hsQ) ≥ ε`. -/
def shellCondSet (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (ε : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M)) (j : ℕ) :
    Set (Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :=
  {A_cor | weakEigCount ε (hsQflat M u Zf z A_cor) ≤ j}

/-- **Leaf-1 (CORRECTED, load-bearing): the shell→conditioned-domain reduction.** The literal
shell-restricted spine integrand is dominated by the `(z, A_cor)`-box freed-loss integrand at `Q = hsQ`,
over `matBox ∩ shellCondSet` (the shell-`j` support sits inside `{weakEigCount ε (hsQ) ≤ j}`, so the RHS
domain ⊇ LHS support; integrand `≥ 0`). Route: head split (`paramsHeadSplit` + `prod_headSplit`, MP),
shell⊆good-set rewrite `Zf z = Z_deep` (`hsSplit_good_of_shell` + `hagree`), the shell membership recast to
`weakEigCount ε (hsQ) ≤ j` (`hsQ` = row-perm of `prod(tailChain)A'`, same singular values), Tonelli, row
split (`rowSplit_lintegral_eq`). The shell↦conditioning identification is the analytic content. -/
theorem shellSpine_le_condBox (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε') (hε'le : ε' ≤ ε / Real.sqrt ((M 1 : ℝ) * M 2))
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z)
    (hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
        weakEigCount ε' (deeperFlagZdeep M (t + j) z)
          ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)}) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ z in paramsBoxM (redChain (t + j) M) 1,
          ∫⁻ A_cor in matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1
              ∩ shellCondSet M (t + j) ε Zf z j,
            ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
              ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
                  Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
                ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf z A_cor)) ^ (-c')) := by
  sorry

/-- **The crux (CORRECTED, easy shells): the conditioned-domain pivot→`decLoss` domination.** On
`matBox ∩ shellCondSet` (where `σ_{M₁−j}(hsQ) ≥ ε` uniformly), the freed Schur-loss integrand is dominated
by a FINITE constant times the comparator-core integrand at `k = ![1]`, `jc = ![minAdm−1]`, `Ccrossf = 0`,
`sΓf = genBox`. Route α: P-radial blow-up (`pivotBlock_radial_blowup`) → `decLoss` + monomial `r^{uM₁−1}`;
fold `B₁₂` into the joint front `[P|B₁₂]`; the front `frobSq(X·hsQ) ≥ ε²‖X·Π‖²` for `Π` = the top-`(M₁−j)`
spectral projection of `hsQ·hsQᵀ` (rank `≥ M₁−j` on `shellCondSet`); D-B
`lintegral_cube_frobSq_neg_of_finrank_range` on `X·Π` at rank `u(M₁−j)`, UNIFORM for `2c'' < u(M₁−j)`,
`c'' = c'−ab/2`; monomial `r^{uM₁−1} → r^{minAdm−1}` via the easy-shell guard. GATED by
`hguard : minAdm M ≤ ab + u(M₁−j)` (the hard shells route to the joint-rank-sector mechanism). -/
theorem headSplit_pivotDom_easy (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hc0 : 0 ≤ c') (hnd : ∀ i, 1 ≤ M i)
    (hguard : minAdm M ≤ (M 0 - (t + j)) * (M 1 - (t + j)) + (t + j) * (M 1 - j))
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) :
    ∃ (C_hle : ℝ≥0∞), C_hle < ⊤
      ∧ (∫⁻ z in paramsBoxM (redChain (t + j) M) 1,
            ∫⁻ A_cor in matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1
                ∩ shellCondSet M (t + j) ε Zf z j,
              ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
                ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
                    Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
                  ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf z A_cor)) ^ (-c')))
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf
              (fun _ => 0) (fun _ => genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1) c' := by
  sorry

/-- **Brick D (route α, easy shells): the head-split domination.** Assembly = the corrected leaf-1
(`shellSpine_le_condBox`) ∘ the corrected crux (`headSplit_pivotDom_easy`), with `hGmeas` discharged via
`measurableSet_weakEigCount_le`. Signature = the canonical stub + `hε'le` + `hjr` (strict-both) + `hc0` +
the easy-shell guard `hguard`; `hcT`/`hUsMeas`/`U_sf`/`hUs`/`hrank`/`hfloor` carried for the stub match.
arch1build amends the stub for the EASY route + wires `headSplit_domination := this`. -/
theorem headSplit_domination_impl_easy (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hc0 : 0 ≤ c')
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hguard : minAdm M ≤ (M 0 - (t + j)) * (M 1 - (t + j)) + (t + j) * (M 1 - j))
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    (hcT : c' < carrierThreshold M)
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
        → Zf z = deeperFlagZdeep M (t + j) z) :
    ∃ (Ccrossf : Params (redChain (t + j) M)
          → Matrix (Fin (M 0 - (t + j))) (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
        (sΓf : Params (redChain (t + j) M)
          → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
        (C_hle : ℝ≥0∞),
      C_hle < ⊤
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf Ccrossf sΓf c' := by
  have hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
      weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)} := by
    have hproj : Measurable (fun z : Params (redChain (t + j) M) =>
        (paramsHeadSplit (redChain (t + j) M) z).2) :=
      measurable_snd.comp (paramsHeadSplit (redChain (t + j) M)).measurable
    have hZdeepMeas : Measurable (deeperFlagZdeep M (t + j)) :=
      measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun jj =>
        ((continuous_prod (dropHead (redChain (t + j) M))).matrix_elem i jj).measurable.comp hproj))
    exact measurableSet_weakEigCount_le _ (deeperFlagZdeep M (t + j)) hZdeepMeas
  obtain ⟨C_hle, hfin, hcrux⟩ :=
    headSplit_pivotDom_easy M t j hε c' hc0 hnd hguard hε' Zf hZfMeas
  exact ⟨fun _ => 0, fun _ => genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1, C_hle, hfin,
    le_trans (shellSpine_le_condBox M t j κ hε c' ht hj hjr ht1 hnd hrange hε' hε'le Zf hagree hGmeas)
      hcrux⟩

end DLNFibre.DLN.RLCT
