import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom

set_option linter.style.longLine false

/-!
# `RouteMSJHeadSplitDomBuild` — Brick D: signature reconciliation (`hGmeas` discharged) + wiring landing pad

**Thread `genm-brickd` (aoyagi-full Stage 2).** Builds toward `headSplit_domination`
(`RouteMSJDeeperFlagCore:550`, the single remaining `(□)` sorry of the interior deeper-cut descent) via the
DRAFT route confirmed sound by satred (`brickD-sublemmas` correction, 2026-07-16): the **hpiv-gated
codim-u·ρ** route (D-B `lintegral_cube_frobSq_neg_of_finrank_range` applied at the SHIFTED `c'' = c'−ab/2`,
the corank `ab/2` extracted first by the strong-block), `pivotShell` conditioning, `Ccrossf = 0`,
`sΓf = genBox`. satred's gammaAtom two-arm route (`corner_C_shift_disposal`/`_gammaAtom`) is the documented
FALLBACK if `headSplit_pivotDom` proves intractable.

## What this module delivers (green)

* **`measurableSet_weakEigCount_le`** (reusable) — the good-set `{z | weakEigCount ε (Z z) ≤ K}` is
  measurable for a measurable matrix family `Z`. Route: `weakEigCount ε (Z z) = ∑ᵢ 𝟙[λᵢ(Z z Z zᴴ) < ε²]`
  is a measurable `ℕ`-valued function (sorted eigenvalues measurable via Brick F's `measurableEigenvalues₀`),
  so its `Iic K`-preimage is measurable. Discharges the draft impl's `hGmeas` HYPOTHESIS internally.
* **`headSplit_domination_impl_amended`** — the reconciled signature (matching the canonical stub +
  controller-sanctioned `hε'le`, and the guard/regime hypotheses the draft route genuinely needs — see
  FINDINGS), proven from the draft's `headSplit_domination_impl` with `hGmeas` discharged. Assembly PROVEN;
  the two tracked leaf sorries are `shellSpine_le_hsQ_box` + `headSplit_pivotDom` (in `RouteMSJHeadSplitDom`).

## FINDINGS for the stub amendment (arch1build) — the draft route needs MORE than `a≥1`

* **`hε'le : ε' ≤ ε/√(M₁M₂)`** — controller-sanctioned; holds by `rfl` at the `deeperFlag_spineToCore` site.
* **`hjr : (j:ℕ) < min (M₀−t) (M₁−t)` (STRICT, both a≥1 AND b≥1)** — NOT merely `a≥1`. `shell_subset_goodSet`
  (the shell⊆good containment, step 5) requires `j < min(M₀−t, M₁−t)`. `a≥1` alone leaves the `b=0` top shell
  (`M₁<M₀`, `j=M₁−t`) uncovered. Where the `b=0` top shell routes (waist? distinct?) is an OPEN scope
  question for satred/the assembly owner (companion to `a=0 → deeperFlag_waist`).
* **`hc0 : 0 ≤ c'`** — the D-B integrability lemma `lintegral_cube_frobSq_neg_of_finrank_range` genuinely
  requires `0 ≤ c'`; NOT cleanly discharged internally (the `c'<0` regime is not obviously trivial). Flagged.
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

/-- **Brick D (draft route), reconciled signature.** The head-split domination with a FINITE reorganization
constant, proven from the draft's `headSplit_domination_impl` with `hGmeas` discharged via
`measurableSet_weakEigCount_le`. Signature matches the canonical stub + `hε'le` + the guard/regime
hypotheses the draft route needs (`hjr` strict-both, `hc0`); `hcT` carried for the stub match (unused here).
Assembly PROVEN; the tracked leaves are `shellSpine_le_hsQ_box` + `headSplit_pivotDom`. -/
theorem headSplit_domination_impl_amended {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hc0 : 0 ≤ c')
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hjr : (j : ℕ) < min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
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
  -- The good set is measurable (discharge the draft impl's `hGmeas`), via the deep-factor measurability.
  have hproj : Measurable (fun z : Params (redChain (t + j) M) =>
      (paramsHeadSplit (redChain (t + j) M) z).2) :=
    measurable_snd.comp (paramsHeadSplit (redChain (t + j) M)).measurable
  have hZdeepMeas : Measurable (deeperFlagZdeep M (t + j)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun jj =>
      ((continuous_prod (dropHead (redChain (t + j) M))).matrix_elem i jj).measurable.comp hproj))
  have hGmeas : MeasurableSet {z : Params (redChain (t + j) M) |
      weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)} :=
    measurableSet_weakEigCount_le _ (deeperFlagZdeep M (t + j)) hZdeepMeas
  exact headSplit_domination_impl M t j κ hε c' hc0 ht hj hjr ht1 hnd hpiv hcvg hrange hε' hε'le
    Zf U_sf hZfMeas hUsMeas hUs hrank hfloor hagree hGmeas

end DLNFibre.DLN.RLCT
