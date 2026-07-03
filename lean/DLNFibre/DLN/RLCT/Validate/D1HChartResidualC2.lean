import DLNFibre.DLN.RLCT.Validate.D1HChartResidual

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartResidualC2` — the first-peel residual at `C²` + slice-vanishing

The banked first-peel producer `dln_hchart_residual` (`D1HChartResidual`) outputs a GLOBAL `C¹`
residual `q`. The SECOND peel (`secondPeel_hchart_residual`, `D1SecondPeelAssembly`) demands its input
slice residual `q (0,·)` be `ContDiff ℝ 2` (`C²`) and vanish at the basepoint (`hslice0`). This module
strengthens the first peel to supply both — CLOSING the reviewer-flagged item-(5) `C¹`-vs-`C²` gap.

## Why `C²` is a STATED-CEILING, not an obstruction (decorrelated: Codex xhigh + the source chain)

The DLN loss is a POLYNOMIAL, so its charts are `C^∞`. Inside `dln_hchart_residual` the entire chain
is already `ContDiffOn ℝ 2` BEFORE the final bump-globalisation (`hg1CD`): `contDiff_chartΦ` proves
each coordinate `ContDiff ℝ ⊤`; `ContDiffAt.to_localInverse` preserves `C^n` exactly (no derivative
loss); `contDiffOn_rawResidVec` is the `C^∞` loss composed with the `C²` inverse. The regularity drops
to `C¹` at ONE spot only — the bump call `exists_contDiff_eventuallyEq_of_contDiffOn (n := 1)`, which
is PARAMETRIC in `n : ℕ∞`. Calling it at `(n := 2)` yields a global `C²` `q` with no new analytic
content. (`χ • g` is `C^k` for a `C^∞` bump `χ` and `C^k` `g`; a bump-globalised local-`C²` map is
globally `C²`.)

## Slice-vanishing `q (0, t0) = 0`

At an optimal `v` (`prod H v = B`) every loss entry vanishes at the flat origin
(`lossEntry_zero_of_optimal`), and the IFT chart fixes it (`Ψsymm 0 = 0`), so the raw residual vector
`rawResidVec … 0 = 0`. The bump agrees with the raw residual near the basepoint `w0 = splitHomeo 0`,
and `w0 = (0, t0)` (the selected block reads `0 (ec k) = 0`), so `q (0, t0) = rawResidVec … 0 = 0`.

Scope L = 2 (`H : Fin 3 → ℕ`); `m = nRegL2 H r` at the use-site. This is the additive strengthening
that makes the two-peel chain composable; the banked `dln_hchart_residual` (`C¹`) is untouched.
-/

open Matrix Module MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {H : Fin (2 + 1) → ℕ} {m : ℕ} {ec : Fin m → Fin (flatDim H)}
  {B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ} {v : Params H} {r : ℕ}
  {er : Fin m → Fin (H 0) × Fin (H 2)}

/-- **The right-inverse chart corollary, additionally exposing `Ψsymm wstar = wstar`.** Same output
as `rlctAtOn_eq_of_contDiff_chart_rinv`, with the extra fixpoint fact the slice-vanishing needs. The
fixpoint is the left-inverse identity at `wstar` (`Ψsymm (Φ wstar) = wstar`, with `Φ wstar = wstar`),
already internal to the bounded-unit chart. -/
theorem rlctAtOn_eq_of_contDiff_chart_rinv_fix {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
    (f : E → ℝ) (Φ : E → E) (wstar : E) (f' : E ≃L[ℝ] E)
    (hΦ : ContDiff ℝ 2 Φ) (hΦ' : HasFDerivAt Φ (f' : E →L[ℝ] E) wstar)
    (hfix : Φ wstar = wstar) :
    ∃ (Ψsymm : E → E) (V : Set E), IsOpen V ∧ wstar ∈ V ∧
      ContDiffOn ℝ 2 Ψsymm V ∧
      Ψsymm wstar = wstar ∧
      (∀ᶠ w in 𝓝 wstar, Φ (Ψsymm w) = w) ∧
      rlctAtOn f wstar = rlctAtOn (fun w => f (Ψsymm w)) wstar := by
  obtain ⟨Ψ, Ψsymm, DΨ, DΨsymm, V, hVopen, hwV, hΨfix, hleft, hright, hΨcont, hsymmcont,
    hderiv, hderivsymm, hdetmeas, hdetmeassymm, hbdd, hbddsymm, hΨΦ, hsymmCD⟩ :=
    exists_boundedUnit_chart_of_contDiffAt Φ wstar f' hΦ hΦ' hfix
  -- `Ψsymm wstar = wstar` (the left inverse at `wstar`, with `Ψ wstar = wstar`).
  have hsymmfix : Ψsymm wstar = wstar := by
    have := hleft wstar hwV; rwa [hΨfix] at this
  have hsymmCA : ContinuousAt Ψsymm wstar :=
    (hsymmcont.continuousWithinAt hwV).continuousAt (hVopen.mem_nhds hwV)
  have h2 : ∀ᶠ w in 𝓝 wstar, Ψsymm w ∈ V := by
    have hmem : Ψsymm wstar ∈ V := by rw [hsymmfix]; exact hwV
    exact hsymmCA (hVopen.mem_nhds hmem)
  have hrinv : ∀ᶠ w in 𝓝 wstar, Φ (Ψsymm w) = w := by
    filter_upwards [hVopen.mem_nhds hwV, h2] with w hwVmem hsymmVmem
    rw [← hΨΦ _ hsymmVmem]; exact hright w hwVmem
  refine ⟨Ψsymm, V, hVopen, hwV, hsymmCD, hsymmfix, hrinv, ?_⟩
  have hinv : ∀ w ∈ V, Ψsymm (Φ w) = w := by
    intro w hw; rw [← hΨΦ w hw]; exact hleft w hw
  have hgerm : f =ᶠ[𝓝 wstar] fun w => (fun w => f (Ψsymm w)) (Φ w) := by
    filter_upwards [hVopen.mem_nhds hwV] with w hwV'
    show f w = f (Ψsymm (Φ w))
    rw [hinv w hwV']
  exact rlctAtOn_eq_of_contDiff_chart f (fun w => f (Ψsymm w)) Φ wstar f' hΦ hΦ' hfix hgerm

/-- The raw residual vector vanishes at the flat origin (optimal `v` ⟹ every loss entry `0` there,
and the chart fixes `Ψsymm 0 = 0`). -/
theorem rawResidVec_zero_of_optimal (hopt : prod H v = B)
    (Ψsymm : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ)) (hΨ0 : Ψsymm 0 = 0) :
    rawResidVec B v er Ψsymm 0 = 0 := by
  rw [rawResidVec]
  rw [show (fun i => rawResid B v er Ψsymm 0 ((entryIdx H).symm i))
      = (0 : Fin (H 0 * H 2) → ℝ) from ?_]
  · rfl
  · funext i
    rw [rawResid]
    by_cases hsr : selRow er ((entryIdx H).symm i)
    · rw [if_pos hsr]; rfl
    · rw [if_neg hsr, hΨ0, lossEntry_zero_of_optimal hopt _ _]; rfl

/-- **The D1 first-peel `hchart` at `C²`, with the slice vanishing.** Strengthens
`dln_hchart_residual`: at an optimal `v` (`prod v = B`, `rank B = r`) with the invertible
flat-Jacobian minor `(er, ec)`, the local RLCT of the DLN loss at `v` equals the post-chart
`∑ s² + ∑ q²` shape for a GLOBAL `C²` residual `q`, with `q (0, t0) = 0`. Same construction as
`dln_hchart_residual`, but the
bump is called at `(n := 2)` (the composite is already `ContDiffOn ℝ 2`) and the slice-vanishing is
read off `rawResidVec_zero_of_optimal`. Feeds the second peel's `hslice`/`hslice0` inputs. -/
theorem dln_hchart_residual_c2 (hopt : prod H v = B) (hr : B.rank = r)
    (her : Function.Injective er) (hec : Function.Injective ec)
    (hminor : ((jacFlatL2 H v).submatrix er ec).det ≠ 0) :
    ∃ (q : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) → EuclideanSpace ℝ (Fin (H 0 * H 2)))
      (t0 : Fin (flatDim H - m) → ℝ),
      ContDiff ℝ 2 q ∧
      q ((0 : Fin m → ℝ), t0) = 0 ∧
      rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) =>
            (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin m → ℝ), t0) := by
  classical
  set Φ : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) := chartΦ H B v er ec with hΦdef
  set f' : (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ) :=
    chartFDerivEquiv H B v er ec hec hminor with hf'def
  have hΦcd : ContDiff ℝ 2 Φ := contDiff_chartΦ
  have hΦ' : HasFDerivAt Φ (f' : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ)) 0 :=
    hasFDerivAt_chartΦ_equiv hec hminor
  have hfix : Φ 0 = 0 := chartΦ_zero hec
  -- the right-inverse chart, additionally exposing `Ψsymm 0 = 0`.
  obtain ⟨Ψsymm, V, hVopen, hwV, hsymmCD, hΨ0, hrinv, hrlcttransfer⟩ :=
    rlctAtOn_eq_of_contDiff_chart_rinv_fix (lossFlatShift H B v) Φ 0 f' hΦcd hΦ' hfix
  -- the residual vector, `C²` on `V`.
  have hgCD : ContDiffOn ℝ 2 (rawResidVec B v er Ψsymm) V :=
    contDiffOn_rawResidVec hopt Ψsymm hsymmCD
  set U : Set ((Fin m → ℝ) × (Fin (flatDim H - m) → ℝ)) := splitHomeo hec '' V with hUdef
  have hUopen : IsOpen U := (splitHomeo hec).isOpenMap V hVopen
  set w0 : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) := splitHomeo hec 0 with hw0def
  have hw0U : w0 ∈ U := ⟨0, hwV, rfl⟩
  have hmapsto : Set.MapsTo (splitHomeo hec).symm U V := by
    rintro p ⟨w, hwV', rfl⟩
    rw [Homeomorph.symm_apply_apply]; exact hwV'
  have hsymmContDiff2 : ContDiff ℝ 2 (splitHomeo hec).symm := by
    refine (contDiff_splitHomeo_symm hec).of_le ?_
    rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg1CD : ContDiffOn ℝ 2
      (fun p => rawResidVec B v er Ψsymm ((splitHomeo hec).symm p)) U := by
    have := hgCD.comp (hsymmContDiff2.contDiffOn (s := U)) hmapsto
    exact this
  -- bump-globalise at `(n := 2)`: `q` global `C²`, `=ᶠ g₁` near `w0`.
  obtain ⟨q, hqCD, hqeq⟩ :=
    exists_contDiff_eventuallyEq_of_contDiffOn (n := 2) hUopen hw0U hg1CD
  -- `splitHomeo 0 = (0, w0.2)`.
  have hfst : (splitHomeo hec (0 : Fin (flatDim H) → ℝ)).1 = (0 : Fin m → ℝ) := by
    funext k; rw [splitHomeo_fst_apply hec 0 k]; rfl
  have hsh : splitHomeo hec (0 : Fin (flatDim H) → ℝ)
      = ((0 : Fin m → ℝ), (splitHomeo hec 0).2) := Prod.ext hfst rfl
  refine ⟨q, w0.2, hqCD, ?_, ?_⟩
  · -- slice-vanishing: `q (0, t0) = q w0 = rawResidVec … 0 = 0`.
    have hw0eq : ((0 : Fin m → ℝ), w0.2) = w0 := by rw [hw0def, hsh]
    rw [hw0eq]
    have hqw0 : q w0 = rawResidVec B v er Ψsymm ((splitHomeo hec).symm w0) := hqeq.self_of_nhds
    rw [hqw0, hw0def, Homeomorph.symm_apply_apply,
      rawResidVec_zero_of_optimal hopt Ψsymm hΨ0]
  · -- the RLCT chart transfer (verbatim the `dln_hchart_residual` assembly, C² `q`).
    set F : (Fin m → ℝ) × (Fin (flatDim H - m) → ℝ) → ℝ :=
      fun p => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2) with hFdef
    have hkey : (fun w => F (splitHomeo hec w)) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
        fun w => lossFlatShift H B v (Ψsymm w) := by
      have hqpull : (fun w => q (splitHomeo hec w)) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
          fun w => rawResidVec B v er Ψsymm w := by
        have hcont : ContinuousAt (splitHomeo hec) 0 := (splitHomeo hec).continuous.continuousAt
        have := hcont.eventually hqeq
        filter_upwards [this] with w hw
        rw [hw, Homeomorph.symm_apply_apply]
      have hgA := germA hopt her hec Ψsymm hrinv
      filter_upwards [hqpull, hgA] with w hwq hwA
      change (∑ i, (splitHomeo hec w).1 i ^ 2) + (∑ i, q (splitHomeo hec w) i ^ 2)
        = lossFlatShift H B v (Ψsymm w)
      have hsel : (∑ i, (splitHomeo hec w).1 i ^ 2) = ∑ k : Fin m, (w (ec k)) ^ 2 := by
        apply Finset.sum_congr rfl; intro k _; rw [splitHomeo_fst_apply hec w k]
      have hresid : (∑ i, q (splitHomeo hec w) i ^ 2)
          = ∑ ij : Fin (H 0) × Fin (H 2), (rawResid B v er Ψsymm w ij) ^ 2 := by
        rw [show (fun i => q (splitHomeo hec w) i ^ 2)
            = fun i => rawResidVec B v er Ψsymm w i ^ 2 from by rw [hwq]]
        rw [show (∑ i, rawResidVec B v er Ψsymm w i ^ 2)
            = ∑ i, (rawResid B v er Ψsymm w ((entryIdx H).symm i)) ^ 2 from by
          apply Finset.sum_congr rfl; intro i _; rw [rawResidVec_apply]]
        exact Equiv.sum_comp (entryIdx H).symm (fun ij => (rawResid B v er Ψsymm w ij) ^ 2)
      rw [hsel, hresid, ← hwA]
    rw [rlctAt_eq_rlctAtOn_lossFlatShift H B v, hrlcttransfer]
    rw [← rlctAtOn_congr_germ (fun w => F (splitHomeo hec w))
      (fun w => lossFlatShift H B v (Ψsymm w)) 0 hkey]
    rw [rlctAtOn_comp_homeomorph (splitHomeo hec) (splitHomeo_mp hec) (splitHomeo_emb hec) F 0]
    rw [hsh]

end DLNFibre.DLN.RLCT
