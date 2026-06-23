import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1NonMPTransport
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeDiffeo

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT` — PIN 1's `regAbsorb_rlct` reduction (#44c)

PIN 1 of the L2 gauge-chart assembly (`deepest_regAbsorb_exists`) bundles the regular-slot
absorption `regAbsorb` with the RLCT-peel conjunct

    rlctAtOn (fun q => ∑ (regAbsorb q).1² + deepestCoreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q => ∑ q.1²         + deepestCoreF (coreAbsorb q).2.1) 0.

This file isolates the **structure-independent heart** of that conjunct: a reduction lemma that
peels the regular substitution `regAbsorb` PAST the coupled core term `deepestCoreF (coreAbsorb
q).2.1`, turning the COUPLED equality into the DECOUPLED #72 peel of `regAbsorb` against a core
term that no longer mentions `coreAbsorb`.

## The coupling and its resolution (the key observation)

The two sides share the core term `deepestCoreF (coreAbsorb q).2.1`, which (since `coreAbsorb` is
the shear `coreShearHomeo shift`, reading the regular slot) DEPENDS on `q.1`. So a direct #72 peel
with `π = regAbsorb` does NOT close it: `(RHS-integrand) ∘ regAbsorb` carries `coreAbsorb (regAbsorb
q)`, not `coreAbsorb q`. The fix is to first change variables by the MEASURE-PRESERVING
`coreAbsorb.symm` (RLCT-invariant, `rlctAtOn_comp_homeomorph`), which collapses the core term to
`deepestCoreF q.2.1` (no `coreAbsorb`) on BOTH sides — because `coreAbsorb.symm` fixes the regular
and spectator slots (so `regAbsorb`'s regular output, which reads only reg+spec, is unchanged), and
`coreAbsorb ∘ coreAbsorb.symm = id` clears the core composition. The decoupled core term is then
independent of the regular slot, so the #72 peel of `regAbsorb` (a reg-slice local diffeo fixing the
core slot) applies cleanly.

This reduction needs ONLY abstract properties of `coreAbsorb` (measure-preserving, fixes reg + spec
+ origin) and of `regAbsorb` (fixes the core slot; its regular output depends only on the reg + spec
input). It is independent of the concrete Schur `shift` and of the concrete `E`-straightening `Ψ`.
The remaining genuinely-analytic atom — the decoupled peel `rlctAtOn (G ∘ regAbsorb) 0 = rlctAtOn G
0` — is supplied as a hypothesis (discharged by the implicit-function-theorem `Ψ` + its
bounded-unit Jacobian via `rlctAtOn_boundedUnit_localHomeomorph`, which needs the concrete `E` map).
-/

open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

/-! ## The structure-independent reduction

Abstract over the three slot types `R` (regular), `C` (core), `S` (spectator) of a split product
`R × (C × S)` (the `DeepestSplit` shape). The reduction transports the regular substitution past the
core term using the measure-preserving conjugation by `coreAbsorb.symm`. -/

section SlotFix
variable {R C S : Type*} [TopologicalSpace R] [TopologicalSpace C] [TopologicalSpace S]

/-- `coreAbsorb.symm` fixes the regular slot, inherited from `coreAbsorb` fixing it: applying
`coreAbsorb_regular` at `coreAbsorb.symm q` and using `coreAbsorb (coreAbsorb.symm q) = q`. -/
theorem symm_fixes_fst (coreAbsorb : (R × (C × S)) ≃ₜ (R × (C × S)))
    (hca_reg : ∀ q, (coreAbsorb q).1 = q.1) (q : R × (C × S)) :
    (coreAbsorb.symm q).1 = q.1 := by
  have h := hca_reg (coreAbsorb.symm q)
  rw [coreAbsorb.apply_symm_apply] at h
  exact h.symm

/-- `coreAbsorb.symm` fixes the spectator slot (same inheritance as `symm_fixes_fst`). -/
theorem symm_fixes_spec (coreAbsorb : (R × (C × S)) ≃ₜ (R × (C × S)))
    (hca_spec : ∀ q, (coreAbsorb q).2.2 = q.2.2) (q : R × (C × S)) :
    (coreAbsorb.symm q).2.2 = q.2.2 := by
  have h := hca_spec (coreAbsorb.symm q)
  rw [coreAbsorb.apply_symm_apply] at h
  exact h.symm

end SlotFix

variable {R C S : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R] [MeasureSpace R] [BorelSpace R]
  [FiniteDimensional ℝ R] [(volume : Measure R).IsAddHaarMeasure]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasureSpace C] [BorelSpace C]
  [FiniteDimensional ℝ C] [(volume : Measure C).IsAddHaarMeasure]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [MeasureSpace S] [BorelSpace S]
  [FiniteDimensional ℝ S] [(volume : Measure S).IsAddHaarMeasure]

omit [NormedSpace ℝ R] [FiniteDimensional ℝ R] [(volume : Measure R).IsAddHaarMeasure]
  [(volume : Measure C).IsAddHaarMeasure] [(volume : Measure S).IsAddHaarMeasure] in
/-- **The reg-absorption RLCT reduction** (PIN 1's heart, structure-independent). Given a
measure-preserving `coreAbsorb` fixing the regular + spectator slots and the origin, and a regular
substitution `regAbsorb` fixing the core slot whose regular output reads only the reg + spectator
input, the coupled RLCT equality

    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q => regF q.1 + coreF (coreAbsorb q).2.1) 0

REDUCES to the decoupled `regAbsorb`-peel

    rlctAtOn (fun q => regF (regAbsorb q).1 + coreF q.2.1) 0
      = rlctAtOn (fun q => regF q.1 + coreF q.2.1) 0

(the core term stripped of `coreAbsorb`). The decoupled peel is the #72 application (the IFT `Ψ` +
its bounded-unit Jacobian); this lemma supplies the conjugation that removes `coreAbsorb` from core
term on both sides. -/
theorem rlctAtOn_regAbsorb_reduce
    (coreAbsorb : (R × (C × S)) ≃ₜ (R × (C × S)))
    (regAbsorb : (R × (C × S)) → (R × (C × S)))
    (regF : R → ℝ) (coreF : C → ℝ)
    (hca_mp : MeasurePreserving coreAbsorb volume volume)
    (hca_base : coreAbsorb 0 = 0)
    (hca_reg : ∀ q, (coreAbsorb q).1 = q.1)
    (hca_spec : ∀ q, (coreAbsorb q).2.2 = q.2.2)
    (hra_regdep : ∀ q q' : R × (C × S), q.1 = q'.1 → q.2.2 = q'.2.2 →
      (regAbsorb q).1 = (regAbsorb q').1)
    (hpeel :
      rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0
        = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0) :
    rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0 := by
  -- The measure-preserving conjugation by `coreAbsorb.symm`.
  have hsymm_mp : MeasurePreserving (⇑coreAbsorb.symm) volume volume :=
    hca_mp.symm coreAbsorb.toMeasurableEquiv
  have hsymm_emb : MeasurableEmbedding (⇑coreAbsorb.symm) := coreAbsorb.symm.measurableEmbedding
  have hsymm_base : coreAbsorb.symm 0 = 0 := by
    conv_lhs => rw [← hca_base]
    rw [coreAbsorb.symm_apply_apply]
  -- LHS: change variables by `coreAbsorb.symm`; the core term collapses to `coreF q.2.1`.
  have hL : rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1) 0 := by
    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
      (fun q : R × (C × S) => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) 0
    rw [hsymm_base] at hstep
    -- `(fun q => regF (regAbsorb q).1 + coreF (coreAbsorb q).2.1) ∘ coreAbsorb.symm`
    --   = `fun q => regF (regAbsorb q).1 + coreF q.2.1`.
    have hfun : (fun q : R × (C × S) =>
          regF (regAbsorb (coreAbsorb.symm q)).1 + coreF (coreAbsorb (coreAbsorb.symm q)).2.1)
        = fun q : R × (C × S) => regF (regAbsorb q).1 + coreF q.2.1 := by
      funext q
      have hcore : (coreAbsorb (coreAbsorb.symm q)).2.1 = q.2.1 := by
        rw [coreAbsorb.apply_symm_apply]
      have hreg : (regAbsorb (coreAbsorb.symm q)).1 = (regAbsorb q).1 :=
        hra_regdep _ _ (symm_fixes_fst coreAbsorb hca_reg q)
          (symm_fixes_spec coreAbsorb hca_spec q)
      rw [hcore, hreg]
    rw [hfun] at hstep
    exact hstep.symm
  -- RHS: same conjugation; the core term collapses, the regular term is untouched.
  have hR : rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
    have hstep := rlctAtOn_comp_homeomorph coreAbsorb.symm hsymm_mp hsymm_emb
      (fun q : R × (C × S) => regF q.1 + coreF (coreAbsorb q).2.1) 0
    rw [hsymm_base] at hstep
    have hfun : (fun q : R × (C × S) =>
          regF (coreAbsorb.symm q).1 + coreF (coreAbsorb (coreAbsorb.symm q)).2.1)
        = fun q : R × (C × S) => regF q.1 + coreF q.2.1 := by
      funext q
      have hcore : (coreAbsorb (coreAbsorb.symm q)).2.1 = q.2.1 := by
        rw [coreAbsorb.apply_symm_apply]
      have hreg : (coreAbsorb.symm q).1 = q.1 := symm_fixes_fst coreAbsorb hca_reg q
      rw [hcore, hreg]
    rw [hfun] at hstep
    exact hstep.symm
  rw [hL, hR, hpeel]

/-! ## The decoupled #72 peel for a core-fixing reg-straightening (the `hpeel` atom)

The decoupled peel `rlctAtOn (fun q => regF (regStraighten q).1 + coreF q.2.1) 0 = rlctAtOn (fun q =>
regF q.1 + coreF q.2.1) 0` is the #72 bounded-unit-Jacobian RLCT change of variables, with
`π = regStraighten` (a local diffeo near `0` fixing the core slot) and the comparison function
`F q = regF q.1 + coreF q.2.1`. Since `regStraighten` fixes the core slot (`(regStraighten q).2.1 =
q.2.1`), `F (regStraighten q) = regF (regStraighten q).1 + coreF q.2.1` — exactly the peel's LHS
integrand. The `IsAddHaarMeasure` instance on the product `M = R × (C × S)` is threaded as an EXPLICIT
hypothesis (#93 fix: the nested-product `volume` does not auto-synthesise it; the producer supplies it
— discharged either by a product-Haar instance or as a standing hypothesis). The IFT bundle
(`πsymm, Dπ, Dπsymm, V`, the on-`V` inverse identities + derivatives + bounded-unit `|det|`) is supplied
by the concrete `regStraighten`'s implicit-function-theorem data (`HasStrictFDerivAt.toOpenPartialHomeomorph`
+ pp2's `dE(0) = id`). -/
theorem rlctAtOn_regStraighten_peel
    (hHaar : (volume : Measure (R × (C × S))).IsAddHaarMeasure)
    (regF : R → ℝ) (coreF : C → ℝ)
    (regStraighten πsymm : (R × (C × S)) → (R × (C × S)))
    (hrs_core : ∀ q, (regStraighten q).2.1 = q.2.1)
    (Dπ Dπsymm : (R × (C × S)) → ((R × (C × S)) →L[ℝ] (R × (C × S))))
    (V : Set (R × (C × S))) (hVopen : IsOpen V) (hwV : (0 : R × (C × S)) ∈ V)
    (hfix : regStraighten 0 = 0)
    (hleft : ∀ w ∈ V, πsymm (regStraighten w) = w) (hright : ∀ w ∈ V, regStraighten (πsymm w) = w)
    (hπcont : ContinuousOn regStraighten V) (hsymmcont : ContinuousOn πsymm V)
    (hderiv : ∀ w ∈ V, HasFDerivAt regStraighten (Dπ w) w)
    (hderivsymm : ∀ w ∈ V, HasFDerivAt πsymm (Dπsymm w) w)
    (hdetmeas : Measurable fun w => |(Dπ w).det|)
    (hdetmeassymm : Measurable fun w => |(Dπsymm w).det|)
    (hbdd : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(Dπ w).det| ∧ |(Dπ w).det| ≤ b)
    (hbddsymm : ∃ a b : ℝ, 0 < a ∧ ∀ w ∈ V, a ≤ |(Dπsymm w).det| ∧ |(Dπsymm w).det| ≤ b) :
    rlctAtOn (fun q : R × (C × S) => regF (regStraighten q).1 + coreF q.2.1) 0
      = rlctAtOn (fun q : R × (C × S) => regF q.1 + coreF q.2.1) 0 := by
  haveI := hHaar
  -- #72 on `F q = regF q.1 + coreF q.2.1`, `π = regStraighten`. `F ∘ π` has the core slot fixed.
  have hkey := rlctAtOn_boundedUnit_localHomeomorph
    (fun q : R × (C × S) => regF q.1 + coreF q.2.1) (0 : R × (C × S))
    regStraighten πsymm Dπ Dπsymm V hVopen hwV hfix hleft hright hπcont hsymmcont
    hderiv hderivsymm hdetmeas hdetmeassymm hbdd hbddsymm
  -- `(fun q => regF q.1 + coreF q.2.1) ∘ regStraighten = fun q => regF (regStraighten q).1 + coreF q.2.1`
  -- (using `regStraighten` fixes the core slot).
  have hfun : (fun q : R × (C × S) => regF (regStraighten q).1 + coreF (regStraighten q).2.1)
      = fun q : R × (C × S) => regF (regStraighten q).1 + coreF q.2.1 := by
    funext q; rw [hrs_core q]
  rw [hfun] at hkey
  exact hkey

/-! ## The IFT → #72 adapter (`rlctAtOn_comp_localDiffeo`)

The clean wrapper the detbound card flagged as "the next layer": from a GLOBALLY smooth self-map `f`
with an INVERTIBLE strict derivative `e : M ≃L[ℝ] M` at `wstar` (and `f` fixing `wstar`), conclude
`rlctAtOn (F ∘ f) wstar = rlctAtOn F wstar`. The implicit-function-theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) packages the local inverse; the bounded-unit Jacobian
(`boundedUnit_fderiv_det`, derived from `ContDiffAt` + the `≃L` derivative) discharges #72's `hbdd`;
`ContDiffAt.to_localInverse` gives the inverse's smoothness at `f wstar = wstar`, hence its
differentiability on a shrunk nbhd. The single open `V` is `Φ.source ∩ Φ.target ∩ (inverse-diff nbhd)`,
on which BOTH inverse identities (`left_inv` on `source`, `right_inv` on `target`) and both derivatives
hold; the det-bounds are intersected in. This is structure-independent Mathlib glue — it is the only
analytic content of `regAbsorb_rlct` once the concrete `regStraighten`'s `dE(0) = id` is supplied. -/
theorem rlctAtOn_comp_localDiffeo {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F : M → ℝ) (wstar : M) (f : M → M) (e : M ≃L[ℝ] M)
    (hcontdiff : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : HasStrictFDerivAt f (e : M →L[ℝ] M) wstar)
    (hfix : f wstar = wstar) :
    rlctAtOn (fun w => F (f w)) wstar = rlctAtOn F wstar := by
  classical
  -- The IFT local diffeo `Φ` (toFun defeq `f`), its source/target open, `wstar ∈ source`.
  set Φ : OpenPartialHomeomorph M M := hf.toOpenPartialHomeomorph f with hΦ
  have hΦcoe : (Φ : M → M) = f := hf.toOpenPartialHomeomorph_coe
  have hsrc_open : IsOpen Φ.source := Φ.open_source
  have htgt_open : IsOpen Φ.target := Φ.open_target
  have hwsrc : wstar ∈ Φ.source := hf.mem_toOpenPartialHomeomorph_source
  -- `f wstar ∈ target` and `f wstar = wstar`, so `wstar ∈ target`.
  have hwtgt : wstar ∈ Φ.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target
    rw [← hΦ] at this
    rwa [hfix] at this
  -- The local inverse `g := Φ.symm`, smooth at `f wstar = wstar` (ContDiff IFT).
  set g : M → M := ⇑Φ.symm with hg
  -- `f` is `ContDiffAt ⊤` everywhere, with `HasFDerivAt f e wstar` (from `hf`).
  have hfderiv_wstar : HasFDerivAt f (e : M →L[ℝ] M) wstar := hf.hasFDerivAt
  have hcda : ContDiffAt ℝ (⊤ : ℕ∞) f wstar := hcontdiff.contDiffAt
  -- `Φ.symm wstar = wstar` (`Φ wstar = f wstar = wstar`, `wstar ∈ source`, `left_inv`).
  have hΦwstar : Φ wstar = wstar := by rw [hΦcoe]; exact hfix
  have hsymm_wstar : Φ.symm wstar = wstar := by
    conv_lhs => rw [← hΦwstar]
    exact Φ.left_inv hwsrc
  -- `g = Φ.symm` is `ContDiffAt ⊤` at `wstar` (`OpenPartialHomeomorph.contDiffAt_symm` at `Φ`).
  have hg_cda0 : ContDiffAt ℝ (⊤ : ℕ∞) g wstar := by
    have hcontdiff_at_symm : ContDiffAt ℝ (⊤ : ℕ∞) f (Φ.symm wstar) := by
      rw [hsymm_wstar]; exact hcontdiff.contDiffAt
    have hfd : HasFDerivAt (Φ : M → M) (e : M →L[ℝ] M) (Φ.symm wstar) := by
      rw [hsymm_wstar, hΦcoe]; exact hfderiv_wstar
    have := Φ.contDiffAt_symm (f₀' := e) hwtgt hfd hcontdiff_at_symm
    rwa [hg]
  -- `g` is `ContDiffAt 1` near `wstar` (downgrade ⊤ → 1, then `eventually`).
  have hg_cda1 : ContDiffAt ℝ (1 : ℕ∞) g wstar := hg_cda0.of_le (by norm_num)
  have hg_ev : ∀ᶠ y in 𝓝 wstar, ContDiffAt ℝ (1 : ℕ∞) g y :=
    hg_cda1.eventually (by simp)
  obtain ⟨Vg, hVg_open, hwVg, hVg_diff⟩ : ∃ Vg : Set M, IsOpen Vg ∧ wstar ∈ Vg ∧
      ∀ y ∈ Vg, DifferentiableAt ℝ g y := by
    obtain ⟨U, hU, hUopen, hwU⟩ := eventually_nhds_iff.mp hg_ev
    exact ⟨U, hUopen, hwU, fun y hy => (hU y hy).differentiableAt (by norm_num)⟩
  -- Bounded-unit Jacobian for `f` (fwd): `ContDiffAt 1` + `HasFDerivAt f (e:≃L) wstar`.
  obtain ⟨Vf, hVf_open, hwVf, af, bf, hafpos, hVf_bnd⟩ :=
    boundedUnit_fderiv_det (f := f) (wstar := wstar) (f' := e)
      (hcontdiff.contDiffAt.of_le (by norm_num)) hfderiv_wstar
  -- Bounded-unit Jacobian for `g` (rev): `ContDiffAt 1 g wstar` + `HasFDerivAt g (e.symm:≃L) wstar`.
  have hg_fderiv_wstar : HasFDerivAt g (e.symm : M →L[ℝ] M) wstar := by
    have hfd : HasFDerivAt (Φ : M → M) (e : M →L[ℝ] M) (Φ.symm wstar) := by
      rw [hsymm_wstar, hΦcoe]; exact hfderiv_wstar
    have := Φ.hasFDerivAt_symm (f' := e) hwtgt hfd
    rwa [hg]
  obtain ⟨Vgb, hVgb_open, hwVgb, ag, bg, hagpos, hVgb_bnd⟩ :=
    boundedUnit_fderiv_det (f := g) (wstar := wstar) (f' := e.symm) hg_cda1 hg_fderiv_wstar
  -- The single working open `V`: source ∩ target ∩ (g-diff nbhd) ∩ (both det-bound nbhds).
  set V : Set M := Φ.source ∩ Φ.target ∩ Vg ∩ Vf ∩ Vgb with hV
  have hVopen : IsOpen V := by
    refine ((((hsrc_open.inter htgt_open).inter hVg_open).inter hVf_open).inter hVgb_open)
  have hwV : wstar ∈ V := ⟨⟨⟨⟨hwsrc, hwtgt⟩, hwVg⟩, hwVf⟩, hwVgb⟩
  -- Inverse identities on `V` (`left_inv` needs source, `right_inv` needs target).
  have hleft : ∀ w ∈ V, g (f w) = w := by
    intro w hw
    have : g (Φ w) = w := Φ.left_inv hw.1.1.1.1
    rwa [hΦcoe] at this
  have hright : ∀ w ∈ V, f (g w) = w := by
    intro w hw
    have : Φ (Φ.symm w) = w := Φ.right_inv hw.1.1.1.2
    rwa [hΦcoe, ← hg] at this
  -- Continuity of `f`, `g` on `V`.
  have hπcont : ContinuousOn f V := hcontdiff.continuous.continuousOn
  have hsymmcont : ContinuousOn g V := by
    refine ContinuousOn.mono ?_ (fun w hw => hw.1.1.2)
    exact fun w hw => (hVg_diff w hw).continuousAt.continuousWithinAt
  -- Derivatives on `V`: `Dπ := fderiv f`, `Dπsymm := fderiv g`.
  have hderiv : ∀ w ∈ V, HasFDerivAt f (fderiv ℝ f w) w :=
    fun w _ => (hcontdiff.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  have hderivsymm : ∀ w ∈ V, HasFDerivAt g (fderiv ℝ g w) w :=
    fun w hw => (hVg_diff w hw.1.1.2).hasFDerivAt
  -- Determinant measurability: `fderiv ℝ ·` is GLOBALLY measurable for ANY map (`measurable_fderiv`,
  -- finite-dim ⟹ `CompleteSpace`; `BorelSpace M` ⟹ `OpensMeasurableSpace`), so `|det ∘ fderiv|` is
  -- measurable for `f` AND the only-locally-smooth inverse `g` alike.
  have hdetmeas : Measurable fun w => |(fderiv ℝ f w).det| :=
    continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ f))
  have hdetmeassymm : Measurable fun w => |(fderiv ℝ g w).det| :=
    continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ g))
  -- Assemble #72.  `Dπ w := fderiv ℝ f w` at `wstar` is `e` (so det = |e.det| > 0 ∈ [af,bf]).
  have hkey := rlctAtOn_boundedUnit_localHomeomorph F wstar f g
    (fun w => fderiv ℝ f w) (fun w => fderiv ℝ g w) V hVopen hwV hfix
    hleft hright hπcont hsymmcont hderiv hderivsymm hdetmeas hdetmeassymm
    ⟨af, bf, hafpos, fun w hw => hVf_bnd w hw.1.2⟩
    ⟨ag, bg, hagpos, fun w hw => hVgb_bnd w hw.2⟩
  exact hkey

/-! ## The concrete reg-straightening from a pivot map (`regStraightenOf`)

The `regAbsorb` field is a TOTAL self-map of `R × (C × S)` whose reg slot carries the nonlinear
straightened residual `E_pivot` (reading reg + spec), fixing core + spec. PIN 1's `regAbsorb_rlct`
needs ONLY that its total strict derivative at `0` is the identity (so the IFT applies); the concrete
nonlinear form of `E_pivot` is PIN 2's (the squeeze). So PIN 1 abstracts over `E_pivot : R × S → R`
with `HasStrictFDerivAt E_pivot (fst) 0` — the "`dE(0) = id`" of the ruling, typed precisely: the
derivative of the reg-component at `0` is the projection `fst : R × S →L R` (identity on the reg
directions, zero on the spectator), which makes the total map's derivative `id_{R×(C×S)}`. -/

section RegStraightenOf
variable {R C S : Type*}
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The reg-straightening built from a pivot map `E_pivot : R × S → R`: replace the reg slot by
`E_pivot (reg, spec)`, fix core + spec. (The (C)-fallback total continuous self-map.) -/
def regStraightenOf (E_pivot : R × S → R) : R × (C × S) → R × (C × S) :=
  fun q => (E_pivot (q.1, q.2.2), q.2.1, q.2.2)

@[simp] theorem regStraightenOf_core (E_pivot : R × S → R) (q : R × (C × S)) :
    (regStraightenOf (C := C) E_pivot q).2.1 = q.2.1 := rfl

@[simp] theorem regStraightenOf_spectator (E_pivot : R × S → R) (q : R × (C × S)) :
    (regStraightenOf (C := C) E_pivot q).2.2 = q.2.2 := rfl

@[simp] theorem regStraightenOf_fst (E_pivot : R × S → R) (q : R × (C × S)) :
    (regStraightenOf (C := C) E_pivot q).1 = E_pivot (q.1, q.2.2) := rfl

theorem regStraightenOf_basepoint (E_pivot : R × S → R) (h0 : E_pivot 0 = 0) :
    regStraightenOf (C := C) E_pivot 0 = 0 := by
  simp only [regStraightenOf]
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  show E_pivot (((0 : R × (C × S)).1), ((0 : R × (C × S)).2.2)) = 0
  rw [← h0]; rfl

theorem continuous_regStraightenOf (E_pivot : R × S → R) (hcont : Continuous E_pivot) :
    Continuous (regStraightenOf (C := C) E_pivot) := by
  refine Continuous.prodMk ?_ (Continuous.prodMk (continuous_fst.comp continuous_snd)
    (continuous_snd.comp continuous_snd))
  exact hcont.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

/-- The reg-straightening's regular output reads only reg + spec (the `hra_regdep` of
`rlctAtOn_regAbsorb_reduce`): two points with the same reg AND spec slots have the same reg output. -/
theorem regStraightenOf_regdep (E_pivot : R × S → R) (q q' : R × (C × S))
    (hreg : q.1 = q'.1) (hspec : q.2.2 = q'.2.2) :
    (regStraightenOf (C := C) E_pivot q).1 = (regStraightenOf (C := C) E_pivot q').1 := by
  simp only [regStraightenOf_fst, hreg, hspec]

/-- **`regStraightenOf E_pivot` has strict derivative `id` at `0`** — the analytic gate of PIN 1.
Given `HasStrictFDerivAt E_pivot (fst : R × S →L R) 0` (the precise `dE(0) = id`), the total map's
strict derivative at `0` is `ContinuousLinearMap.id`. Assembled by `HasStrictFDerivAt.prodMk` of the
three components: reg (`E_pivot ∘ (reg,spec)-projection`, derivative `fst ∘ that = reg-projection`),
core (`(reg,(core,spec)) ↦ core`, linear), spec (linear). -/
theorem hasStrictFDerivAt_regStraightenOf (E_pivot : R × S → R)
    (hE : HasStrictFDerivAt E_pivot (ContinuousLinearMap.fst ℝ R S) 0) :
    HasStrictFDerivAt (regStraightenOf (C := C) E_pivot)
      (ContinuousLinearMap.id ℝ (R × (C × S))) 0 := by
  -- The inner linear projection `(reg,(core,spec)) ↦ (reg,spec)`, strict-diff'able everywhere.
  set proj : (R × (C × S)) →L[ℝ] (R × S) :=
    (ContinuousLinearMap.fst ℝ R (C × S)).prod
      ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))) with hproj
  have hproj_sd : HasStrictFDerivAt (fun q : R × (C × S) => (q.1, q.2.2)) proj 0 :=
    proj.hasStrictFDerivAt
  -- reg-component: `E_pivot ∘ proj`, derivative `fst.comp proj = reg-projection`.
  have hreg_sd : HasStrictFDerivAt (fun q : R × (C × S) => E_pivot (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ R S).comp proj) 0 := by
    have hcomp := hE.comp (x := (0 : R × (C × S))) hproj_sd
    simpa using hcomp
  -- core + spec components: linear projections.
  have hcore_sd : HasStrictFDerivAt (fun q : R × (C × S) => q.2.1)
      ((ContinuousLinearMap.fst ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))) 0 :=
    ((ContinuousLinearMap.fst ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))).hasStrictFDerivAt
  have hspec_sd : HasStrictFDerivAt (fun q : R × (C × S) => q.2.2)
      ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))) 0 :=
    ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))).hasStrictFDerivAt
  have hcs_sd : HasStrictFDerivAt (fun q : R × (C × S) => (q.2.1, q.2.2))
      (((ContinuousLinearMap.fst ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))).prod
        ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S)))) 0 :=
    hcore_sd.prodMk hspec_sd
  have htotal := hreg_sd.prodMk hcs_sd
  -- The assembled derivative is `id` (each slot projects to itself).
  refine htotal.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro x
  show ((ContinuousLinearMap.fst ℝ R S).comp proj x,
      (((ContinuousLinearMap.fst ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))) x,
       ((ContinuousLinearMap.snd ℝ C S).comp (ContinuousLinearMap.snd ℝ R (C × S))) x))
    = x
  exact Prod.ext rfl (Prod.ext rfl rfl)

end RegStraightenOf

end DLNFibre.DLN.RLCT
