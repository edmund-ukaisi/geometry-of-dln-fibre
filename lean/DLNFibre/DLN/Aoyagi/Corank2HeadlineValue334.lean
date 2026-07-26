import DLNFibre.DLN.Aoyagi.Corank2Headline334

/-!
# `DLN.Aoyagi.Corank2HeadlineValue334` — born-α `hsandwich` discharge (elder fact #2), sorry-free

Tightens `Corank2Headline334.rlctAt_coreGen334_ge_four_of_family` by DISCHARGING its `hsandwich`
hypothesis from the elder's fact-#2 mechanism: the per-pivot born-native chart `g_c` exposes ONE
`coreGen` entry (index `k0 c`) as EXACTLY the survivor monomial `∏_d w_d^{ek₀_c d}` (`hentry` — the
P1-cert `M[0,0] = E` after the recoord shear cancels the block-elim cross-term), so the loss
dominates that monomial's square GLOBALLY:

`∑ᵢ (coreGenᵢ ∘ g_c)² ≥ (coreGen_{k0 c} ∘ g_c)² = (∏_d w_d^{ek₀_c d})²`   (`Finset.single_le_sum`).

With the wire's constant-survivor family `bexp_c := fun _ ↦ ek₀_c` and `cst_c := 1/Mn`
(`Mn = dvec(last)·dvec 0 = 12`, the number of `coreGen` entries), the monomial side collapses
(`DomainSandwich.sumSqFam_const_monomialFam`: `∑ₖ monomialₖ² = Mn·monomial²`) and `cst·Mn·monomial²
= monomial² ≤ loss` — the wire's `hsandwich`, holding at EVERY `w` (`ρ_leaf = ∞`, no value shrink;
the survivor is a UNIT, so no domain restriction). The `1/Mn` scale is RLCT-invisible (absorbed in
`cst`); `hchain` is `le_refl` (the survivor family is constant).

So this reduces the (3,3,4) V-lower headline to a contract with NO measure-theoretic sandwich left —
only the born-α VALUE `hentry` (the per-leaf entry-equality, P1-cert core), the area-formula data,
the a.e.-cover, and `divisorMin = 8`. That `hentry` (× the singular leaves, the all-leaves min) is
the dedicated born-native seat.

## Scope (honest)
- IN: the `hsandwich`-free reduction — headline `4 ≤ rlctAt` from the exact survivor-entry equality
  `hentry` + area-formula family data + a.e.-cover + `divisorMin = 8`. Sorry-free, clean-three.
- OUT: `hentry` itself (the born-native `g_c` fan + the per-leaf `coreGen_{k0}∘g_c = monomial`
  recoord-shear algebra, P1 cert F5–F9); the concrete cover (`hcover`) and `jac`/routine for the
  born-native family — the dedicated seat this contract plugs into.
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core.Aoyagi RLCT
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi

-- maxHeartbeats bump: instantiating the 20-hypothesis reduction at the concrete `coreGen`
-- family forces heavy `whnf` on the flattened-product loss during unification (heavy-but-finite).
set_option maxHeartbeats 1000000 in
/-- **The (3,3,4) V-lower headline from the born-α survivor ENTRY-equality** (elder fact #2). The
`hsandwich`-free tightening of `rlctAt_coreGen334_ge_four_of_family`: instead of the sum-level
sandwich, the seat supplies the exact per-leaf entry-equality
`hentry : coreGen (k0 c) (g c w) = ∏_d w_d^{ek₀_c d}` (globally in `w`) — the born-native chart
exposes that `coreGen` entry as the survivor monomial exactly. The loss then dominates that monomial
square by `Finset.single_le_sum`, so with the constant-survivor family `bexp = fun _ ↦ ek₀ c` and
`cst = 1/Mn` the wire's `hsandwich` holds at every `w` (no value shrink), and the headline follows
from `rlctAt_coreGen334_ge_four_of_family`. -/
theorem rlctAt_coreGen334_ge_four_of_survivor_entries
    {numCharts : ℕ} (hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (g : Fin numCharts → (Fin 21 → ℝ) → (Fin 21 → ℝ))
    (dom nbhd excep : Fin numCharts → Set (Fin 21 → ℝ))
    (k0 : Fin numCharts → Fin (dvec (Fin.last 2) * dvec 0))
    (ek₀ : Fin numCharts → Fin 21 → ℕ)
    (jac : Fin numCharts → Fin 21 → ℕ) (unit : Fin numCharts → (Fin 21 → ℝ) → ℝ)
    (U : Set (Fin 21 → ℝ))
    (hbind : ∀ c, (bindingAxes (ek₀ c)).Nonempty)
    (hgdiff : ∀ c, Differentiable ℝ (g c))
    (hdomcpt : ∀ c, IsCompact (dom c))
    (hnbhd_open : ∀ c, IsOpen (nbhd c)) (hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (hexcep_meas : ∀ c, MeasurableSet (excep c)) (hexcep_null : ∀ c, volume (excep c) = 0)
    (hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (hunit_cont : ∀ c, ContinuousOn (unit c) (nbhd c))
    (hunit_ne : ∀ c, ∀ u ∈ nbhd c, unit c u ≠ 0)
    (hjac : ∀ c, ∀ u ∈ nbhd c, |jacDet (g c) u| = jacWeight (jac c) u * |unit c u|)
    (hentry : ∀ c, ∀ w, coreGen dvec eWrap (k0 c) (g c w) = ∏ d, (w d) ^ (ek₀ c d))
    (hU : U ∈ 𝓝 (0 : Fin 21 → ℝ))
    (hcover : volume (U \ ⋃ c, g c '' dom c) = 0)
    (hunit_mult : ∀ c, ∀ d ∈ bindingAxes (ek₀ c), ek₀ c d = 1)
    (hdivisorMin : Finset.univ.inf' hne
        (fun c ↦ (bindingAxes (ek₀ c)).inf' (hbind c) (fun d ↦ (jac c d + 1 : ℝ))) = 8) :
    (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) := by
  -- `Mn = dvec(last)·dvec 0 = 12 > 0` (the number of `coreGen` entries; the `1/Mn` scale base).
  have hMnR : (0 : ℝ) < ((dvec (Fin.last 2) * dvec 0 : ℕ) : ℝ) := by
    have : (dvec (Fin.last 2) * dvec 0 : ℕ) = 12 := by decide
    rw [this]; norm_num
  have hMn0 : ((dvec (Fin.last 2) * dvec 0 : ℕ) : ℝ) ≠ 0 := ne_of_gt hMnR
  -- The constant-survivor family and its `1/Mn` sandwich constant.
  refine rlctAt_coreGen334_ge_four_of_family hne g dom nbhd excep
    (fun c ↦ fun _ ↦ ek₀ c) k0 jac unit (fun _ ↦ 1 / ((dvec (Fin.last 2) * dvec 0 : ℕ) : ℝ)) U
    hbind hgdiff hdomcpt hnbhd_open hdom_sub hexcep_meas hexcep_null hg_inj
    (fun _ _ _ ↦ le_refl _) hunit_cont hunit_ne hjac (fun _ ↦ one_div_pos.mpr hMnR) ?_ hU hcover
    hunit_mult hdivisorMin
  -- `hsandwich`: entry-equality ⟹ loss ≥ monomial² globally; `cst·Mn·monomial² = monomial²`.
  intro c p _
  refine Filter.Eventually.of_forall (fun w ↦ ?_)
  rw [sumSqFam_const_monomialFam]
  have hcancel :
      (1 / ((dvec (Fin.last 2) * dvec 0 : ℕ) : ℝ))
          * (((dvec (Fin.last 2) * dvec 0 : ℕ) : ℝ) * (∏ d, (w d) ^ (ek₀ c d)) ^ 2)
        = (∏ d, (w d) ^ (ek₀ c d)) ^ 2 := by
    field_simp
  rw [hcancel]
  have hsum : sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ g c) w
      = ∑ i, (coreGen dvec eWrap i (g c w)) ^ 2 := by
    simp only [sumSqFam, Function.comp_apply]
  refine ⟨sq_nonneg _, ?_⟩
  rw [hsum]
  calc (∏ d, (w d) ^ (ek₀ c d)) ^ 2
      = (coreGen dvec eWrap (k0 c) (g c w)) ^ 2 := by rw [hentry c w]
    _ ≤ ∑ i, (coreGen dvec eWrap i (g c w)) ^ 2 :=
        Finset.single_le_sum (f := fun i ↦ (coreGen dvec eWrap i (g c w)) ^ 2)
          (fun i _ ↦ sq_nonneg _) (Finset.mem_univ (k0 c))

-- Forced axiom gate: the born-α `hsandwich` discharge rests only on
-- `[propext, Classical.choice, Quot.sound]` (no born-α value content is proved here — `hentry` is
-- a hypothesis; only the sum-of-squares domination is discharged).
#assert_banked_clean_batch [rlctAt_coreGen334_ge_four_of_survivor_entries]

end DLNFibre.DLN.Aoyagi
