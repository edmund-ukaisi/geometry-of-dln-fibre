<task>
Lean 4 / Mathlib v4.29 (DLNFibre RLCT formalisation). I'm proving the "Route-M rlct-cover BRIDGE": the
RLCT of a core `F` at the deepest point `0` equals the infimum over a chart cover of per-leaf monomial
thresholds. I have a SPECIFY (green signature, body sorry); I want the cleanest PROOF decomposition
before grinding — flag the hardest sub-step + the right Mathlib lemmas.

THE GOAL (signature compiles):
  theorem routeM_rlctAtOn_eq_iInf {N} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
      (ι) [Fintype ι] [Nonempty ι] (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ)
      (hcover : IsRouteMCover F U ι d k h) :
      rlctAtOn F 0 = ⨅ i : ι, monomialThreshold (d i) (k i) (h i)

THE ABSTRACT COVER HYPOTHESIS (IsRouteMCover, fields):
  Fmeas : Measurable F
  Uopen : IsOpen U ;  Umem : 0 ∈ U
  cover_le : ∀ c' : NNReal,
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c':ℝ)))
        ≤ ∑ i : ι, ∫⁻ y in unitBox (d i), ENNReal.ofReal (monomialIntegrand (d i)(k i)(h i)(c':ℝ) y)
  cover_ge_div : ∀ c' : NNReal, (∃ i, monomialThreshold (d i)(k i)(h i) ≤ (c':ℝ≥0∞)) →
      ∀ Ω, IsOpen Ω → 0 ∈ Ω → ¬ IntegrableOn (fun x => |F x|^(-(c':ℝ)) * 1) Ω volume

GREEN LIBRARY LEMMAS (verified to exist, signatures as given):
- rlctAtOn_ge_of_integral_lt (F) (hFm : Measurable F) (U) (hU : IsOpen U) (h0 : 0 ∈ U) (t : ℝ≥0∞)
    (hfin : ∀ c' : NNReal, (c':ℝ≥0∞) < t → ∫⁻ x in U, ENNReal.ofReal (|F x|^(-(c':ℝ))) < ⊤) : t ≤ rlctAtOn F 0
- rlctAtOn_le_of_adm_le (F) (t) (hadm : ∀ c' : NNReal, (∃ Ω, IsOpen Ω ∧ 0 ∈ Ω ∧
    IntegrableOn (fun w => |F w|^(-(c':ℝ)) * 1) Ω volume) → (c':ℝ≥0∞) ≤ t) : rlctAtOn F 0 ≤ t
- monomialIntegrand_integrable_of_lt (d k h) (c' : NNReal) (hc' : 0 < c')
    (hlt : (c':ℝ≥0∞) < monomialThreshold d k h) : IntegrableOn (monomialIntegrand d k h (c':ℝ)) (unitBox d) volume
- monomialThreshold d k h : ℝ≥0∞ := sSup {c | ∃ c':NNReal, c=c' ∧ IntegrableOn (monomialIntegrand d k h c') (unitBox d) volume}
- monomialIntegrand d k h c u = (∏ⱼ |u j|^(h j)) * (∏ⱼ |u j|^(2 k j))^(−c)

MY PLANNED DECOMPOSITION (critique + fix):
- le_antisymm. Let t := ⨅ i, monomialThreshold (d i)(k i)(h i).
- (≥) t ≤ rlctAtOn F 0: via rlctAtOn_ge_of_integral_lt with this t. Need: ∀ c' < t, ∫⁻_U |F|^{−c'} < ⊤.
    From cover_le: bound by ∑ᵢ ∫⁻_{unitBox} monomialIntegrand_i. c' < t = ⨅ ⟹ c' < monomialThreshold_i ∀i
    ⟹ each leaf integrable (monomialIntegrand_integrable_of_lt) ⟹ each ∫⁻ < ⊤ ⟹ finite sum < ⊤. (the c'=0 edge: 0 < t since thresholds > 0? need 0 < c' for the integrable lemma — handle c'=0 separately, |F|^0=1 integrable on bounded U.)
- (≤) rlctAtOn F 0 ≤ t: via rlctAtOn_le_of_adm_le with t. Need: any admissible c' (integrable on some Ω∋0) has c' ≤ t. Contrapositive: if c' > t = ⨅, then ∃ i, monomialThreshold_i ≤ c' (the ⨅ is attained / < c'), so cover_ge_div ⟹ NOT integrable on any Ω — contradicting admissibility. So admissible ⟹ c' ≤ t. (the ⨅-attained step: ⨅ over a Fintype Nonempty is attained, so ⨅ < c' ⟹ ∃ i, threshold_i ≤ ... need threshold_i < c' or ≤; careful with strict/non-strict + the ⨅ = min over finite.)
</task>

<output_contract>
  1. Is my le_antisymm decomposition correct? (yes/no + any gap).
  2. For (≥): the exact lemma chain to get `∑ᵢ ∫⁻_{unitBox} monomialIntegrand_i < ⊤` from `c' < ⨅ threshold`
     — including the `IntegrableOn ⟹ ∫⁻ ofReal < ⊤` step (which Mathlib lemma: HasFiniteIntegral / Integrable.lintegral_lt_top / ofReal?) and the finite-sum-of-finite (ENNReal.sum_lt_top). Handle the c'=0 edge.
  3. For (≤): the exact handling of `c' > ⨅ threshold ⟹ ∃ i, threshold_i ≤ c'` over a Fintype Nonempty
     ⨅ (iInf attained — which Mathlib lemma, e.g. ciInf / Finset.exists_... / le_ciInf), and the strict/non-strict
     boundary (cover_ge_div takes `threshold_i ≤ c'`; the ⨅ < c' gives some `threshold_i < c'` ⟹ ≤). Is `≤` in cover_ge_div the right boundary or should it be `<`?
  4. The single HARDEST sub-step + whether it should be factored into a separate lemma.
  5. Any field of IsRouteMCover that is mis-stated for the proof to go through (e.g. should cover_le's RHS
     box be unitBox or a signed box; should cover_ge_div quantify differently)?
  Under ~500 words. Mark inference vs. fact; don't invent Mathlib lemma names (flag "verify" if unsure).
</output_contract>

<grounding_rules>
  The listed library lemmas + monomialThreshold/monomialIntegrand defs are FACT. rlctAtOn F 0 = sSup of
  admissible exponents (weightedThreshold). Flag any additional Mathlib lemma as "verify". Distinguish
  "this closes it" from "needs a glue lemma".
</grounding_rules>
