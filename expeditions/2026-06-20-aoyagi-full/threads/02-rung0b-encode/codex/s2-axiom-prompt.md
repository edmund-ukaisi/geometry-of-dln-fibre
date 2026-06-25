# Red-team: the single cited axiom (S2) for an RLCT formalisation in Lean 4 + Mathlib

I am formalising Aoyagi's exact learning coefficient (real log-canonical threshold, RLCT) for deep
linear networks. The whole development proves everything from scratch EXCEPT one cited analytic fact
(Hironaka/Watanabe normal-crossing → RLCT extraction), stated as the single permitted `axiom`. I need
your independent judgment on whether my Lean statement of this axiom is FAITHFUL to the cited fact and
MINIMAL (cites only the irreducible monomial-integral content, nothing more), and whether it is
NON-VACUOUS (the hypotheses are satisfiable, the conclusion is not trivially true/false).

## The definitions already in place

```lean
-- Params H : composable real matrix tuples (a Pi of function spaces); has a MeasureSpace instance
--   = product Lebesgue measure on ℝ^N.  TopologicalSpace too.
-- rlctAt H F w* : ℝ≥0∞ := sSup { c : ℝ≥0∞ | ∃ c' : ℝ≥0, c = c' ∧
--                  ∃ U ∈ 𝓝 w*, IntegrableOn (fun w => |F w| ^ (-(c':ℝ))) U volume }
--   (Aoyagi Def 1, integral-supremum form; |F|^{-c}; bump dropped via ∃ U ∈ 𝓝.)
-- rlctOrderAt H F w* : ℕ  -- opaque placeholder (the analytic pole order θ; Mathlib lacks the
--   meromorphic continuation to define it directly; its value is pinned by THIS axiom).
```

## The cited fact (Aoyagi p.6, Hironaka extraction)

If a proper analytic π : Q → V resolves F to normal-crossing form on local coords (u₁,…,u_d):
K(π u) = unit(u)·∏_j |u_j|^{2k_j} (the function becomes a monomial times a nonvanishing unit), and
|det Dπ(u)|·φ(π u) = pos(u)·∏_j |u_j|^{h_j} (the Jacobian × bump is a monomial times a positive unit),
with k_j, h_j ≥ 0 integers, then
  λ = min over charts, min over axes j of (h_j+1)/(2k_j),  and
  θ = max over charts of #{ j : (h_j+1)/(2k_j) = λ }.
The irreducible per-axis fact: ∫_0^ε u^{h-2kc} du < ∞ ⟺ h - 2kc > -1 ⟺ c < (h+1)/(2k).

## My draft Lean axiom

I am tempted to state it abstractly with: a Fintype ι of charts; per chart a dimension d i and
exponent functions k i, h i : Fin (d i) → ℕ; the resolution maps φ i and the hypotheses that
(a) the chart images cover a neighbourhood of w* ∩ {F=0}, (b) each φ i is a proper analytic diffeo
onto its image, (c) on each chart F∘φ i = unit·∏|u_j|^{2 k i j} with unit nonvanishing, and
|det Dφ i|·(bump∘φ i) = pos·∏|u_j|^{h i j} with pos positive, (d) bump is C∞ compact-support, bump(w*)>0;
CONCLUSION: rlctAt H F w* = ⨅ i, ⨅ j, ((h i j)+1)/(2*(k i j))  (in ℝ≥0∞)
        AND rlctOrderAt H F w* = ⨆ i, (Finset.univ.filter (fun j => ((h i j)+1)/(2*(k i j)) = rlctAt H F w*)).card

## Questions

1. Is the conclusion `λ = ⨅ᵢ ⨅ⱼ (hⱼ+1)/(2kⱼ)` in ℝ≥0∞ the faithful form? Edge cases: a chart axis with
   k_j = 0 (the function is a unit in that direction). In ℝ≥0∞, (h+1)/(2·0) = (h+1)/0 = ⊤. Is taking
   that axis's ratio = ⊤ (i.e. it never binds the min) the correct behaviour? Should k_j=0 axes be
   excluded, or is ⊤ exactly right?
2. The bump appears in the Jacobian-monomial hypothesis (its exponent h_j absorbs the bump). But rlctAt
   has NO bump (it uses ∃ U ∈ 𝓝). Is it legitimate for the cited axiom to take bump data in its
   hypotheses yet conclude about the bump-free rlctAt? (My claim: φ-independence makes rlctAt = the
   bumped Def-1 value, and that φ-independence is a SEPARATE lemma S1 I prove; the axiom only cites the
   monomial extraction.) Is this a clean separation, or am I smuggling φ-independence into the axiom?
3. Is anything in my hypothesis list MORE than the irreducible monomial fact — i.e. am I citing the
   change-of-variables validity, the cover, or the properness when I should be PROVING those? The brief
   draws the cited line at "the chart-level monomial formula" only; cover + change-of-variables stay on
   my side (R1/S1). Does my axiom as drafted accidentally cite them?
4. The order conclusion `θ = ⨆ chart-count` rides inside this axiom (the analytic pole order = chart
   count is asserted here, since Mathlib can't define the analytic order). Is bundling the order into
   the same axiom sound, or does it over-extend the citation? (θ is explicitly the secondary deliverable.)
5. Is there a SIMPLER faithful statement? E.g. should I state the irreducible 1-D / monomial integral
   convergence criterion as the axiom and DERIVE the chart formula, rather than axiomatising the chart
   formula directly? Tradeoff: deriving needs change-of-variables + Fubini-type splitting (more of my
   own work but a smaller citation). Which is the better bedrock for a "one citation only" hero standard?
6. Any sign/convention hazard in the ratio (h_j+1)/(2k_j) or the pole at z=-λ that I should pin?

Give me your independent verdict per question (FAITHFUL / FAITHFUL-WITH-CAVEAT / NOT-FAITHFUL, plus the
fix). Withhold nothing; if my draft is over-citing, say exactly which hypothesis to drop or move.
