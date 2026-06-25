<task>
I am fidelity-auditing a Lean 4 + Mathlib proof. Verify the PROOF SHAPE is sound and the
STATEMENT faithfully encodes the informal mathematics. Do NOT trust the prose; reason from the
Lean.

INFORMAL CLAIM: For the trivial deep-linear network H=(1,1,1) (two 1x1 scalar layers c1=A 0 0 0,
c2=A 1 0 0), target B=0, the loss is dlnLoss A = (c1*c2)^2. The real log-canonical threshold
(Aoyagi Def 1, integral-supremum form: sup of exponents c for which |F|^{-c} is locally integrable
near the deepest point) at the origin equals 1/2.

DEFINITION of rlctAt (Lean):
  rlctAt H F wstar := sSup { c : ENNReal | ∃ c' : NNReal, c = (c' : ENNReal) ∧
      ∃ U ∈ 𝓝 wstar, IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) U volume }

THE THEOREM PROVEN:
  rlctAt (1,1,1) (dlnLoss (1,1,1) 0) deepest111 = monomialThreshold 2 (1,1) (0,0)   [= 1/2]
where deepest111 = (fun _ => 0) is the origin.

PROOF STRATEGY (the part to red-team):
1. monomialThreshold 2 (1,1) (0,0) = 1/2 is proven separately (axiom-free, via Mathlib's
   intervalIntegral.integrableOn_Ioo_rpow_iff: IntegrableOn (·^s) (Ioo 0 t) ↔ -1 < s).
2. unfold rlctAt. Prove the admissible set equals { c | ∃ c':NNReal, c=c' ∧ (c':ℝ) < 1/2 }, then
   sSup of that = 1/2.
3. The set equality (hset) is proven by ext + two directions:
   FORWARD: given ARBITRARY U ∈ 𝓝 (origin) with |dlnLoss|^{-c'} integrable on U, derive c' < 1/2.
     - transport integrand to |x*y|^{-2c'} on R^2 via measure-preserving homeomorphism
       entryME : Params(1,1,1) ≃ᵐ R×R  (= paramsEquivFlat ≫ finTwoArrow).
       Uses U = entryME⁻¹(entryME '' U) [injectivity] and integrableOn_comp_preimage.
     - entryME '' U ∈ 𝓝 (0,0) [forward image of nbhd under homeomorphism].
     - extract a symmetric box [-ε,ε]² ⊆ entryME '' U  (sup metric).
     - integrable on [-ε,ε]² ⟹ c' < 1/2  via prodBoxSymm_rpow_integrableOn_iff (forward).
   REVERSE: given c' < 1/2, exhibit U = entryME⁻¹((-1,1)²) ∈ 𝓝(origin), integrable there
     via prodBoxSymm_rpow_integrableOn_iff (reverse) on [-1,1]² then mono_set Ioo⊆Icc.

KEY transport identity (integrand_eq_comp):
  |dlnLoss A|^{-c'} = |x*y|^{-2c'} ∘ entryME, justified by dlnLoss=(c1c2)^2 and
  |t^2|^{-c'} = |t|^{-2c'}, and c1*c2 = (entryME A).1 * (entryME A).2 (product preserved by the flattening).
</task>

<output_contract>
Three sections, terse:
1. STATEMENT FIDELITY: Does rlctAt as defined faithfully capture Aoyagi Def 1's
   integral-supremum RLCT? Flag any gap (e.g. restricting c'≥0 via NNReal; the "some neighbourhood"
   existential vs a fixed bump; sSup vs sup; ENNReal codomain). Is "= 1/2" the correct RLCT for
   (c1c2)^2 at 0 in R^2? Sanity-check the exponent: ∫∫ |xy|^{-2c} dx dy near 0 converges iff c<1/2 — verify.
2. PROOF-SHAPE SOUNDNESS: Is there a vacuous/missing direction? Does the FORWARD direction
   genuinely quantify over ALL neighbourhoods (the gate against under-counting admissible c)? Any
   way the set-equality could be hollow? Is prodBoxSymm used in the right direction each branch?
3. VERDICT: sound / specific-hole. If hole, give the minimal concrete counterexample or fix.

Mark each claim as [INFERENCE] or [FACT-from-given]. Do not invent Mathlib lemma behavior; if you
must assume a lemma's statement, say so.
</output_contract>

<grounding_rules>
You have only the text above, not the repo. Flag inference vs fact. If the soundness depends on a
Mathlib lemma whose exact statement you cannot verify, say which lemma and what it would need to say.
</grounding_rules>
