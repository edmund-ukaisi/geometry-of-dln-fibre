<task>
Lean 4 + Mathlib v4.29. I must build ONE module establishing the ORBIT O_M as an irreducible
affine variety, headline `(MvPolynomial.vanishingIdeal k O_M).IsPrime`, with ZERO sorry/axiom.

SETTING (all PROVED, available):
- `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`, `[Field k] [IsAlgClosed k]`.
- `BaseChangeGroup d := ∀ v : Fin (N+1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ` (units = GL).
- action `(P • A) i = P_{i.succ} * A_i * (P_{i.castSucc})⁻¹` (a `MulAction`).
- `RepCoord d := Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)` (Finite).
- `canonicalCoord d : Tuple d ≃ (RepCoord d → k)`, `canonicalCoord d A ⟨i,r,c⟩ = A i r c` (linear entry-flatten).
- L0 dictionary (PROVED): `MvPolynomial.vanishingIdeal`/`zeroLocus`, `mem_vanishingIdeal_iff`,
  `vanishingIdeal_isRadical`, `isZariskiIrreducible_iff_isPrime_vanishingIdeal`
  (`IsZariskiIrreducible Z ↔ (vanishingIdeal Z).IsPrime`, where `IsZariskiIrreducible Z` :=
   `IsIrreducible (pointToPoint '' Z)` in `PrimeSpectrum`), `MvPolynomial.funext` (infinite domain).
- Mathlib bricks confirmed present: `RingHom.ker_isPrime [IsDomain S] (f) : (ker f).IsPrime`;
  `IsLocalization.isDomain_of_le_nonZeroDivisors`; `IsLocalization.Away.surj`;
  `IsLocalization.mk'_eq_zero_iff`, `to_map_eq_zero_iff`; `Matrix.mul_adjugate : A * adjugate A = det A • 1`;
  `Matrix.adjugate`, entries are polynomials in entries of A.

TARGET (L1, the recon judged "one module, bricks present" but flagged two sub-steps as possibly heavier):
  Define `O_M := canonicalCoord d '' { A | ∃ P : BaseChangeGroup d, P • M = A }`.
  Define orbit map `μ_M : BaseChangeGroup d → (RepCoord d → k)`, `P ↦ canonicalCoord d (P • M)`, so `range μ_M = O_M`.
  Define `𝒪(G_d)` = coordinate ring of G_d = `Localization.Away (∏_v det P_v)` of `MvPolynomial (entry-index) k`,
    a DOMAIN (entries free vars; inverse via adjugate/det).
  Define pullback `μ_M^* : MvPolynomial (RepCoord d) k → 𝒪(G_d)` (aeval sending coord var ⟨i,r,c⟩
    to the (r,c) entry of P_{i+1} M_i P_i⁻¹, the inverse entries = adjugate/det in the localization).
  Prove `vanishingIdeal (range μ_M) = RingHom.ker μ_M^*` (a poly vanishes on the image iff its pullback is 0;
    ⟸ trivial by point-eval; ⟹ via localization-element-vanishing-on-dense-open-D(∏det) + MvPolynomial.funext).
  Then `(vanishingIdeal O_M).IsPrime` = `ker into domain prime`.

I have analysed the ⟹ direction as bounded (no absent sub-library): μ_M^*(g) = mk'(h, (∏det)^n) by Away.surj;
h·∏det vanishes everywhere (0 on V(∏det), = g(μ_M P) = 0 on D(∏det)) ⟹ funext ⟹ h·∏det = 0 ⟹ (domain) h = 0
⟹ mk'(h,·)=0. The friction I foresee: (a) building μ_M^* with the per-vertex Sigma-typed entry-variable
indexing across ∏_v GL_{d_v} of VARYING sizes d_v; (b) the adjugate-over-det inverse entries as localization
elements and proving P_v · P_v⁻¹ = 1 matches the action's unit-inverse; (c) evaluating localization elements at
group points to run the vanishing argument; (d) the set-equality `range μ_M = O_M`.
</task>

<output_contract>
1. ROUTE VERDICT: is my localization-pullback route the right one, or is there a materially cheaper route to
   `(vanishingIdeal O_M).IsPrime` in Mathlib v4.29 (e.g. via continuous-image-of-irreducible / closure, or
   reusing `isZariskiIrreducible_iff_isPrime_vanishingIdeal` more directly)? If cheaper, name the exact lemmas.
2. The SINGLE hardest sub-step, and whether it needs a genuinely-absent Mathlib sub-library (name it) or is
   just friction.
3. A rough LoC band (e.g. 200-300 / 400-600 / 600+) and whether this is honestly "one module" or a sub-ladder.
4. The cleanest way to dodge friction (a)-(d) above, if any — especially whether I can AVOID the explicit
   adjugate-entry construction (e.g. by carrying P⁻¹ entries as SEPARATE free variables + the relation
   det·(stuff)=1, or a different model of 𝒪(G_d)).
Be concrete with Mathlib v4.29 lemma names. Flag inference vs. fact.
</output_contract>

<grounding_rules>
Flag any lemma name you are not sure exists at the v4.29 pin as "GUESS — verify". Distinguish
"this is standard and present" (fact) from "this probably exists / would need proving" (inference).
</grounding_rules>
