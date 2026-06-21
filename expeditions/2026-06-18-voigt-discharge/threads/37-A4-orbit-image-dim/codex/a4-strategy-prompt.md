<task>
I am formalising in Lean 4 + Mathlib v4.29 (toolchain leanprover/lean4:v4.29.0) the AG-half of a
deep-linear-network result. I need a STRATEGY review of the cleanest Mathlib-native formulation of a
multi-step "transcendence degree ≤ Jacobian rank" chain, BEFORE I sink time into wrong infrastructure.
I want your independent diagnosis of where the formalisation should be phrased to minimize from-scratch
field-extension Kähler theory.

SETTING (concrete objects, all LANDED and compiling in my library):
- k : a field. For the hard step, [CharZero k].
- B := groupRing d := Localization.Away (groupDenom d) of MvPolynomial (GroupCoord d) k. B is a DOMAIN
  (instance landed). GroupCoord d is a Finite Sigma type Σ v, Fin (d v) × Fin (d v).
- A k-algebra hom μ* := orbitPullback M : MvPolynomial (RepCoord d) k →ₐ[k] B, given as
  aeval (genericOrbitCoord M) where genericOrbitCoord M : RepCoord d → B picks out matrix entries of
  Pgen_{i+1} · M_i · Pgen_i⁻¹ (Pgen = generic invertible matrices; the inverse lives in B via adjugate/det⁻¹).
  RepCoord d is a Finite Sigma type. So the family f := genericOrbitCoord M : RepCoord d → B is a finite
  family in the domain B.
- (orbitPullback M).range : a subalgebra of B, a f.g. k-domain (instance landed). Call it Aimg.
- δ⁰ := deformationδ M M : C⁰ →ₗ[k] C¹, an explicit k-linear map between finite-dim k-vector spaces,
  φ ↦ (φ_{i+1} M_i − M_i φ_i)_i. finrank k (LinearMap.range (deformationδ M M)) is the target RHS.

THE CHAIN I must land (route c), with A0 already landed:
  A0 (landed): varietyDim(Z_M) = (ringKrullDim Aimg).unbotD 0.
  A4.1: (ringKrullDim Aimg).unbotD 0 = (Algebra.trdeg k Aimg).toNat  [char-free; Aimg f.g. domain].
  A4.2: (Algebra.trdeg k Aimg).toNat ≤ (generic Jacobian rank of f)  [CharZero; the hard one].
  A4.3: (generic Jacobian rank of f) = finrank k (LinearMap.range (deformationδ M M))  [char-free].
  A4.4: chain ⟹ (ringKrullDim Aimg).unbotD 0 ≤ finrank k (range δ⁰).

What I have CONFIRMED present in Mathlib v4.29:
- Algebra.trdeg (Cardinal), trdeg_add_eq (tower additivity, domain), trdeg_eq_zero [IsAlgebraic],
  MvPolynomial.trdeg_of_isDomain, IsTranscendenceBasis / exists_isTranscendenceBasis,
  trdeg_le_of_injective/surjective, AlgEquiv.trdeg_eq.
- KaehlerDifferential.mvPolynomialBasis (Ω[k[σ]/k] free on {dx}), mvPolynomialBasis_repr_apply (coords=pderiv),
  KaehlerDifferential.finite.
- Mathlib.RingTheory.Kaehler.JacobiZariski: Function.Exact lemmas: KaehlerDifferential.exact_mapBaseChange_map,
  Algebra.H1Cotangent.exact_δ_mapBaseChange, exact_δ_map.
- Algebra.FormallyUnramified.of_isSeparable (K L) [Algebra.IsSeparable K L] : FormallyUnramified K L.
  In Unramified/Field.lean. (FormallyUnramified ⟺ subsingleton Ω in the field-extension setting.)
- PerfectField.ofCharZero ; PerfectField ⟹ every algebraic extension separable.
- LANDED in my own Core: ringKrullDim_quotient_eq_noetherRank (gives, for a prime p of MvPolynomial (Fin n) k,
  an integral injective k[Fin s] →ₐ (R/p) and ringKrullDim (R/p) = s); first-iso Aimg ≃ₐ R/ker.

What is ABSENT (no named lemma): "rank Ω[L/k] = trdeg k L" for a field extension; any direct
"AlgebraicIndependent ↔ Jacobian rank" bridge.

KEY QUESTIONS (rank by leverage, give the single cleanest path for each):

1. A4.2 PHRASING. The certificate proof is: maximal alg-indep subfamily f_{i_1..r} of the f_i; r = trdeg;
   then in Ω_{K/k} (K = Frac B) the differentials {d f_{i_a}} stay K-linearly independent because for
   E = k(f_{i_a}) ⊆ K with K/E algebraic and char 0, the base-change map K ⊗_E Ω_{E/k} → Ω_{K/k} is
   INJECTIVE; hence r ≤ rank_K{d f_i}. QUESTION: what is the SINGLE cleanest Mathlib-native object for
   "generic Jacobian rank of f" so that A4.2 and A4.3 share it? Candidates:
     (a) rank over Frac(B) of the K-span of {d f_i} in Ω_{Frac(B)/k};
     (b) rank over B of the B-span of {d f_i} in Ω_{B/k} (B = groupRing, localization of poly ring);
     (c) the matrix rank of (pderiv_j (numerator stuff)) — messy because of the localization/inverse.
   Is working in Ω_{B/k} (B itself, NOT its fraction field) and using that B is a LOCALIZATION of a
   polynomial ring (so Ω_{B/k} is B-free on {dx_j} via KaehlerDifferential of a localization — does
   Mathlib have Ω of a localization is base-changed Ω?) enough, sidestepping the fraction field entirely?
   Or is the fraction field unavoidable for the "trdeg" comparison?

2. A4.2 SEPARABLE BASE CHANGE INJECTIVITY (the hardest sub-lemma). Does Mathlib v4.29's JacobiZariski
   exact sequence (KaehlerDifferential.exact_mapBaseChange_map for E → K → over k? or k → E → K?) plus
   Ω_{K/E} = 0 (from FormallyUnramified K/E ⟸ separable algebraic) give the injectivity of
   K ⊗_E Ω_{E/k} → Ω_{K/k} more cheaply than re-deriving it? Spell out the exact triple (R,S,T) to feed
   the exact sequence and which Function.Exact lemma yields injectivity, and what "Ω_{K/E} subsingleton"
   API discharges the cokernel/kernel term. Is there a subtlety that FormallyUnramified gives H1Cotangent
   or Ω subsingleton, and which one the exact sequence needs?

3. A4.3 WITHOUT A JACOBIAN MATRIX. Can I AVOID ever forming a pderiv matrix? Idea: define the "differential
   rank" as finrank of the k-linear (or B-linear) span of {d(f_i)} and prove DIRECTLY that the k-linear map
   "φ ↦ derivative of orbit map" equals δ⁰ via a Derivation/tangent argument, so that
   (generic Jacobian rank) = finrank(range δ⁰) is proved by exhibiting a linear iso of the two spans,
   rather than by an explicit pderiv computation of the adjugate/det⁻¹ entries. The certificate's
   "dμ_e = δ⁰" was checked symbolically. What is the cleanest Lean object identity that captures
   "differential of orbit map at identity = δ⁰" and connects to whatever rank object answer (1) picks?
   Is the constant-rank-under-G step (rank(dμ_P) independent of P) needed in this Ω/differential-span
   formulation, or does it dissolve once the rank object is the GENERIC (fraction-field / B-localization)
   rank rather than a pointwise one?

4. SCOPE TRIAGE. If A4.2's separable-base-change injectivity is the dominant cost, what is the smallest
   honest SCOPED LEMMA I can state it as (with a one-line note of the field-theory content) so that
   A4.1 + A4.3 + an A4.2-skeleton + A4.4-conditional all land green and sorry-free with the injectivity
   as the single clearly-named open obligation? Give the exact Lean signature you'd recommend for that
   scoped lemma.
</task>

<output_contract>
Four sections, headed Q1..Q4. For each: the single recommended path in 3-6 sentences, then a bulleted
list of the exact Mathlib lemma names / (R,S,T) instantiations / object definitions to use. End with a
"BIGGEST RISK" one-liner naming the step most likely to thrash and the cheapest fallback. Be concrete
about Lean v4.29 API; if you are unsure a lemma exists at that pin, say so and give the search term.
</output_contract>

<grounding_rules>
Distinguish "I know this Mathlib lemma exists at v4.29" from "this likely exists, verify by grep". Do not
invent lemma names with false confidence — flag every name you are not sure about. The diagnosis (which
object to phrase the rank as, and whether the fraction field is avoidable) is what I am buying; I will
verify every lemma locally before using it.
</grounding_rules>
