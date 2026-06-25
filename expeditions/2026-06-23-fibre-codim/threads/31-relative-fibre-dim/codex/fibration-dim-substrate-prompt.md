<task>
Design, as an independent commutative algebraist, the CLEANEST varietyDim-native Lean-4 + Mathlib
(pin v4.29) proof of a SPECIAL-CASE relative/fibration dimension theorem for a CONSTANT-ISOMORPHIC-FIBRE
surjection. Adjudicate which Mathlib v4.29 substrate to lean on. The homogeneity (all fibres isomorphic)
is the lever that makes this tractable WITHOUT general Chevalley / upper-semicontinuity — design the
proof to exploit exactly that. Do NOT rubber-stamp; argue from the algebra and name v4.29 lemmas.
</task>

<context>
Affine setup over an algebraically closed field k, char 0. Rep_d = ⊕ Mat (composable matrix tuples).
mult : Rep_d → Mat_{p×q} the iterated matrix product (a polynomial/regular map). Loci:
- Σ^r := {A | rank(mult A) = r}  (EXACT-rank locus; reducible in general).
- Mat^{=r} := rank-exactly-r matrices (a SINGLE GL_p×GL_q orbit, irreducible, smooth, dim δ = r(p+q−r)).
- F := mult⁻¹(E), E a fixed rank-r normal form (the fibre; REDUCIBLE in general — anchor (3,3,3),r=1:
  F has irreducible components of dims 10,9,9, NON-equidimensional).
- δ := r(p+q−r) = dim Mat^{=r}.

varietyDim Z := (ringKrullDim (MvPolynomial(coords) / vanishingIdeal Z)).unbotD 0 — Krull dim of the
SET-LEVEL coordinate ring (vanishingIdeal is radical by construction; varietyDim = dim of the Zariski
closure as a reduced set = max over irreducible components).

TARGET THEOREM:
   varietyDim Σ^r = varietyDim Mat^{=r} + varietyDim F   ( = δ + dim F ).

THE HOMOGENEITY LEVER (already formalized, green, LANDED):
- Σ^r = ⋃_{P ∈ H} (P • ·)'' F, H = GL_p × GL_q acting through the two endpoint vertices (inner units
  telescope away in mult). [productRankLocus_eq_iUnion_smul_fibre]
- mult is H-equivariant: mult(P • A) = P_N · mult(A) · P_0⁻¹. [mult_smul]
- EVERY fibre of mult over a rank-r point is H-isomorphic to F (G1: same rank ⟹ same fibre, an
  explicit regular iso A ↦ P•A). [codimRepCanonical_fibre_eq_of_rank_eq, image_smul_fibre]
- Mat^{=r} is a SINGLE H-orbit; H acts transitively on the base. So mult : Σ^r → Mat^{=r} is a
  surjection whose fibres are ALL isomorphic (the base is HOMOGENEOUS under H, and the total space is
  the H-sweep of one fibre). Fibre dimension is CONSTANT.

LANDED engine substrate I can reuse:
- varietyDim Mat^{=r} = δ. [DeterminantalStratumDim, via the N=1 single-orbit case]
- For an IRREDUCIBLE orbit closure Z_M: varietyDim Z_M = ringKrullDim((μ_M*).range) = trdeg, where
  (μ_M*).range is a subalgebra of a DOMAIN O(G), so ringKrullDim = trdeg (finite-type domain over k).
  [OrbitPullbackDim, JacobianTrdeg] — this is a DOMAIN/IRREDUCIBLE method.
- varietyDim is radical-insensitive; transports across coordinate-ring AlgEquiv even between different
  ambient spaces. [VarietyDimRadical: ringKrullDim_quotient_radical, varietyDim_eq_of_coordRingAlgEquiv,
  ringKrullDim_quotient_comap_ringEquiv]
- Reducible catenary: for any nonempty subset, codimRep + varietyDim = card (ambient dim).
  [RadicalCatenary: height_add_ringKrullDim_quotient_eq_card_of_ne_top]
- Mathlib v4.29 CONFIRMED PRESENT: MvPolynomial.ringKrullDim_of_isNoetherianRing
  (dim(MvPolynomial ι R) = dim R + card ι, finite ι, any Noetherian R); trdeg_add_eq (tower additivity,
  needs the TOP ring NoZeroDivisors = a DOMAIN); IsLocalization.orderIsoOfPrime;
  AtPrime.ringKrullDim_eq_height.
- Mathlib v4.29 CONFIRMED ABSENT: ringKrullDim(A ⊗_k B) = dim A + dim B; trdeg-of-tensor-product;
  packaged ringKrullDim_localization; general Chevalley fibre-dimension / upper-semicontinuity;
  relative Noether normalization over a domain (only field-base Noether normalization present).

THE REDUCIBILITY OBSTRUCTION (the crux to design around): both Σ^r and F are REDUCIBLE, so the
domain method (varietyDim = trdeg) does NOT apply to them directly — O(Σ^r), O(F) have zero divisors.
trdeg_add_eq needs the TOP ring to be a domain (irreducible). The homogeneity lever must be used to
REDUCE to the irreducible/domain case component-wise, OR to give a chain/Krull-dim argument that does
not need a domain.
</context>

<questions>
Adjudicate the candidate substrates for the cleanest varietyDim-native proof at v4.29. For EACH, say
present-or-absent at v4.29 (name lemmas), and whether the homogeneity lever lets it dodge the
reducible obstruction:

(i) ORDER/KRULL-DIM CHAIN BOUNDS: bound ringKrullDim(O(Σ^r)) by chains. Total chains ↔ base chains +
    fibre chains. Is there a clean Mathlib chain/`Order.krullDim`/`ringKrullDim` going-up + going-down
    pair that gives `dim total = dim base + (max over fibre dims)` for a surjection with closed fibres?
    Does it need flatness/going-down (which mult lacks globally)? Can homogeneity supply going-down on
    the open exact-rank locus?

(ii) TRDEG-ADDITIVITY IN THE TOWER k ⊆ K(base) ⊆ K(total), COMPONENT-WISE: take ONE top irreducible
    component Σ_0 of Σ^r (so varietyDim Σ^r = max = varietyDim Σ_0 if Σ_0 is top-dim). Σ_0 is
    irreducible ⟹ O(Σ_0) is a DOMAIN ⟹ trdeg_add_eq APPLIES to the tower k ⊆ K(Mat^{=r}) ⊆ K(Σ_0)
    (mult|Σ_0 dominant onto the irreducible Mat^{=r}). Then dim Σ_0 = dim Mat^{=r} + relative_trdeg, and
    the homogeneity (constant fibre) should identify relative_trdeg with dim F_0 (a top component of F).
    QUESTIONS: (a) Is trdeg_add_eq's field-tower version present and applicable here? (b) Does
    homogeneity let you identify relative_trdeg = dim(fibre over the generic point of Mat^{=r}) = dim F_0
    WITHOUT generic flatness — purely because all fibres are isomorphic? (c) The bookkeeping: does
    "max over Σ^r components = δ + max over F components" follow cleanly, given each top Σ-component is
    H-sweep of a top F-component? Is THIS the cleanest route?

(iii) SPEC-TOPOLOGY going-down / localization_away_comap_range: model the fibration on the principal
    open detΔ≠0 chart, use Spec-level comap-range/going-down. Present at v4.29? Cleaner than (ii)?

(iv) ANYTHING ELSE: e.g. realize Σ^r-chart as a localized polynomial extension O(F)[δ vars]_loc and use
     ringKrullDim_of_isNoetherianRing directly (the +δ is then landed Mathlib). Does the homogeneity /
     gauge make O(Σ^r ∩ chart) ≅ O(F)[δ free vars]_loc, sidestepping trdeg entirely? Is the +δ then a
     one-liner from the present poly-Krull-dim lemma + a localization-no-drop lemma?

ALSO: the localization-preserves-top-dim sub-lemma ("non-empty open D(detΔ) of an irreducible component
carries its dimension") — where does it sit in your chosen route, and what is its cheapest v4.29 proof?
</questions>

<output_contract>
- CHOSEN SUBSTRATE (one line): which of (i)-(iv) is cleanest AND present at v4.29, and the one-sentence why.
- The proof STRATEGY in 4-8 named steps, each labelled LANDED (engine) / Mathlib-present (name the lemma)
  / MUST-BUILD. Exploit the constant-isomorphic-fibre homogeneity explicitly — say WHERE it enters and
  what it buys (which general theorem it lets you avoid).
- The reducibility handling: exactly how the route reduces to the irreducible/domain case (component-wise
  max, or a chart that is a domain) — this is the make-or-break; be concrete.
- The localization-top-dim sub-lemma's place + cheapest route.
- The SINGLE biggest risk in the decomposition (the step most likely to need absent machinery).
- Honest sub-lemma count (~5-8). Distinguish FACT from INFERENCE; flag guesses about v4.29 contents.
</output_contract>

<grounding_rules>
- The make-or-break is the reducibility: O(Σ^r), O(F) are NOT domains, but trdeg_add_eq / the engine's
  varietyDim=trdeg method need a domain. Design the route so the homogeneity lever reduces to the
  irreducible case (component-wise) cleanly — or pick a substrate that never needs a domain.
- Name Mathlib v4.29 lemmas when you assert present/absent. Do not paste Lean you have not type-checked.
- Prefer the route with the FEWEST must-build pieces and the LIGHTEST absent-machinery exposure.
</grounding_rules>
