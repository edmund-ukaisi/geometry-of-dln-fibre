<task>
Lean 4 + Mathlib formalisation. I am about to formalise a "smooth-block certificate" / "standard-smooth local model" for a top-dimensional component of an affine variety (a fibre of a multiplication map). My brief (from a controller) says, loosely:

  "At a generic point of a top-dimensional component of the fibre, certify the standard-smooth
   local model: the Kähler/cotangent module Ω (equivalently the conormal/Jacobian module) is
   FREE of rank = codim there. Pin the rank to the proved codim."

I am worried the brief CONFLATES two distinct modules, and I want to lock down the precise, honest mathematical statement BEFORE building Lean infrastructure. Here is the exact situation:

GIVEN (all already PROVED, sorry-free, in my repo):
- k is an algebraically closed field (so perfect). A = a finite-type k-algebra = O(component) = the coordinate ring of one TOP-DIMENSIONAL irreducible component of the fibre. It is a finitely-presented DOMAIN over k.
- The component ring is generically SMOOTH: `Algebra.IsSmoothAt k I` holds at the generic point I (banked: isSmoothAt_sweepFibre_topComponent). Equivalently the component-quotient domain is smooth at its generic point ⊥.
- The fibre lives in an ambient affine space 𝔸^Ambient where Ambient = Fintype.card (RepCoord d) = number of polynomial coordinate variables.
- The geometric CODIMENSION of the fibre is PROVED in closed form:
    codim(fibre) = height(vanishingIdeal) = C + δ,  C = (cCodim d r).toNat,  δ = r·(d_N + d_0 − r).
  This is `codimRepCanonical_fibre_eq_cCodim_add_shift`. So codim is a proved number.
- I also have (banked, SmoothPointRegular.lean / SmoothLocalRelativeDimension.lean), for a finite-type k-algebra A and a MAXIMAL ideal m at which A is smooth:
    * a basic-open chart S = A[1/f] (f ∉ m) that IsStandardSmoothOfRelativeDimension n k S, with Ω[S⁄k] FREE of rank n = finrank S Ω[S⁄k];
    * Ω[A_m⁄k] free of rank n where n = ringKrullDim(A_m) (the LOCAL Krull dimension = relative dimension);
    * A_m is a regular local ring, and finrank κ(m) (m/m²) = n = ringKrullDim(A_m).

MY CONCERN: standard algebraic geometry says, for a smooth variety X ⊆ 𝔸^Ambient of dimension dim X:
  - Ω_{X/k} (the Kähler/cotangent module) is locally free of rank = dim X = RELATIVE dimension = Ambient − codim.
  - the CONORMAL module I/I² (equivalently coker/ker of the Jacobian) is locally free of rank = codim.
These are COMPLEMENTARY (their ranks sum to Ambient). So "Ω free of rank = codim" looks WRONG: Ω is free of rank = (Ambient − codim) = dim X, NOT codim. The thing free of rank = codim is the conormal/Jacobian module.

QUESTIONS:
1. Is my reading correct that the brief conflates Ω (rank = dim X = Ambient − codim) with the conormal module (rank = codim)? Or is there a convention under which "Ω free of rank = codim" is defensible? Be precise.
2. Given the banked machinery (smooth at a maximal ideal ⟹ Ω[A_m⁄k] free of rank = ringKrullDim(A_m); A_m regular; finrank κ (m/m²) = dim), what is the cleanest HONEST headline I should formalise that (a) is true, (b) genuinely pins a free-module rank to the PROVED codim number C + δ, and (c) is reachable? 
   In particular: to express "rank = codim" honestly I'd need rank(conormal) = codim, i.e. n_conormal = Ambient − dim(component) = codim. Is the cleanest route to instead state "Ω free of rank = dim(component) = Ambient − codim" (relative dimension), and SEPARATELY note dim(component) = Ambient − codim so codim is pinned? Or should I target the conormal module directly?
3. CRITICAL reachability subtlety: my smoothness fact is at the GENERIC point (prime I / ⊥), but the banked "Ω free + regular + dim" machinery is stated at a MAXIMAL ideal m (closed point). Generic smoothness of a domain over alg-closed k gives a DENSE smooth open, hence a smooth CLOSED point exists, and a free Ω there. Is stating the certificate at "some/a generic closed point of the smooth locus" (an existence statement: ∃ a maximal ideal m in the component ring, smooth, with Ω[A_m] free of rank = dim component = Ambient − codim) the honest and reachable target? Or is there a clean way to get the free-rank statement literally at the generic point ⊥ / the function-field level? Which is more faithful to "at a generic point of a top-dimensional component"?
4. Is `dim(component) = Ambient − codim` automatic, or does it need the component to be top-dimensional AND the ambient to be irreducible/equidimensional (affine space IS irreducible, so height + dim(quotient) = dim(ambient) holds for a prime in a polynomial ring over a field, by catenary/Cohen-Macaulay)? State the exact Mathlib-shaped fact I'd lean on (e.g. height p + ringKrullDim (R/p) = ringKrullDim R for a polynomial ring R over a field).

Keep it tight and concrete; I have the Mathlib v4.29 pin.
</task>

<output_contract>
Four numbered answers matching Q1–Q4. For Q1 a crisp verdict (conflation: yes/no + why). For Q2/Q3 give the SINGLE cleanest honest headline statement shape (in words + a Lean-ish signature sketch) you recommend, and name the complementary statement I should NOT overclaim. For Q4 name the exact dimension/height identity. End with a 2-line "biggest risk to fidelity" note.
</output_contract>

<grounding_rules>
Distinguish standard-math fact from your inference about my specific repo. If you are unsure whether a Mathlib lemma exists at v4.29, say "likely exists, verify name" rather than asserting a signature.
</grounding_rules>
