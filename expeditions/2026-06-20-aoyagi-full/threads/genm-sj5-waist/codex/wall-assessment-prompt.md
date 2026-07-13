<task>
Adjudicate a Lean-4/Mathlib (v4.29) FORMALISATION-REACHABILITY question. I do NOT want a re-derivation
of the mathematics (the math is scout-certified to close). I want an honest verdict on whether one
specific new brick is a BOUNDED formalisation or a genuine NEW-MODULE WALL, and whether there is a
cheaper route. Withhold nothing; adjudicate either direction (bounded / wall).

CONTEXT (a DLN-fibre RLCT project; deep linear networks). We must prove finiteness of a box integral
below a threshold for the "WAIST" case of a 3+-width chain M = (M0, M1, M2, ...). Concretely the target
(hole c) is: for a chain M : Fin (L+3) -> N in the WAIST regime M1 < min(M2,...,Mlast), with M1 >= 2,
a "decorated" box integral I(c') = INT over parameter box of (jac monomial) * decLoss^{-c'} is finite
for all c' < (1/2) * minAdm M. There is a decorated strong induction hypothesis available (finiteness
for every admissible decoration of every ONE-LAYER-SHORTER chain).

The scout's mathematical route (route-A "SVD-qPeel", certified CLOSES-LABOUR by exact arithmetic +
decorrelated Codex) is, at L=0 (3-width chain (x,s,z), A0 is x*s, A1 is s*z, s<=z):
  ||A0 A1||_F^2 = sum_{j=1}^s sigma_j^2 * ||A0 u_j||^2   (spectral/SVD of the deep layer A1)
  -> change variables A1 -> (sigma, U, V) with rectangular-SVD Jacobian
     dA1 ~ prod_{i<j}|sigma_i^2 - sigma_j^2| * prod_j sigma_j^{z-s} dsigma dU dV
  -> Weyl majorant on the ordered chamber: prod_{i<j}|sigma_i^2 - sigma_j^2| <= prod_j sigma_j^{2(s-j)},
     giving monomial powers h_j = z+s-2j
  -> integrate out frames U in O(s), V in Stiefel V_s(R^z); the A0-integral is O(s)-invariant
  -> banked corner engine qPeelIntegral (finite for c' < (1/2) sum_j(h_j+1) under gate h_j <= m_j)
  -> charge identity sum_{j=1}^s min(x, z+s+1-2j) = minAdm(x,s,z) makes threshold = (1/2) minAdm, TIGHT.

A read-only Mathlib recon (v4.29, rev 8a17838) established, with rg-level certainty:
  BANKED (project or Mathlib): step 1 loss identity (frobSq_mul_eq_sum_eigenvalues via the Gram spectral
    theorem, no SVD needed); step 3 A0-frame integration (exists_ortho_ext + a measure-preserving
    orthogonal right-mult CoV; sidesteps Haar-on-O(s) on the A0 side); step 5 qPeelIntegral_lt_top
    (complete, sorry-free); step 6 shell cover (weakEigCount/singularShell/lintegral_le_sum_finCover);
    the general diffeomorphism CoV MeasureTheory.Function.Jacobian (the scaffold only).
  GENUINELY ABSENT from Mathlib (rg-confirmed 0 hits): eigenvalue-map Jacobian / prod|lambda_i-lambda_j|
    Vandermonde density; Wishart / random-matrix eigenvalue density; rectangular-SVD parametrisation
    measure (A -> (sigma,U,V) CoV); Weyl integration formula; coarea formula; eigenvalue-map
    continuity/differentiability (A -> eigenvalues A as HasFDerivAt); Haar on O(s); Stiefel manifold
    V_s(R^z) (only the unit-sphere manifold instance exists).

So the ONE genuinely-new brick is step 2 (the A1-eigenvalue-marginal DENSITY / Jacobian). NB: the EASY
s=1 sub-case (||A0 A1||^2 = ||A0||^2 ||A1||^2, product of two Morse integrals, no density) is a SEPARATE
hole (M1=1), NOT this target. This target is exactly s = M1 >= 2, the case that NEEDS step 2.

The recon flagged a cheaper alternative to the literal SVD/Wishart density:
  route (c): peel A1's OWN corank one direction at a time by a Schur-complement chart ON A1 (pivot its
  invertible k*k block; the Schur complement is a rational/polynomial map, Jacobian = a det(pivot)-power,
  amenable to MeasureTheory.Function.Jacobian); depth <= s recursion, bottom leaves are s=1-like,
  qPeelIntegral consumes the freed blocks. Reuses banked Jacobian CoV + qPeel + shell cover; NEW = the
  deep-layer Schur charts (structurally close to banked FRONT-factor Schur charts, roles swapped) + the
  flag-recursion bookkeeping. Recon's kill-condition: "if a rank-2 (s=2, e.g. (3,2,3)) deep-layer Schur
  chart cannot be written as a MeasureTheory.Function.Jacobian CoV with a det-power Jacobian in one
  module, route (c) is not moderate and the SVD density (HEAVY) is forced." That deciding worked chart
  has NOT been done.

Also: for L>=1 the "deep layer" is a PRODUCT (not a single matrix), so it does not SVD into free blocks;
the intended general-L handling is an arity recursion peeling >=4-width chains toward a 3-width leaf,
using reversal CoV I(M)=I(reverse M) to orient to a good end. BUT a separate scout cert REFUTED
"peel the better end" as a COMPLETE cover: the palindrome (2,1,2) is head-split-divergent from both ends,
and >=4-width chains, though top-good from an end, are transitively FORCED into 3-width waist leaves. So
reversal alone does not discharge general-L waists; the 3-width SVD-qPeel must be a genuine BASE case and
the recursion must reach it.

<output_contract>
Answer in <= 6 short sections, ranked, fact-vs-inference tagged:

1. VERDICT on step 2 (the deep-layer eigenvalue-density brick) at Mathlib v4.29: BOUNDED-PLUMBING /
   MODERATE-NEW-MODULE / HEAVY-NEW-MODULE-WALL. One sentence why.

2. The cheapest reachable route for s>=2 (rank the candidates): (i) literal rectangular-SVD/Wishart
   density; (ii) deep-layer polynomial Schur-flag recursion (route c); (iii) something else I have not
   named. For the top pick, name the SINGLE hardest Lean sub-obligation and whether Mathlib v4.29 has the
   primitive (be concrete: which lemma/typeclass, or "absent").

3. The (3,2,3) deciding chart: is the rank-1 deep-layer Schur chart on A1 (2x3) writable as ONE
   MeasureTheory.Function.Jacobian CoV with a det(pivot)-power Jacobian? Sketch the map + Jacobian, or
   say why not. This decides route (c)'s difficulty label.

4. General-L: given route-B ("peel the better end") is refuted, is there a SOUND reduction of a general-L
   waist to the 3-width SVD-qPeel base via the arity recursion (the decorated one-shorter IH)? Or is
   there a hidden obstruction (e.g. the deep-layer product's rank stratification needs its own nested
   resolution that does not bottom out)? Flag inference vs fact.

5. Is the charge identity sum_{j=1}^s min(x, z+s+1-2j) = minAdm(x,s,z) (for s<=z; 0 violations over 936
   triples) the right ELEMENTARY de-risking first layer to build now, or is there a better first target
   that unblocks more? A clean proof idea for it (min-of-parabola gCrux = sum-of-capped-arithmetic-series)
   in <= 4 lines would help.

6. The single cheapest test/computation that would most reduce my uncertainty on the step-2 difficulty
   label before I commit a formalisation tide.
</output_contract>

<grounding_rules>
Distinguish FACT (you can derive it or it is standard) from INFERENCE (Mathlib-availability guesses).
For any Mathlib lemma you cite as existing at v4.29, tag it [likely-exists] vs [confirmed-recall] — I
will verify before use. Do NOT claim a Mathlib primitive exists to make a route look bounded; if you are
unsure it exists, say so and treat it as absent for the verdict. The math closing is NOT in question;
only Lean-v4.29 reachability + the cheapest route.
</grounding_rules>
