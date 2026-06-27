<task>
DECISIVE STRATEGIC VERDICT (not a repo analysis): pick the cleanest ∀M route for a determinant. Work the
ABSTRACT math yourself; do NOT explore a repository.

SETTING. A chart phi_M : R^N -> R^N for a deep-linear-network resolution, N = sum_k M_k M_{k+1}. The chart
is phi_M = paramsEquivFlat ∘ chartParamsGen(u, B_det), where chartParamsGen's L layer-matrices A_0..A_{L-1}
are produced by a chain recursion:
   C_L = u * Rfin            (leaf, u = the radial pivot scalar = x_p)
   C_k = Bmat_k * chainQ(N_k) + u * Rmat_k        (the Schur frame at boundary k)
   A_k = chainA(N_k, W_k, C_{k+1})                (the layer matrix = [C_{k+1} - N_k W_k ; W_k], a block stack)
Goal: |det D(phi_M)| = |x_p|^{m-1} * (spectator monomials), m = minAdm = sum_j r_j c_j (the achiever codim).

TWO ROUTES to the ∀M determinant (the math is settled; this is which Lean construction is cleaner over
OPAQUE dependent widths Text_k/Wext_k):

(i) FACTORIZATION  phi = Q_linear ∘ T,  T = composition of FLAT (R^N -> R^N) "pivotBlowupOn"/shear maps:
    - a radial pivotBlowupOn(active, p): coord p -> x_p, active coords j -> x_p*x_j, det |x_p|^{|active|-1}=|x_p|^{m-1};
    - per-boundary Schur shears (det 1) and b=aβ substitutions (pivotBlowupOn, spectator-monomial det);
    - Q_linear = paramsEquivFlat ∘ pack, a coordinate permutation (det 1).
    The KEY obligation is the bridge `chartParamsGen(u, B_det) = pack ∘ T` (the chain's layers EQUAL the
    explicit factored form). FACT: this route is proven on 4 small anchors (sizes N=6,8,21,27), but EACH
    used EXPLICIT per-coordinate vector tables for T and pack (e.g. T(x) = ![x0 - x1*x2, x4*x1, x2, ...]) and
    `fin_cases`/`ring` to prove the bridge. The ∀M lift must make T_M and pack_M WIDTH-PARAMETRIC functions
    of (M, the achiever path t*, the residual-block sizes r_j*c_j) and prove the bridge over opaque widths.

(ii) DIRECT CHAIN-DET: compute |det D(phi_M)| directly as the telescoping product of PER-LAYER block
    determinants of the chain itself, reusing a banked det engine: a monoid-hom telescope
    `|det (list.prod of full-ambient factors)| = prod of per-factor |det|`, where each factor is the
    fderiv of one boundary's contribution. The per-boundary block dets are banked: the Schur frame det
    `|det K|^{r+c}`, an LDU-core det, a unit-triangular chain det = 1, and the radial det |x_p|^{m-1}. No
    explicit T_M vector; the chart IS the chain, and its Jacobian is claimed to telescope per-layer.

QUESTIONS:
1. Which route's ∀M lift is cleaner over OPAQUE dependent widths? Specifically: does route (i)'s
   width-parametric T_M + the bridge `chartParamsGen = pack ∘ T_M` avoid or merely RELOCATE the
   dependent-width per-coordinate fight that the 4 anchors did explicitly? Is route (ii)'s per-layer
   det-telescope genuinely width-parametric (the det monoid-hom needs no Fin-cast), OR does it hide the same
   opaque-width difficulty in expressing the chart's fderiv AS a list-product of full-ambient block factors?
2. The deep obstruction for route (ii): the chart's fderiv D(phi_M) is the fderiv of a NONLINEAR map (the
   A_k are products/blocks of the read coordinates). For its determinant to telescope as a product of
   per-LAYER block dets, you must express D(phi_M) as a composition (list-product) of full-ambient CLMs whose
   dets are the known block dets. Is that decomposition itself a `composeFold = phi` bridge in disguise (the
   SAME obligation as route (i)), or is it genuinely different / easier? Reason carefully — both routes
   ultimately need "the chart equals a product of factors with known dets."
3. Given the 4 anchors ALL used route (i) (explicit-table factorization), is the ∀M-clean move to make the
   route-(i) T_M/pack_M parametric (so the bridge becomes ONE width-parametric funext via the banked
   chainA_apply_castAdd/natAdd entry laws), or to switch to route (ii)? Weigh: route (i) has 4 working
   templates but explicit tables; route (ii) is untested but might avoid the tables.
4. The active-set placement: F4 (banked) says keep CANONICAL FlatIdx order + a DECIDABLE `active : Finset`
   with active.card = m (NO per-M bijection e_M); pivotBlowupOn needs only active.card. CONFIRM this suffices
   for the radial |x_p|^{m-1} factor in the CHOSEN route, or name what extra it needs.
5. (3,3,3,3) worked check: minAdm=6, T*=(2,1,0), drops at all 3 boundaries. Sketch how the chosen route gives
   det = |x_p|^5 * spectators. (The banked anchor's answer is |u0|^5·|u1|^4·|u4|^2·|u9|^3 — note the
   spectator exponents from the per-boundary Schur/LDU factors.)
6. KILL-FLAG: if BOTH routes are persistent opaque-width walls (neither lands without an open-ended fight),
   say so sharply.
</task>

<output_contract>
- Q1: which route is cleaner over opaque widths; does (i) relocate or avoid the fight; is (ii) genuinely
  width-parametric. FACT vs INFERENCE.
- Q2: a SHARP analysis of whether route (ii)'s fderiv-as-list-product is the same bridge obligation as (i).
- Q3: a single recommendation (i parametric / ii) with the why, weighing 4-templates-but-explicit vs untested.
- Q4: confirm canonical-FlatIdx + active-Finset suffices for the radial, or name the gap.
- Q5: the (3,3,3,3) det sketch.
- Q6: clear yes/no on whether both are walls.
</output_contract>

<grounding_rules>
- Reason about the ABSTRACT construction; do NOT explore any repository or dump file contents.
- The banked facts (4 anchors via route (i) explicit tables; the det monoid-hom telescope; the per-boundary
  block dets schurFrame=|det K|^{r+c}, LDU, chainUnit=1, radial=|x_p|^{m-1}; chainA_apply_castAdd/natAdd entry
  laws; |active|=minAdm; canonical FlatIdx + active Finset) are FACTS.
- Be decisive — the goal is the route that LANDS in Lean over opaque widths, not the prettiest.
</grounding_rules>
