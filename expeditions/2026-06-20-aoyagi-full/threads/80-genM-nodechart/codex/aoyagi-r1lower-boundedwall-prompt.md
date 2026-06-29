<task>
I am adjudicating ONE truth-value for a Lean 4 + Mathlib formalisation expedition: is the
"general-M achiever-path box-divergence" leg BOUNDED (a large but standard build, decomposable
into pieces with no new mathematics) or a genuine WALL (needs new math / an operator scope
decision)? I need a decorrelated second opinion. Reason from the structure I give you; flag
inference vs. what you can actually verify.

## The mathematical setting
A deep linear network with layer-width vector M = (M_0,...,M_L). The "route-M" loss is a
sum-of-squares of the entries of a product of L matrices. We resolve its singularity at the
"deepest achiever point" by a chart phi : box -> flat-parameter-space, and need the box integral
  ∫_{[-ε,ε]^N} |routeMCore M (x)|^{−c'} dx = +∞   at the threshold c' = (1/2)·minAdm(M),
for every ε>0. (This is the "divergence at the threshold" = codimension is ACHIEVED; it pairs with
a finiteness leg to pin the RLCT = (1/2)·minAdm.) minAdm(M) is a combinatorial quantity (a
layer-peeling recursion giving the codimension of the achiever stratum).

## What is ALREADY PROVEN (sorry-free) in the Lean codebase
1. An M-AGNOSTIC reduction theorem: given a structure `NodeAchieverChart M` that bundles
   - a chart map phi, a binding pivot axis p,
   - a Jacobian-exponent vector leafH with leafH(p) = minAdm(M)−1 (so the radial blow-up gives
     exponent minAdm−1 on the pivot),
   - a unit factor U with a compact bound + a.e.-positivity on the box,
   - the leaf-integrand identity (∏_j|u_j|^{leafH j})·|F∘phi|^{−c} = monomialIntegrand·U^{−c} (a.e.),
   - the change-of-variables `cov`:  ∫_{phi''(V\{u_p=0})} g = ∫_{V\{u_p=0}} ofReal(∏_j|u_j|^{leafH j})·g(phi u),
       i.e. the chart's Jacobian is the PURE MONOMIAL |det Dphi| = ∏_j |u_j|^{leafH j},
   - image containment (small source box maps into the cube),
   THEN the box divergence follows. (Proven; uses one cited normal-crossing→RLCT axiom for the
   monomial integral.) So the ENTIRE leg reduces to: construct a `NodeAchieverChart M` for arbitrary M.

2. The RATE identity is proven ∀M: routeMCore M (phi x) = (x_p)²·U(x), single radial pivot,
   decoder-agnostic. The monomial-determinant TELESCOPING engine is proven ∀M (|det of a List.prod
   of full-ambient endos| = ∏ per-factor dets — but the per-factor dets are HYPOTHESES, the engine
   does not produce them). The interior `Ubound` (a.e.-positivity) is proven for the interior-drop
   class. The boundary-CLEAN branch is FULLY proven sorry-free (its chart is a single-pivot
   polynomial radial blow-up, so cov is the generic pivotBlowupOn lemma).

3. FOUR concrete anchors are proven sorry-free end-to-end through the reduction: M=(2,2,2),
   (3,3,4), (4,4,2,2), (3,3,3,3). The (3,3,3,3) interior anchor has |det Dphi| =
   |u0|^5·|u1|^4·|u4|^2·|u9|^3 (FOUR weighted axes), via an LDU coordinatization of each Schur K-core
   so each det K_s becomes a MONOMIAL in LDU-pivot coords.

## The gap (the question)
The leg is a 4-way case split on M's descent structure:
  - L=1: pure radial — banked.
  - BOUNDARY-CLEAN (deepRank = deepRows): single-pivot polynomial radial — DONE sorry-free ∀M.
  - BOUNDARY-SMEARED (deepRank < deepRows): RATIONAL single-pivot chart (divides by a Gram minor,
    pole on a null set). Instances (1,2,1)/(1,3,2)/(2,3,1) done; ∀M needs a rational-pole change-of-
    variables transport whose Lean interface (a.e.-analytic off a null set) is UNCONFIRMED for the
    rational map.
  - INTERIOR (an interior boundary drops BOTH row and col rank): the heaviest. The Schur-frame K-core
    blocks are FREE coordinates, so |det Dphi| = ∏_s |det K_s|^{r_s+c_s} is MULTI-AXIS and
    construction-sensitive (no uniform closed-form leafH across the family). The cov field demands a
    PURE MONOMIAL determinant, but det K_s is a POLYNOMIAL (e.g. z1·z4−z2·z3). The (3,3,3,3) anchor
    fixed this by LDU-coordinatizing each K-core (det K = ∏ LDU pivots = monomial). The general
    interior chart must do the same ∀M: (i) LDU-coordinatize genBlk's K-cores over opaque
    variable-length widths; (ii) prove the "map equality" that the structured chart EQUALS a
    composeFold of [radial, schurFrame_s, lduCore_s, ...] over the variable-length descent path —
    this is the dependent-Fin-cast bottleneck; (iii) the multi-axis leafH; (iv) injOn off the
    weighted-axis planes + the n-fold null-slice cov.

## The decoder-fidelity trap (the reason I am paranoid)
There are MULTIPLE candidate "decoders" (concrete realizations of phi). A free-K decoder
(`phiFlatStructV`, readK = free coords) has Jacobian ∏_s|det K_s|^{r_s+c_s} — a degree-t POLYNOMIAL
per core — so its monomial-cov field is UNSATISFIABLE for cores of size t≥2. A "dead-leaf" decoder
(Rfin:=0) gives the WRONG determinant exponent (interior-E-block-count, not minAdm−1). Only an
"active-center / live-leaf" decoder, LDU-coordinatized, gives both the correct minAdm−1 threshold
AND a monomial det. The recent build trail shows ~5 spec-first catches where a green/sorry-free
contract was found to carry an UNSATISFIABLE cov hypothesis for t≥2 cores. So any "BOUNDED" verdict
must confirm the monomial-det cov is satisfiable for the LDU-coordinatized live decoder ∀M, not just
at the t=1 anchors.

Two prior decorrelated checks exist: (A) an exhaustiveness worry — is the 4-way split provably total?
The trichotomy is proven only modulo an unproven hypothesis deepRank(M) ≤ deepRows(M) ∀M (the widths
are noncomputable argmins, not decide-reducible). (B) the smeared rational-cov interface gap.

<output_contract>
Respond in EXACTLY these sections, terse:

1. VERDICT: one of {BOUNDED, WALL, BOUNDED-WITH-NAMED-RISK}. One sentence.

2. THE INTERIOR MONOMIAL-DET COV — is the LDU-coordinatization of K-cores over variable-length
   opaque widths a BOUNDED build or does it hide new math? Specifically: is "det K_s = ∏ LDU pivots
   = monomial" robustly available ∀M (every K-core admits an LDU factorization with the pivot
   monomial det realized in chart coordinates), or is there a degeneracy (zero pivot / non-generic
   core) that breaks the monomial form on a non-null set? Rank this as the #1 risk or not.

3. THE MAP-EQUALITY (phiStructured = composeFold over opaque variable-length widths) — is this
   "just" a dependent-cast engineering build (bounded), or could the structured chart and the fold
   FAIL to be equal as maps for some M (a genuine obstruction)? What is the single cheapest
   discriminating test short of the full build?

4. THE TWO PRIOR RISKS (exhaustiveness deepRank≤deepRows ∀M; smeared rational-cov interface) — for
   each, BOUNDED or WALL, one line.

5. THE TRAP: the single most likely way a BOUNDED verdict here is WRONG.

6. If BOUNDED-WITH-NAMED-RISK: name the ONE piece an operator scope decision should weigh.
</output_contract>

<grounding_rules>
You cannot see the repo. Mark every claim [Inference] (from the structure I described) or
[Repo-contingent guess] (depends on Lean details you can't verify). Do NOT assert that a specific
Lean lemma exists or compiles. The diagnosis (bounded-vs-wall reasoning) is what I am buying, not code.
Be willing to say "I cannot discriminate without X."
</grounding_rules>
