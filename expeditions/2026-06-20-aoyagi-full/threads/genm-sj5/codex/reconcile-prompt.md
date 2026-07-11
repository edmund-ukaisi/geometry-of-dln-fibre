<task>
An RLCT finiteness route adjudication (deep linear networks). Two candidate routes for ONE integral;
decide if they contradict or address different mechanisms, and whether the cheaper route genuinely closes
or relocates the hard part. Be adversarial — the burden is on the CHEAPER route (it reuses a majorant a
prior analysis flagged). HUNT the divergence; conclusion withheld.

THE INTEGRAL (to show < ∞ for c' < ½·minAdm(M), M=(3,3,3,4), ½·minAdm = 7/2):
  I(c') = ∫_{A'} ∫_{A₀-chart}  frobSq(A₀·Q)^{−c'},    Q = A₁·A₂ (tail product, from A'), A₀ front (3×3).
Equivalently (freeing the Schur block Γ, a measure-preserving shear) the freed-Γ triple
  = ∫_{A'} ∫_{x} ∫_{Γ}  (w + ‖C·Q̃ₚ + Γ·Q_b‖²)^{−c'},   w = ‖P·Q̃ₚ‖² (pivot energy), Q_b = Y·A₂ (corank rows).

ROUTE A (native ledger, believed by a prior tick): PEEL Γ FIRST (corank Morse atom) →
  det(Q_bQ_bᵀ)^{−a/2} · w^{−(c'−ab/2)}  (a = M₀−t). Then the residual w^{−...} and the det-Gram SHARE A₂
  (w = ‖(P·A₁ₚ + B·A₁_c)·A₂‖², det involves Y·A₂), so a unit-Jacobian CoV cannot make them independent
  reduced-chain variables → the coupling is carried through a decorated monomial ledger to a monomial
  terminal (the "diag(b) descent"), and the plain reduced-chain IH is Hölder-infeasible at the zero-slack
  binding cut (minAdm = peelCharge + minAdm(redChain) exactly).

ROUTE B (cheaper, front-first): do NOT peel Γ first. Integrate the WHOLE front A₀ jointly to get
  g(Q) := ∫_{A₀} frobSq(A₀Q)^{−c'}, then ∫_{A'} g(Q). Two sub-claims:
  (B1) g(Q) ≍ σ_min(Q)^{−α}, α = max{0, 2c'−m₀(q−1)} (a LOCAL box exponent: the box keeps the collapsing
       direction O(1), the ∫(σ²z²+w)^{−c'}dz→bounded mechanism). [A prior decorrelated pass confirmed this
       for the codim-1 top stratum.] BUT on the codim-2 stratum the true g ≍ σ^{−β₂}, β₂ = 2c'−m₀(m₀−2) >
       α — the single σ_min^{−α} bound UNDERSHOOTS on codim-2 (a prior finding). So Route B must be a
       RANK-STRATIFIED cover (cell by corank) + a corank-q COUPLED corner majorant per cell, closing
       ∫_{A'} against the product-rank tube codim D = minAdm(reduced) (established ∀M).
  (B2) The corank-q coupled corner (a q-block additive corner ∫(Σ_i u_i²U_i)^{−c'}∏|u_i|^{h_i}, U_i deep
       units) closes by a q-ary weighted-AM-GM at min-cut weights, PROVIDED the deep units U_i cast into
       INDEPENDENT free blocks (disjoint deep coordinates). A prior cert claims the clean-coordinate cast
       makes U_i read DISJOINT rows of A₂ (independent). Route A's coupling analysis suggests A₂ is shared.

Answer, exactly:
Q1. Do Route A's "coupling irreducible / decorated ledger" and the Cauchy–Binet-majorant/front-first Route
    B CONTRADICT, or address DIFFERENT mechanisms (Γ-first-peel-then-factor vs front-first-joint-then-tube)?
    Be precise about what each establishes.
Q2. THE DECIDING QUESTION. In Route B, after integrating the front A₀ jointly and covering by corank cells,
    does the corank-q corner genuinely factor over DISJOINT variables — i.e. do the deep units U_i read
    DISJOINT coordinate slices of A₂ (making the q-ary AM-GM valid and the ∫_{A'} tube a product of
    independent deep-block Wishart integrals), OR is A₂ irreducibly shared across the U_i (so the
    factorization fails and Route B secretly needs the same ledger)? The pivot energy w is INTEGRATED in
    g(Q) here (not held as a separate factor) — does that dissolve the Route-A coupling, or does it
    resurface in the corank-q corner?
Q3. ★ THE {w=0} QUESTION. A prior tick found the Γ-first route gives +∞ on {w = ‖P·Q̃ₚ‖² = 0}. Under Route
    B (w integrated jointly in g(Q)), is {w=0} a null sub-locus of the front A₀ integration handled by
    g(Q) ≍ σ_min^{−α} (finite ∫_{A'}), OR does it resurface as a genuine joint-resolution obstruction (Route
    B relocating the mountain-core)? Does the front-first joint integration + the strict threshold
    c'<½minAdm + the product-rank tube codim genuinely close it?
Q4. VERDICT: which route closes the Level-A finiteness hole most economically, and is Route B genuinely
    cheaper (a contained cover + Wishart-base build) or does it relocate the decorated-ledger mountain?
</task>

<output_contract>
Q1: contradict vs different-mechanisms, precise. Q2: the disjoint-vs-shared-A₂ verdict for the corank-q
corner in Route B (does integrating the pivot jointly dissolve the coupling?). Q3: the {w=0} adjudication
under Route B. Q4: which route, and whether Route B is genuinely cheaper or relocates the mountain. Mark
inference vs derived; hunt the divergence — if Route B has a hidden wall, exhibit it.
</output_contract>

<grounding_rules>
Exact reasoning (radial/Beta/Wishart, Cauchy–Binet, the box-vs-fullspace cutoff). The pivotal question is
whether integrating the front A₀ JOINTLY (Route B) genuinely decouples the deep so the corank-q corner
factors over disjoint A₂-slices, or whether A₂ is irreducibly shared. Do NOT assume Route B works (it's
the cheaper/contested one); do NOT assume it fails. Reason the disjoint-vs-shared question specifically.
</grounding_rules>
