<task>
I am designing the LOAD-BEARING inductive predicate for a resolution-of-singularities (blow-up
change-of-variables) finiteness proof, and need an independent read on the FAITHFUL SHAPE of the
predicate + its one-step transform. This is a Lean-4/Mathlib formalisation of an RLCT (real
log-canonical threshold) box-finiteness result for deep linear networks (Aoyagi's rank-flag (S,J)
resolution). Adjudicate the SHAPE; do not write Lean.
</task>

<context>
GOAL predicate (the top-level target, π=∅):
  RouteMBoxThresholdFinite M := ∀ c' ≥ 0, c' < ½·minAdm(M) →
      ∫_{A ∈ box} frobSq(prod M A)^{−c'} < ⊤
where M = (M_0,...,M_L) is a width vector, `prod M A = A_0·A_1·...·A_{L-1}` is the layer-matrix product
(the DLN multiplication map), `frobSq` = squared Frobenius norm, box = [−1,1]^(all entries), and
minAdm(M) = the minimal admissible codimension (a combinatorial min over rank-flag strata). The plain
strong induction "∀ shorter chains M', RouteMBoxThresholdFinite M'" FAILS ("exhausted lane"): at the
binding cut the residual exponent saturates, leaving no budget for the coupling between the peeled
front block and the deeper product.

BANKED, exact/verified engine (I can consume these, cannot change them):
(1) SOUNDNESS gate: minAdm(M) ≤ peelCharge(M,u) + minAdm(redChain(u,M)), where peelCharge(M,u)=(M_0−u)(M_1−u)
    is the Case-2 block codim, and redChain(u,M)=(u,M_2,...,M_L) collapses the front two widths to a
    single pivot width u (one fewer layer). Over ℝ: ½·minAdm(M) − ½·peelCharge ≤ ½·minAdm(redChain).
(2) TWO corank-block regime lemmas (isotropic, ALREADY additive form), both over an outer measurable
    domain Z (measure μ) and inner block D over its box matBox p q T:
    (a) c' > pq/2, W z > 0:  ∫_Z ∫_D (frobSq D + W z)^{−c'} ≤ Cresid(pq,c')·∫_Z (W z)^{−(c'−pq/2)}
        [per-layer exponent SHIFT c' ↦ c'−pq/2, deeper core W handed to the strong IH]
    (b) c' < pq/2, W z ≥ 0:  ∫_Z ∫_D (frobSq D + W z)^{−c'} < ⊤    [terminal block Morse dominance]
    Here pq = peelCharge = the block dimension.
(3) A generator-level carrier `SJLinGenState`: generators b_i = (monomial ∏_ℓ|u_ℓ|^{supp(i,ℓ)}) ·
    (linear form in active vars x), loss = ∑_i b_i². Operations: radialStep (prepend a fresh
    fully-shared exceptional divisor u_0 dividing every generator to order 1; loss ↦ u_0²·loss);
    rowMix (Schur elimination = a linear mix R of generators) with `gen_rowMix_const`: at CONSTANT
    support (all generators share the same accumulated monomial) the mix factors the shared monomial
    out UNCONDITIONALLY; loss_blockSplit (additive split of the loss over a sum-type pivot⊕corank
    generator index).
(4) TERMINAL endpoint: ∫_{u ∈ [0,1]^d} (sjLoss e u)^{−c'} · (∏_ℓ |u_ℓ|^{h_ℓ}) du < ⊤ for
    c' < monomialThreshold(d, sharedDivisorExp(e), h) = min_ℓ (h_ℓ+1)/(2·k_ℓ), k = sharedDivisorExp(e)
    = min_i supp(i,ℓ) (the SHARED-divisor exponent). Here sjLoss = ∑_i (∏_ℓ|u_ℓ|^{e(i,ℓ)})² is the
    fully-resolved (pure-monomial-generator) loss, and it factors: sjLoss = (∏_ℓ|u_ℓ|^{2k_ℓ})·(residual
    unit ≥ 1 at a dehomogenised generator).

KEY FIDELITY FACTS established by prior exact-algebra work:
- ANISOTROPY: after peeling the front block at pivot rank t, the front corank residual is
  frobSq(C·Q̃ + Γ·Q_b) where Γ is the freed corank block and Q_b is the deeper product's non-pivot rows.
  The Γ·Q_b coupling is ANISOTROPIC in Γ (weighted by the deeper Q_b).
- The naive route "bound the front integral ∫_{A_0} frobSq(A_0·Q)^{−c'} POINTWISE in the deeper Q by a
  power of the deeper Gram det(Q Qᵀ)" is FALSE / DIVERGES on the rank-deficient-Q locus (which is
  measure-zero but SETS the RLCT). So one CANNOT integrate the front block out against Q pointwise.
- SHARED-DIVISOR: two generators sharing ONE exceptional divisor δ (loss δ²(x²+y²), threshold ½) vs
  two fresh divisors (loss δ₁²x²+δ₂²y², threshold 1) give DIFFERENT RLCTs. A fresh-per-block accounting
  UNDERCOUNTS. The deeper factor's rank loci are INTRINSIC to the deeper product (independent of the
  front coupling rows), so one sequential chart cover can resolve both the front coupling term and the
  deeper loss with the SAME (shared) exceptional divisors — but this must be tracked generator-by-
  generator (a sum-of-squares/frobSq equality is TOO COARSE to certify which generators share a divisor).
- CLEAR-FIRST ordering: the recursion must do each step's scalar Schur elimination FIRST (at constant
  support, so gen_rowMix_const applies) and attach that step's radial divisor AFTER.
</context>

<questions>
Q1. What is the FAITHFUL inductive predicate to carry through this recursion — the object at an
    INTERMEDIATE profile (k front-peels done, L−k layers remaining)? Specifically: what is the
    integrand, the weight, the integration domain, and the threshold? Is the object
    "∫ (accumulated Jacobian monomial ∏u^h)(z's exceptional coords) · frobSq(prod(remaining chain) A')^{−c'}
     over (exceptional box)×(remaining-chain box)" — i.e. a SEPARABLE weight × ORIGINAL-reduced-chain-loss —
    the faithful intermediate object? Or must the loss be the generator-carrier loss (SJLinGenState.loss,
    monomial-prefix × linear-residual) over the blown-up chart coordinates, because the separable
    weight×original-loss form hides the anisotropy/shared-divisor coupling and is only faithful at the
    terminal (where sjLoss_factor makes it genuinely separable)?

Q2. Does a CLEAR-FIRST peel step (scalar Schur elimination at constant support via gen_rowMix_const,
    THEN attach the radial via radialStep, THEN the corank regime lemma) compose from the intermediate
    predicate at profile π to the intermediate predicate at profile (π extended by one cut) — with the
    exponent shift c' ↦ c'−½·peelCharge handled by regime (2a), and terminating at the (4) terminal via
    regime (2b) / the monomial threshold? Where, precisely, does the anisotropy removal / shared-divisor
    sharing enter the step, and does the intermediate predicate you chose in Q1 carry enough to make the
    step non-circular and sound (in particular on the rank-deficient-deeper-factor locus)?

Q3. Threshold level-bridge: the top predicate uses ½·minAdm; the terminal uses
    monomialThreshold = min_ℓ(h_ℓ+1)/(2k_ℓ). For the base case to discharge the intermediate predicate
    at the terminal profile, what must hold between ½·minAdm(remaining chain) and monomialThreshold?
    Is carrying "carrierThreshold(π) = ½·minAdm(remChain π)" as the intermediate threshold sound, given
    the soundness gate (1)?

Provide your OWN best design for the predicate + step SHAPE (structure/def/theorem-level, no Lean
syntax needed), then answer Q1–Q3. State confidence and the single most likely way your design is wrong.
</questions>

<output_contract>
- Your recommended SHAPE for the intermediate predicate (integrand/weight/domain/threshold) + the peel-step
  transform + the base + the π=∅ corollary.
- A crisp verdict on Q1: separable weight×original-loss vs generator-carrier loss (or a third option).
- Where anisotropy/shared-divisor enters the step and whether your predicate carries enough (Q2).
- The threshold level-bridge (Q3).
- Confidence + the single most likely failure of your design.
- Distinguish clearly what is INFERENCE vs what follows directly from the banked facts I gave.
</output_contract>

<grounding_rules>
Ground strictly in the banked engine + fidelity facts above. Do not invent Mathlib lemmas. If the
faithful predicate is genuinely under-determined by what I gave, say so and name the missing datum.
</grounding_rules>
