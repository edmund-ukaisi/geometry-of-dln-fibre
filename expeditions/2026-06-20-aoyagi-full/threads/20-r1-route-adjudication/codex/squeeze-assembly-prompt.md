<task>
We are formalising (in Lean) the real-log-canonical-threshold (RLCT) of the square-Frobenius loss
of a deep linear network at its deepest singular point. The geometric content reduces to the RLCT
of the matrix-product "core" loss F = ‖C¹·C²·…·C^L‖² at the origin (all Cˢ = 0), for free matrices
Cˢ of size Mˢ×M^{s+1}. The established VALUE is rlct(F) = ½·minAdm(M), where
  minAdm(M₀,…,M_L) = min over weakly-decreasing rank profiles t of
       Mval(t) = (M₀−t₁)(M₁−t₁) + Σ_{j≥2}(t_{j−1}−t_j)(M^{j+1}−t_j).
This obeys the layer-peeling recursion
  minAdm(M₀,M₁,M₂,…,M_L) = min_{t ≤ min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t, M₂, …, M_L) ].

We are choosing between two Lean routes to prove rlctAtOn(F)(0) = ⨅_i monomialThreshold(dᵢ,kᵢ,hᵢ),
where the RHS value is already proven = ½·minAdm via a separate "value lane".

ROUTE B (the one under scrutiny) is a per-node SQUEEZE recursion. Its proven machinery:
  • rlctAtOn_squeeze: if c₁·Φ ≤ F ≤ c₂·Φ near w* with c₁,c₂>0, then rlctAtOn(F)(w*) = rlctAtOn(Φ)(w*).
    (Same-point sandwich; NO change of variables, NO measure Jacobian.)
  • The per-node step computes rlctAtOn(flatCore)(0,0) = nReg/2 + rlctAtOn(G²)(0), where
    Φ = (∑_{j∈nReg} Eⱼ²) + G², and G² is the "reduced-chain loss".
  • The single remaining interface hypothesis `hnode` asserts: near the deepest point, the per-node
    core is in the Schur form
        flatCore w = (∑_j w₁ⱼ²)  +  ∑_{i,j} (bcolᵢ · w₁ⱼ + SΓᵢⱼ)²
        G(w₂)²     = ∑_{i,j} SΓᵢⱼ²
        ∑_i bcolᵢ² ≤ T²
    Here w₁ = the nReg regular coordinates (= the pivot-row product "Erow"); bcol = a single pivot
    COLUMN vector; SΓ = a residual matrix. The cross term bcolᵢ·w₁ⱼ is a RANK-1 outer product
    bcol⊗Erow. The recursion's reduced chain is redChain(t,M) = (t, M₂, …, M_L) — one fewer layer —
    and the datum demands G² = dlnLoss(redChain t M) ∘ redEmbed via a measure-preserving homeomorphism
    redEmbed onto the parameter space of the reduced WIDTH-CHAIN (t, M₂, …).

FACTS we have established by exact symbolic computation (sympy) and Newton-polytope LP:
  (1) hardPivot Schur with ONE pivot cleared (1×1 block = 1): the lower rows of the product factor
      EXACTLY as lowerᵢⱼ = bcolᵢ·Erowⱼ + (S·Γ)ᵢⱼ — i.e. the cross term IS the rank-1 outer product.
      Verified as a CommRing matrix identity.
  (2) (2,2,2,2) chain, rank-1 layer-1 peel: after one incidence chart + one blow-up,
      F = α²ρ²·U with U = ‖[[ξ,η],[bξ+r,bη+s]]·C³‖², and U VANISHES TO ORDER 4 at the deepest point
      (NOT a unit). So one blow-up does not terminate; the residual U is a fresh (2,2,2) core.
  (3) (3,3,4) core [an L=2 / RRR chain], minimiser t=(1,0), Mval=8, true rlct=4 (anchored to the
      published Aoyagi-Watanabe 2005 reduced-rank-regression closed form, and independently to a
      diag(b) coupled resolution). A "threshold-only / per-row-scalar" recursion gives 3 (WRONG).
      The peel gives F ∼ ‖T‖² + ‖Δ·S‖², T clean 1×4, Δ a FREE 2×2, S a free 2×4 (disjoint variable
      sets from T). The matrix product Δ·S (Δ free 2×2) is generically rank 2.
  (4) (3,3,4): minAdm(redChain 1 (3,3,4)) = minAdm(1,4) = 4 (a two-width LEAF, smooth dlnLoss = 4
      squares, rlct value 2). minAdm(2,2,4) = 4 as well (a (2,2,4) PRODUCT core, rlct value 2 via a
      genuine radial resolution of a determinantal-type variety). Both have rlct VALUE 2.

We have run the per-node Schur-form algebra, the (2,2,2,2) blow-up, and the (3,3,4) peel exactly.
Your job is an INDEPENDENT read of the soundness of Route B's hnode interface and its recursion
assembly — do NOT assume our conclusion (we have one; it is withheld here).

QUESTIONS (answer each explicitly):

Q-A. Consider the hnode interface at a node where the layer-1 peel has corank ≥ 2 (the residual
  block Δ is a genuine ≥2×2 matrix, e.g. (3,3,4) at t=1). Can the per-node Schur form
     flatCore = ∑ Eⱼ² + ∑ᵢⱼ(bcolᵢ·Eⱼ + SΓᵢⱼ)²,  G² = ∑ SΓᵢⱼ²,  with bcol a SINGLE column and
     SΓ the residual — be satisfied while ALSO honestly meeting redCore_eq: G² = dlnLoss(redChain)
     ∘ (measure-preserving homeomorphism)? Pay attention to whether the rank-1 cross term bcol⊗Erow
     can represent a rank-2 Δ-coupling, and to whether the geometric reduced core matches the
     width-chain reduced loss dlnLoss(redChain).

Q-B. The per-node squeeze necessarily delivers rlct(node) = nReg/2 + rlct(reduced). This is an
  ADDITIVE split where the nReg coordinates contribute as a SMOOTH (Morse) block (rlct = nReg/2).
  Is there any way for this additive-smooth-block arithmetic to reproduce the value at a
  corank-≥2 binding branch, OR does the coupled Δ-block (whose 12 free coords resolve to rlct 2,
  far below the smooth 12/2=6) necessarily force the coupling to live in G² (the "reduced" core),
  with G² then NOT being a smooth/width-chain reduced loss?

Q-C. The squeeze rlctAtOn_squeeze sandwiches F between c₁·Φ and c₂·Φ at the SAME point with
  c₁,c₂>0 constants. For the conclusion rlctAtOn(F) = rlctAtOn(Φ) to be both SOUND and useful at a
  genuinely singular reduced core, where (if anywhere) does the argument secretly need the analytic
  monomial→RLCT extraction (the "rlct of a normal-crossing monomial integrand")? Flag any place
  the chain would have to import that analytic fact rather than derive it from the squeeze alone.

Q-D. Net: is the hnode interface a SOUND-but-narrow hypothesis (true for a restricted class of
  width vectors), or is it (as stated, with the rank-1 cross term + width-chain reduced loss)
  unsatisfiable / value-wrong at corank-≥2 binding branches? Name the precise scope on which it
  holds, and the precise obstruction where it fails.
</task>

<output_contract>
Four sections Q-A, Q-B, Q-C, Q-D, in order. For each: a sharp verdict (one line) then the
load-bearing reasoning (≤ 8 lines). In Q-D give the scope as a predicate on the width vector M
(e.g. "corank ≤ 1 at every binding peel"). Tag each claim FACT (forced by the algebra you can
verify from the setup) or INFERENCE (your structural judgement). End with ONE line: the single
most load-bearing thing that, if true, would make hnode sound general-L.
</output_contract>

<grounding_rules>
Do not assume our conclusion. You may use the exact facts (1)-(4) as given (they are
sympy/Newton-LP verified). Distinguish a rlct VALUE coincidence (two germs with the same rlct) from
a GERM isomorphism (measure-preserving homeomorphism) — these are different and the distinction is
load-bearing for redEmbed. If you assert a matrix-rank or ideal fact, it must be checkable from the
stated free-matrix structure. Flag inference vs fact explicitly on every claim.
</grounding_rules>
