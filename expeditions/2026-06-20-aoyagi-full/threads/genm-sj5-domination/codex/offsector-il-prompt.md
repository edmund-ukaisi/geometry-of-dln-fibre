<task>
Adjudicate a SOUNDNESS/CLOSURE question in an RLCT-finiteness induction for deep linear networks.
I withhold my own conclusion; derive yours independently from the structure. Exact power-counting /
integrability reasoning, not Monte-Carlo.

SETUP (exact objects).
- Chain M = (M0,M1,...,M_last), layers A_s of size M_s x M_{s+1}. Loss frobSq(prod A_s). Params = box of
  layer tuples. We prove, by induction on arity (#layers), that the box integral
  ∫_Params frobSq(prod)^{-c'} < ∞ for all c' < carrierThreshold(M) := (1/2) minAdm(M), where
  minAdm(M) = min_t [ (M0 - t)(M1 - t) + minAdm( (t, M2, ..., M_last) ) ], base arity-2 (n,m) -> minAdm=n*m.
  IH: all shorter chains M' finite for c'' < carrierThreshold(M').

INDUCTIVE STEP (the "front peel", at a binding cut t*; a = M0 - t*, b = M1 - t*, peelCharge = a*b):
- Split front layer A1 (M0 x M1) into a t*-pivot block + a freed a x b corner (variable Γ).
- Split the deeper tail Z_tail = prod(A2..A_last) (size M1 x M_last) rows into t* pivot rows Q_p and
  b corank rows Q_b. Here Q_b = A_cor * Z_deep, where A_cor = the b corank rows of A2 (size b x M2), FREE,
  and Z_deep = prod(A3..A_last) (size M2 x M_last).
- A banked lemma (Gaussian integration of the freed corner Γ) gives, GIVEN Q_b Q_b^T positive-definite
  and pivot energy w = frobSq([P|B12]*Z_tail_pivot) > 0, for c' > a*b/2:
      ∫_Γ (freedSchurLoss)^{-c'} dΓ  ≤  det(Q_b Q_b^T)^{-a/2} · Cresid · (w + residual)^{-(c' - ab/2)}.
  Dropping the nonneg residual and using w = frobSq(Γ' * Z_deep) = the loss of a genuine reduced comparator
  D' on the reduced chain M' = (t*, M2, ..., M_last) (arity one less), the GOOD sector {σ_min(Q_b) >= ε}
  closes: det(Q_bQ_b^T)^{-a/2} <= ε^{-ab/2} (a constant), and the IH gives D'.integral(c'-ab/2) < ∞ for
  c' - ab/2 < carrierThreshold(M') = carrierThreshold(M) - ab/2, i.e. c' < carrierThreshold(M). CLEAN.

THE OPEN SURFACE: the OFF sector {σ_min(Q_b) < ε} (Q_b near a row-rank drop). There det(Q_bQ_b^T)^{-a/2}
blows up. I have found the following facts (please verify each independently and answer the questions):

FACT 1. The banked freed-corner lemma ALSO has a "bounded" form: ∫_Γ (freedSchurLoss)^{-c'} dΓ ≤ w^{-c'}·vol(box)
  (drop the nonneg corner term, integrand ≤ constant w^{-c'}); valid for any c'≥0, w>0, no PosDef needed.
  This does NOT blow up as Q_b -> 0. So the TRUE ∫_Γ interpolates: as Q_b -> 0 the freed-corner integral
  -> w^{-c'}·vol (finite), while the atom bound det(Q_bQ_b^T)^{-a/2}·(...)^{-(c'-ab/2)} -> ∞. Hence the atom
  bound is LOSSY / vacuous on the off sector.

FACT 2. Exact interpolation of the true freed-corner integral: writing τ_k = singular values of Q_b (b of
  them), and diagonalizing, ∫_Γ (w + ||c + Γ Q_b||^2)^{-c'} dΓ = (∏_k τ_k)^{-a} · ∫_{u ∈ box scaled by τ}
  (w + ||u||^2)^{-c'} du  (u ∈ R^{ab}). For b=1 (single τ=||Q_b||): = τ^{-a}·U(w,τ), with
  U(w,τ) = ∫_{|u|<~τ, R^{a}} (w+|u|^2)^{-c'} du  ~  w^{a/2 - c'}   (regime τ >= sqrt(w))
                                                ~  w^{-c'} τ^{a}    (regime τ <= sqrt(w)).
  So I := τ^{-a} U ~ det(Q_bQ_b^T)^{-a/2} w^{a/2 - c'} (atom, τ≥√w) or ~ w^{-c'} (bounded, τ≤√w).

FACT 3. Integrating the ATOM bound over the free corank block A_cor (b x M2), with Z_deep FULL RANK:
  W := ∫_{A_cor∈box} det(A_cor Z_deep Z_deep^T A_cor^T)^{-a/2} dA_cor. For b=1 this is
  ∫_{R^{M2}} (Σ σ_i^2 x_i^2)^{-a/2} dx, whose singularity at {A_cor Z_deep = 0} = {A_cor=0} (codim M2 for
  full-rank Z_deep) is integrable iff a < M2, giving W finite; if a = M2 it is log-divergent, if a > M2
  it DIVERGES. And near a first-order tail rank-drop (σ_min(Z_deep)=s->0) with a<M2, W ~ s^{-max(0,a-(M2-1))}
  (a LOG at a = M2-1). So the corank weight's divisor exponent p_W = max(0, a-(M2-1)) [b=1].

FACT 4. Whether a >= M2 arises at a genuine binding cut: YES. E.g. M=(3,2,2,3) has minAdm=4, binding cut
  t*=1 giving a = M0-t* = 2, b = M1-t* = 1, M2 = 2, so a = M2 = 2, peelCharge = 2, reduced chain (1,2,3)
  with minAdm=2. carrierThreshold(M)=2. Also (3,3,4)@t*=1 gives a=b=2, corank-2. So a>=M2 (hence W divergent
  and the atom-over-A_cor route dead) occurs for genuinely-binding, thin chains.

QUESTIONS.
Q1. Is my FACT 1/2 correct that the single freed-corner atom bound is genuinely LOSSY on the off sector,
    i.e. the atom-brick domination canNOT close the off sector when a >= M2 (because ∫ det(Q_bQ_b^T)^{-a/2}
    over the free A_cor diverges), even though the TRUE integral is finite?
Q2. The natural sound closure is a TWO-REGIME split: use the BOUNDED brick (I ≤ w^{-c'} vol) on the region
    {τ = σ_min(Q_b) ≤ sqrt(w)} and the ATOM brick on {τ ≥ sqrt(w)}. Does ∫_{off} min(atom, bounded) over
    the joint variables (A_cor, reduced vars, Z_deep-degeneration) converge for c' < carrierThreshold(M)?
    In particular: on {τ ≤ √w}, the constraint ||A_cor Z_deep|| ≤ √w cuts the A_cor measure to a slab of
    volume ~ (√w / σ_min(Z_deep))^{M2} (b=1), giving ∫ w^{-c'}·(√w/σ)^{M2}·(reduced measure). Does the
    factor w^{M2/2 - c'} recover enough budget to compose to carrierThreshold(M)? Do the charges ADD to
    exactly (1/2)minAdm(M), or is there a width where the joint estimate UNDERSHOOTS (off-sector threshold
    < carrierThreshold(M))?
Q3. #118 GAP: a rank-drop-STRATUM recursion (recurse into {corank Z_deep >= q+1}) is unsound because a
    2nd-order degeneration (Z=a·b scalar product: σ_min = |ab| ~ t^2 at a=b=0, but corank(Z)=1 with NO
    deeper corank stratum) is never reached. The proposed fix recurses on NETWORK DEPTH (peel a deeper
    factor; strictly decreases; bottoms out at the 2-layer base = a single FREE-ENTRY layer, where
    σ_min ~ dist transversally, order 1). Is the network-depth recursion sound and does it PROVABLY reach
    the a·b 2nd-order point? Note a known category error to avoid: a single matrix M(t)=[[1,t],[t,0]] is
    affine+immersive yet σ_min ~ t^2 (tangent to {det=0}); does the "2-layer base has order-1 everywhere"
    claim survive when the base matrix has FREE entries (not a constrained curve)?
Q4. NET verdict: does the off sector CLOSE for c' < carrierThreshold(M) by (bounded brick) ⊕ (atom brick)
    two-regime split + network-depth recursion, with charges adding to (1/2)minAdm(M) — a SOUND but LABOUR
    design — OR is there a genuine obstruction (a width where the joint budget undershoots, or the
    network-depth recursion fails to reach a degenerate point)? One line: "CLOSES (labour)" or
    "OBSTRUCTION at <where>".
</task>

<output_contract>
Answer Q1-Q4 in order, terse, with the exponent arithmetic explicit for Q2 (the composition to
(1/2)minAdm(M), or the width where it undershoots). For Q3 give the reason the network-depth recursion does
or does not reach the a·b point. For Q4 one line NET. Flag any of FACT 1-4 that are wrong.
</output_contract>

<grounding_rules>
Reason from the stated objects only. Exact integrability/power-counting; no Monte-Carlo certification.
Distinguish what you PROVE from what you INFER. If you need an assumption (e.g. uniform transversality of the
tail product near its rank-drop), state it explicitly as an assumption.
</grounding_rules>
