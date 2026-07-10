<task>
I am a Lean formaliser on a project formalising Aoyagi's RLCT computation for deep linear networks
(square-Frobenius loss). I need a decorrelated adjudication of TWO design questions about "one decorated
peel" before I write Lean. Answer from the math; I give you the exact banked Lean objects.

SETTING. Chain of widths M = (M0,M1,...,ML), L≥2 (≥3 widths). Layer matrices A0:M0×M1, A1:M1×M2, ...
Product prod = A0·A1···A_{L-1} (M0×ML). Loss = frobSq(prod) = sum of squares of entries. TARGET (called
(□)): the box integral ∫_{A in [-1,1]^box} frobSq(prod A)^{-c'} dA is FINITE for every c' < (1/2)·minAdm M,
where minAdm M is the minimal admissible codim (an integer, = the zero-product-locus codim). We prove (□)
by strong induction on chain arity: one "peel" reduces M (arity L+3) to redChain t M = (t, M2,...,ML)
(arity L+2, ONE fewer layer) at a pivot rank t ≤ min(M0,M1), charging peelCharge = (M0-t)(M1-t), then the
one-shorter IH (box-finiteness of ALL arity-(L+2) chains) closes it. Soundness (BANKED):
minAdm M ≤ peelCharge + minAdm(redChain t M), so c' < (1/2)minAdm M shifted down by (1/2)peelCharge stays
below (1/2)minAdm(redChain t M).

BANKED PIECES (all sorry-free Lean, verified):
(A) MATRIX-BOX SIDE. Set P=A0's pivot t×t block (invertible on the chart), a=M0-t, b=M1-t.
  - gammaPeelIntegral_schurShearFree_eq : the per-(t,ρ,κ)-chart integral EQUALS the "freed-Γ" form
    ∫_{A' tail box} ∫_{x=(P,B12,C) outer, P invertible} ∫_{Γ free over shear-box}
       (freedSchurLoss x Γ Qtilde)^{-c'},  where
    freedSchurLoss = frobSq(P·Qp~) + frobSq(C·Qp~ + Γ·Qb),  Qp~ = Qp + P^{-1}B12·Qb,
    Qtilde = (prod(tailChain M) A') reindexed into (pivot t ⊕ corank b) rows, Qb = corank rows.
    (EQUALITY, no hypotheses — a pure change of variables. Γ, the a×b corank block, is now a free var.)
  - freedSchurLoss_inner_peel_lt_top (Regime A): the inner-Γ integral is finite IF (i) pivot core
    0<frobSq(P·Qp~), (ii) Qb·Qbᵀ positive-definite, (iii) c' > a·b/2.
  - freedSchurLoss_inner_bounded_lt_top (Regime B): if 0<frobSq(P·Qp~) (core positivity) alone, over any
    FINITE-measure domain the inner-Γ integral is finite for any c'≥0 (integrand bounded).
(B) DECORATED-CARRIER SIDE. A carrier SJLinGenState with generators b_i = (monomial ∏|u_ℓ|^{supp i ℓ})·
  (linear residual in active vars); loss = Σ b_i². Banked: radialStep (prepend fully-shared divisor u0,
  loss ×= u0²), rowMix by matrix R with side-condition hsh (each mixed generator combines only old
  generators sharing its target support) — hsh is FREE at a "fresh block" (all generators share support,
  gen_rowMix_const); loss_blockSplit (partition generators into pivot⊕corank splits loss additively);
  a monomial terminal finiteness sjLoss_terminal_lintegral_lt_top. The block-elimination is the det-1 unit
  A0 = invSchurLeft(A,C)·diag(A,Γ)·invSchurRight(A,B), R-blocks C·A^{-1} and A^{-1}·B.

THE STANDING GAP (per repo's own headers, triple-confirmed by prior decorrelated Codex): supplying the
Regime-A interface hyps (i)(ii)(iii) AS A MEASURE STATEMENT over the outer tail A' is the unbanked "(S,J)
double induction" descending the carrier to the terminal + wiring the reduced coupling to the strong IH.
CRUCIAL: at the binding cut minAdm M = a·b + minAdm(redChain t* M) the residual exponent EXACTLY saturates
the reduced-chain IH threshold, so a black-box Hölder split (bound the decorated integral by a product of
the reduced-chain box integral times a radial factor) is claimed INFEASIBLE (borderline divergence).

MY TWO QUESTIONS:

Q1 (T2 framing). A prior recon said "extend the fresh-block rowMix identity to the ACTUAL Schur matrix
R = A^{-1}B at a NON-fresh block." But the carrier design says hsh (support-homogeneity) is FALSE for
arbitrary R and the block-elimination is only applied at FRESH blocks (post-radial, common support), where
hsh is free. Starting from the trivial decoration (supp≡0) and applying radialStep (prepends a
fully-shared column), the common-support invariant is MAINTAINED, so when the elimination fires it IS at a
fresh block. IS my determination correct that "arbitrary R at a non-fresh block" is a misframing / dead
target, and the genuine content is the fresh-block elimination (already banked) COUPLED to the radial CoV?
Or is there a real, separable non-fresh-block rowMix obligation I am missing?

Q2 (the peel CoV route). To prove one peel, which is the sounder route, and is either actually able to
DODGE the binding-cut Hölder infeasibility?
  (a) REUSE the banked matrix-box CoV (gammaPeelIntegral_schurShearFree_eq) + the two FreedPeel inner-Γ
      branches, and supply interface hyps (i)(ii)(iii) by integrating the OUTER tail A' — i.e. the descent
      is on the OUTER parameters, transported through the carrier; OR
  (b) build a carrier-NATIVE change of variables (radial+rowMix+blockSplit as an actual measure CoV on the
      matrix box with monomial Jacobian), independent of gammaPeel.
  For whichever you favour, state precisely HOW the shared-divisor absorption (monomialising so the reduced
  chain and the radial factor CLEANLY, i.e. an EQUALITY/exact factoring, not a Hölder inequality) evades
  the binding-cut saturation. Is the exact-factoring claim sound, and what is the single load-bearing
  sub-lemma it rests on?
</task>

<output_contract>
Two sections, Q1 and Q2. 
Q1: a one-word verdict (CORRECT / INCORRECT / PARTIAL) on my T2 determination, then ≤6 sentences of
justification, then the single sharpest thing I might be missing (or "nothing material").
Q2: pick (a) or (b) (or "hybrid" with the split), ≤10 sentences. Then: does the exact-factoring route
GENUINELY dodge the binding-cut Hölder infeasibility — YES/NO/UNPROVEN — and name the ONE load-bearing
sub-lemma. End with the single cheapest discriminating check (a small chain + a concrete computation) that
would confirm or refute the route before I sink formalisation effort.
Keep total under ~450 words. Flag any claim that is inference vs. a fact you can derive from what I gave.
</output_contract>

<grounding_rules>
You may reason from the math and the banked objects as I described them. Do NOT assume Mathlib has GMT /
tube-volume / Łojasiewicz (it does NOT). Flag explicitly when you are inferring vs. deriving. If a claim
needs a fact I did not give (e.g. a specific value of minAdm), say so rather than guessing.
</grounding_rules>
