<task>
Adjudicate a design question in the RLCT / integral-finiteness resolution of deep-linear-network
loss (Aoyagi-style). Work the exact algebra; adjudicate EITHER direction (a clean route EXISTS, or a
scoped no-go with the sufficient conditions). Withhold nothing about the facts; I want your independent
read, not a rubber stamp.

SETUP (exact, matches a verified Lean formalisation).
- A "chain" is a width vector M = (M_0, M_1, ..., M_L), all widths >= 1, giving L layer matrices
  A_s of shape M_s x M_{s+1}. The layer product is prod(M,A) = A_0 A_1 ... A_{L-1}, shape M_0 x M_L.
- The target box integral is  I(M, c') = ∫_{box} ‖prod(M,A)‖_F^{-2c'} dA, box = all entries in [-1,1].
  GOAL: prove I(M,c') < ∞ for every c' < minAdm(M)/2.  ("minAdm" defined below.)
- minAdm recursion (exact, verified):  minAdm(n,m) = n·m;
  minAdm(M) = min_{0<=t<=min(M_0,M_1)} [ (M_0 - t)(M_1 - t) + minAdm(t, M_2, ..., M_L) ].
  redChain(t,M) = (t, M_2, ..., M_L), one fewer layer.
- BASE, ALREADY PROVEN (unconditional, all widths): for every 3-width chain (m,n,p),
  I((m,n,p), c') < ∞ for c' < minAdm(m,n,p)/2.  Call this "the mnp base".
- The general proof peels the FRONT: at binding cut t and a "shell" indexed by the number j of small
  singular values of the deep-tail product Q = A_1...A_{L-1} (shape M_1 x M_L), the head-split reduction
  bounds the shell integrand by C · [reduced comparator on redChain(u,M), u=t+j] at exponent shifted by
  ½·(M_0-u)(M_1-u), closed by the induction hypothesis (IH: I(M') for all one-shorter chains M').
- The head-split's constant C is FINITE iff the "pivot criterion" holds:
  hpiv(u):  minAdm(redChain(u,M)) <= u · ρ,   where ρ = min(M_1, M_2, ..., M_L) (tail min width).
  When hpiv(u) FAILS, the head-split diverges (C = ∞). These failing shells are the "WAIST shells".

ESTABLISHED FACTS (exact, exhaustively checked — treat as given).
(F1) A chain has a hpiv-FAILING (waist) shell  ⟹  M_1 < min(M_2, ..., M_L)  [strict front pinch].
     Hence on any waist chain ρ = M_1, and the deep-tail product Q (M_1 x M_L) has generic
     full row rank M_1.
(F2) For all waist chains:  minAdm(M) <= minAdm(M_0, M_1, M_L)   AND   minAdm(M) <= M_0·M_1.
(F3) A whole-chain domination  I(M,c') <= const · I((M_0,M_1,M_L), c')  is provably TOO STRONG:
     the L-layer integral genuinely diverges for c' in (minAdm(M)/2, minAdm(M_0,M_1,M_L)/2), where the
     3-width integral is still finite. So no c'-uniform domination by a 3-width box can hold on that range.
(F4) On the shell where Q is bounded away from degeneracy (all singular values >= ε, i.e. j=0), the shell
     integral is finite up to c' < M_0·M_1/2 directly (frobSq(A_0 Q) >= ε²·frobSq(A_0), front Morse bound,
     deep integrated over a compact region). So the FULL-rank-deep shell is easy; the hard shells have
     the deep product degenerate (j >= 1).

THE QUESTION.
On a WAIST chain (M_1 < min(M_2,...,M_L)), consider a shell where the deep-tail product Q has j >= 1
small singular values AND hpiv(t+j) fails. The head-split reduction to redChain(t+j, M) diverges there.
Design a reduction of THIS waist shell's box integral to a 3-width "mnp base" integral (finite up to
minAdm/2 of the 3-width chain), OR prove a scoped no-go. Key sub-questions:
  (Q1) Which 3-width chain (m,n,p) is the right target, and does its minAdm cover the needed threshold
       c' < minAdm(M)/2 (i.e. is minAdm(M) <= minAdm(m,n,p))?
  (Q2) What is the reduction mechanism that correctly ACCOUNTS FOR the deep charge (the divergence from
       the deep layers degenerating), given (F3) forbids a naive whole-chain domination? Candidate
       mechanisms: change-of-variables collapsing the tail; a per-shell exponent/charge bookkeeping that
       transfers the deep degeneracy into a lower 3-width threshold; peeling a different layer / using the
       IH on the tail sub-chain (M_1,...,M_L); a rank-stratified additivity.
  (Q3) Does the reduction need the induction hypothesis (on some one-shorter chain), or is it a direct
       reduction to the banked 3-width base with no IH? If it needs an IH, which chain?
  (Q4) Is reversal (transpose CoV, I(M) = I(reverse M)) needed, or avoidable? (Note: 3-width chains are a
       base case, so the recursion never has to peel a 3-width waist.)
</task>

<output_contract>
1. VERDICT: does a waist shell reduce to the mnp base cleanly (LABOUR), or a scoped no-go (+ the
   sufficient conditions under which it closes)? One line.
2. For Q1-Q4, a direct answer each, with the exact algebra / threshold arithmetic that settles it.
3. The single cleanest reduction mechanism you can construct (or the obstruction that blocks all
   candidates), with a worked check on the minimal waist chains (2,1,2) [L=0, 3-width] and (2,1,2,2)
   [L=1, 4-width, front waist], stating minAdm of each and the target 3-width chain.
4. The one thing most likely to break the proposed route.
Keep it tight; exact arithmetic over prose.
</output_contract>

<grounding_rules>
- Exact integer/rational arithmetic for all thresholds; Monte-Carlo only as a guide, never as a result.
- Distinguish clearly what you PROVE vs CONJECTURE vs suspect.
- If a candidate mechanism fails, say why with a concrete counterexample.
- Do not assume any machinery beyond: the mnp 3-width base (given), the minAdm recursion, standard
  linear algebra (SVD, rank, PSD monotonicity), Lebesgue/Fubini, and the induction hypothesis on
  one-shorter chains.
</grounding_rules>
