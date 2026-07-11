<task>
I am designing the formaliser-ready build-plan for ONE analytic obligation in a Lean/Mathlib
formalisation of Aoyagi (2023) §5 "Proof of Main Theorem" (the deep-linear-network learning-coefficient
= real log-canonical threshold). I need an INDEPENDENT read on (1) the correct recursion structure and
(2) which of two integration atoms is the native one. Do NOT rubber-stamp; attack from scratch.

## The mathematical object (exact)
We want: for a "chain" of free real matrices C^(1),...,C^(L) with C^(s) of size M^(s) x M^(s+1)
(the coranks; M : Fin(L+1) -> N), the box integral
    I(M,c') = ∫_{A in [-1,1]^params} frobSq( C^(1)·C^(2)···C^(L) )^{-c'}
is FINITE for every c' < (1/2)·minAdm(M), where
    minAdm(M) = min_{t <= min(M0,M1)} [ (M0-t)(M1-t) + minAdm( (t,M2,...,ML) ) ]     (proven recursion),
i.e. minAdm is a MIN over layer-peel cuts t of [ front block codim (M0-t)(M1-t) + minAdm(reduced chain) ].
This is Aoyagi's RLCT lower-bound leg (finiteness below threshold), obtained by his recursive
coordinate blow-up: radial blow-ups + det-1 unit ("Lemma 2 / Gaussian-Schur") clears +
absorption-by-renaming into the next factor + a diag(b) monomial ledger, terminating at a pure monomial
ideal whose exponents give the threshold.

## The single open obligation (one peel step)
Everything is already reduced (sorry-free) to ONE Prop. Given the "one-shorter IH" = box-finiteness
for EVERY chain with one fewer layer, prove ONE peel of the leading layer-pair:
resolve the front factor C^(1) (M0 x M1) at a rank-t pivot minor (t = the cut, 1<=t<=min(M0,M1)); the
t-pivot is cleared by a det-1 unit transform, leaving a "corank block" Γ of size p x q
(p=M0-t, q=M1-t) COUPLED to the deeper product via a matrix Q_b = (deeper product restricted), plus a
resolved pivot energy. The claim: the resulting integral is finite for c' < (1/2)·minAdm(M).
At the "binding cut" u* one has EXACTLY minAdm(M) = (M0-u*)(M1-u*) + minAdm(reduced chain), i.e. the
front block codim (M0-u*)(M1-u*) plus the reduced-chain threshold saturate with ZERO slack.

## Two candidate integration atoms for the corank block Γ
ATOM-1 ("integrate Γ to full space"): treat Γ ∈ R^{p×q} as free, integrate over ALL of R^{p×q}:
    ∫_{R^{p×q}} (w + ‖A_piv‖² + ‖Ccross + Γ·Q_b‖²)^{-c'} dΓ
      = det(Q_b Q_bᵀ)^{-p/2} · Cresid(pq,c') · (w + ‖A_piv‖² + ‖Ccross·(I-P)‖²)^{-(c'-pq/2)},
    valid ONLY when Q_b has full row rank (Q_b Q_bᵀ positive definite); gives exponent shift
    c' ↦ c'-pq/2 and a Gram-determinant weight det(Q_bQ_bᵀ)^{-p/2}. This weight is UNBOUNDED /
    the identity FAILS on the locus {rank Q_b < q} (det = 0).
ATOM-2 ("radial blow-up within the box"): keep Γ a bounded chart coordinate on [-1,1]^{p×q}; introduce
    a radial coordinate u0 (Γ = u0·Γ̂, Γ̂ on the sphere), so the loss becomes w + u0²·(...), the polar
    Jacobian contributes u0^{pq-1}, and the radial u0-integral over [0,1] converges for c'>0. The u0
    divisor is recorded in the diag(b) monomial ledger (shared into the deeper loss); the block is
    resolved to normal-crossing and the finiteness is read off a monomial terminal.

## The rank stratification of Q_b (from a chart census)
On the rank-t pivot chart the coupling Q_b (size q × deeper-width) stratifies by rank:
 - "good" stratum rank Q_b = q (full row rank): a full-measure slice, NON-binding (its codim exceeds
   the reduced-chain threshold);
 - "top" stratum rank Q_b = q-1: closes elementarily;
 - "deeper" stratum rank Q_b <= q-2 (needs q>=2): reported as ~86% of the binding "corner" charts —
   this is where the true threshold minAdm is attained (the BINDING stratum).

<questions>
Q1. RECURSION STRUCTURE. Is this peel provable as a PLAIN single peel — i.e. hand the reduced integrand
    directly to the one-shorter (undecorated) IH — or does it REQUIRE a genuine double induction
    (the IH must carry a decoration / monomial weight, OR the descent must land a strictly-shorter chain
    with the decoration absorbed)? Concretely: after the front peel, the diag(b) monomial weight u0^{...}
    is SHARED into the deeper loss (not separable except at the terminal). Can a plain-IH single peel
    close it, or is that a category error? What is the correct, minimal well-founded induction measure?

Q2. THE ATOM QUESTION. On the BINDING deeper stratum {rank Q_b <= q-2}, is ATOM-1 (full-space Γ integral,
    Gram-det weight det(Q_bQ_bᵀ)^{-p/2}) a valid route to the sharp threshold, or does integrating Γ over
    full space over-count / diverge relative to the true (bounded-box) integral? Is ATOM-2 (in-box radial
    blow-up + monomial ledger) the correct native mechanism there? Or is there a THIRD handling — e.g.
    recognising the Gram-det weight det(Q_bQ_bᵀ)^{-p/2} as itself the corank-Gram integral of a
    STRICTLY-SHORTER chain and RECURSING on it (a chain-length descent) with a corrected, lower threshold?

Q3. THE THRESHOLD ON THE DEEPER STRATUM. If Q_b = Y·A (Y the top corank rows, A = deeper product of the
    remaining layers, widths M2,...,M_last), what is the correct integrability threshold for
    ∫ det(Q_bQ_bᵀ)^{-a/2} in terms of the remaining widths? Is it governed by q (the free-Q value) or by
    min(M2,...,M_last) (the tightest remaining width)? Does a CONTRACTING tail (M2 < M_last) lower it?

Q4. WELL-FOUNDEDNESS. Aoyagi's literal inner loop uses a two-index (S,J) state where BOTH S and J can
    increase across the three branches (Case 1(1), Case 1(2), Case 2). Naively this is not obviously
    terminating. What is the minimal correct termination measure for the LITERAL inner (S,J) loop? Is
    there a strictly simpler alternative measure (e.g. chain-length / arity) if one descends by
    absorbing each resolved layer into the next factor rather than iterating the (S,J) coordinates?

Answer each question directly with your independent reasoning. Distinguish clearly what you can prove /
compute from what is inference. If you would compute a small exact example to decide Q2/Q3, name it.
</questions>

<output_contract>
- A direct verdict on Q1 (plain vs double induction; the correct measure).
- A direct verdict on Q2 (ATOM-1 vs ATOM-2 vs chain-length-descent on the binding deeper stratum), with
  the mechanism WHY (what goes wrong with the rejected atom).
- A direct answer on Q3 (the threshold: q-governed vs min-tail-governed; contracting-tail effect).
- A direct answer on Q4 (the minimal termination measure; literal (S,J) vs chain-length).
- Any place you think the framing above hides an error.
</output_contract>

<grounding_rules>
- Ground your reasoning in the exact objects above; if you need a fact not stated, name the assumption.
- Exact algebra only for any load-bearing arithmetic; a small symbolic example (e.g. p=q=1, or a 1x1
  degenerate Q_b) is welcome to decide the atom question — state it exactly.
- I am WITHHOLDING my own tentative conclusion deliberately. Do not try to guess and agree with it.
</grounding_rules>
