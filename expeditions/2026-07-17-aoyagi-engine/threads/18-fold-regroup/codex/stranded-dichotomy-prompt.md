# Independent check: a monomializing resolution's Jacobian vs a filtered ledger

Derive independently; I withhold my conclusions.

## Setup

A resolution of a singularity is built as a tree of blow-ups. Each blow-up "births" an exceptional
divisor; a divisor has a coordinate z_k, an integer "exponent" E_k ≥ 1, and a "clearing level" t̃_k ≥ 0
(a non-negative integer derived from a rank profile; t̃ = 0 means "analytic/terminal", t̃ > 0 means
"stranded"). The composite chart's Jacobian determinant is a monomial:

    |det D(chartMap)(w)| = ∏ over ALL born divisors k of |z_k(w)|^{E_k − 1}.

(one factor per divisor actually blown up — the FULL ledger.)

A separate object, the LOSS F (a sum of squared monomials), vanishes to order 2 exactly along each
ANALYTIC (t̃=0) divisor and does NOT vanish along stranded (t̃>0) divisors — those fold into a residual
core bounded away from 0 on the source box.

A construction filters the leaf ledger to the ANALYTIC (t̃=0) divisors only, and a headline theorem
claims:

    |det D(chartMap)(w)| = ∏ over ANALYTIC (t̃=0) divisors of |z_k(w)|^{E_k − 1}.

## Facts established by exhaustive simulation of the actual recursion

Reachable terminals routinely carry STRANDED divisors with E > 1. Minimal witness: a 1-layer network
with widths (2,3) reaches a terminal whose full ledger is { divisor A: E=6, t̃=0 ; divisor B: E=2, t̃=1 }.
The fold blows up BOTH A and B, so |det D chartMap| = |z_A|^5 · |z_B|^1, while the analytic-filtered RHS
is |z_A|^5.

## QUESTIONS

Q1. Is the headline (analytic-filtered RHS) TRUE or FALSE in general? Justify with the witness.

Q2. If FALSE, what is the honest Jacobian identity — the full-ledger form
    |det D chartMap| = ∏ over ALL divisors |z_k|^{E_k−1}, or an "analytic × stranded" factorization?
    State it precisely.

Q3. The downstream use is the RLCT / learning coefficient: the real log-canonical threshold of
    ∫ F(w)^{−λ} |det D chartMap(w)| dw near the origin (the smallest pole in λ). Do the stranded
    factors |z_k|^{E_k−1} (E_k ≥ 1, so a NON-negative power, and F does NOT vanish along z_k=0) change
    the location of the smallest pole? I.e. are the stranded factors "RLCT-inert"? Prove it or give a
    counterexample. (Consider: a bounded integral ∫_0^R z^{E−1} dz for E ≥ 1 has no pole in λ.)

Q4. Given Q1–Q3, what should the leaf's Jacobian statement quantify over so that (a) the identity is
    TRUE and (b) the RLCT read is unaffected? Be concrete about which ledger (analytic vs full) each
    consumer (the Jacobian identity; the loss factorization; the RLCT pole) should read.

Exact reasoning throughout.
