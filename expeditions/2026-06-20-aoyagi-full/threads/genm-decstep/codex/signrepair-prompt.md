<task>
Verify a resolution-of-singularities exceptional-power claim: does the transverse determinantal-blow-up
Jacobian repair the naive negative exponent UNIFORMLY across ALL rank strata (not just top / n=4)?

CONTEXT. RLCT of frobSq(P Z0 W), square chain (n,n,n,n), threshold c* = (1/2)minAdm(n,n,n,n). A resolution
stratifies by the rank of the corank contribution; on each stratum the peel reduces to a shorter chain
redChain(u', (n,n,n,n)) at a shifted exponent, where u' = u + (rank drop) and u = binding cut. The
naive pivot-Gram exceptional exponent on a deep stratum is NEGATIVE; a transverse determinantal-blow-up
Jacobian |det J| must repair it to > −1.

EXACT ARITHMETIC (verified). Label a stratum by the corank-at-the-deepened-cut value m = n − u' (0 ≤ m ≤ b,
b = n − u). The minAdm-recursion cut charge is peelCharge = (n−u')² = m². The per-stratum threshold is
    T_m = (m² + minAdm(u', n, n)) / 2,   u' = n − m.
This gives min_m T_m = c* AND EVERY stratum T_m ≥ c*, with the binding strata MARGINAL (T_m = c*, the
harmless log). Verified n=4..7 over all strata (e.g. n=4: T_0=6, T_1=11/2*, T_2=11/2*; c*=11/2). So with
the charge = m² = (corank-at-cut)², the exceptional powers stay ≥ threshold uniformly.

A CARE-POINT I FOUND. If one instead uses the charge (b−r)² labeled by the corank RANK r (so u'=u+(b−r)),
the two must be paired consistently: charge (b−r)² requires u' = u + r (r = rank DROP); charge r² requires
u' = u + (b−r) (r = rank). Mixing them (u'=u+(b−r) with charge (b−r)²) gives min_r = 7/2 ≠ c* = 11/2 for
n=4 — a spurious "undershoot". The correct invariant is charge = (corank at the deepened cut)² =
peelCharge(M, u'), regardless of labeling.

  Q1. Is the arithmetic claim correct — that with charge = (corank-at-cut)² = peelCharge(M, u'), EVERY
      rank stratum has threshold T_m ≥ c* (so the exceptional powers a_i − 2c'·N_i > −1 for all c' < c*,
      at every stratum, binding strata marginal)? Recompute for n=5 or n=6 across all strata and confirm
      or refute.

  Q2. THE ANALYTIC CRUX. Is "the transverse determinantal-blow-up Jacobian |det J| = the codim
      (corank-at-cut)²" a STANDARD resolution-of-singularities fact (detail-at-scale, buildable) — i.e.
      for the rank-stratum of the relevant determinantal variety, the ambient blow-up's Jacobian is the
      exceptional divisor to the power (codim − 1), and combined with the loss vanishing order it yields
      exactly the T_m above? Or is there a genuine obstruction: the relevant variety is a RELATIVE
      determinantal incidence (the residual Γ·Q_b·(I−P) lives in the quotient by the pivot row space,
      Q_b(I−P)·Q̃ₚᵀ = 0), and its transverse Jacobian may NOT equal the naive determinantal codim —
      requiring a bespoke relative-quotient computation. State precisely the determinantal-resolution fact
      and whether the RELATIVE (pivot-coupled) setting changes the Jacobian power.

  Q3. Does the repair hold at EVERY stratum, or is there a specific deep stratum (small m, i.e. large rank
      drop) where even the transverse Jacobian leaves a net exponent ≤ −1? Give the smallest n and stratum
      where it would first fail, if any.

  Q4. Net: is the "transverse-Jacobian = (corank-at-cut)² codim, exceptional powers > −1 uniform" a PROVEN
      / standard-technique claim ready for a formaliser (with the arithmetic as the certificate), or does
      the RELATIVE-quotient setting hide a genuine sub-gap in the Jacobian computation?
</task>

<output_contract>
Answer Q1-Q4 in order. Q1: recompute one n across all strata (show the numbers). Q2/Q3 are the crux: the
analytic |det J| = codim identity in the RELATIVE (pivot-coupled) setting. Flag PROVEN (standard
determinantal-resolution fact you state) vs INFERENCE. End with a one-line verdict:
UNIFORM-REPAIR-STANDARD-TECHNIQUE / GAP-IN-RELATIVE-JACOBIAN / SIGN-FAILS-AT-<n,stratum>.
I have withheld my own tentative verdict; do not assume it.
</output_contract>

<grounding_rules>
Distinguish the exact-arithmetic (the T_m ≥ c* budget, recomputable) from the analytic Jacobian claim
(the |det J| = codim in the relative setting). The load-bearing question is Q2/Q3: whether the transverse
Jacobian of the RELATIVE (pivot-quotient) determinantal incidence equals the naive codim, uniformly. State
the standard determinantal-blow-up Jacobian fact (exceptional divisor to power codim−1) and whether the
relative quotient preserves it. Do not paste Lean or long code.
</grounding_rules>
