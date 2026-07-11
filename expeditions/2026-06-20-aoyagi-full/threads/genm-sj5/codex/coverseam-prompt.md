<task>
An analytic finiteness / change-of-variables question about a determinantal (Gram) integral
arising in a resolution-of-singularities computation for deep linear networks. Adjudicate exactly,
and adversarially: I want to know whether a specific reduction route WALLS (has a genuine divergence)
or is finite. Do NOT assume it is finite; hunt for the divergence.

FIXED SETUP. Real matrices Y (b x m) and A (m x q) with m < q (the "contracting" regime). Set
Q := Y*A  (b x q) and consider the box integral (entries of Y and A in [-1,1], box contains origin)

    I(a) = ∫_box det(Q Q^T)^{-a/2} d(Y,A),      a > 0 real.

Concrete instances I care about: (b,m,q) = (2,3,4) and (1,3,4) (these come from resolving the chain
(3,3,3,4) at a binding corank cut), plus toy witnesses (1,1,2), (2,2,3), (1,2,3).

THE ROUTE UNDER SCRUTINY ("det-inverse dominant-minor cover"). For fixed A of full row rank m, one
changes variables in the inner ∫_Y via Q_S := Y*A_S where A_S is an m x m column-block of A (a choice
of m of the q columns, S), Jacobian dY = |det A_S|^{-b} dQ_S. To keep |det A_S|^{-b} controlled one
covers A-space by the finitely many charts {S : |det A_S| is the largest m x m minor} ("dominant-minor
cover"). On chart-S one rewrites the reduced core over the (A-dependent, "shrinking") image of the box,
and the |det A_S|^{-b} Jacobian is supposed to cancel against that shrinking image.

THE FEARED FAILURE MODE (from a sibling "atom" route). If instead one integrates the corank block over
FULL space (not the box), one manufactures a divergence the true box integral does not have. The exact
1-D signature: ∫_R (s^2 z^2 + w)^{-c} dz = K_c * s^{-1} * w^{1/2-c}  (an s^{-1} pole), whereas the box
version ∫_{-1}^1 (s^2 z^2 + w)^{-c} dz -> 2 w^{-c} (bounded, NO s^{-1}). The worry is that the
dominant-minor cover, via the |det A_S|^{-1}-type Jacobian and the chart SEAM (the boundary
{|det A_S| = |det A_{S'}|} where the dominant minor switches), reintroduces this s^{-1}/Beta-type
divergence -- i.e. a divergent boundary/seam term.

Answer these:

Q1. Does partitioning the box integral into the finitely many dominant-minor charts create any
    boundary/seam term at all? On the seam {|det A_S| = |det A_{S'}|}, is the integrand
    det(QQ^T)^{-a/2} singular or bounded (away from the deep rank-drop locus)? Give the exact status.

Q2. On chart-S, after the CoV Y->Q_S, is the |det A_S|^{-b} Jacobian genuinely cancelled, or can a
    residual det-inverse survive and diverge -- either at the seam, or as A_S -> singular along the
    seam, or where TWO or more m x m minors vanish simultaneously (rank(A) <= m-2)? Distinguish a
    divergence of the true integral I(a) from a divergence of a particular per-chart BOUND.

Q3. Independently of the cover: what is the exact convergence threshold a_c for I(a) as a function
    of (b,m,q) in the m<q regime, and what is the CLEANEST way to PROVE finiteness up to a_c (e.g. a
    Gaussian/Wishart moment bound, or a Cauchy-Binet single-minor lower bound det(QQ^T) >= a squared
    minor)? Does the cleanest finiteness route need the dominant-minor cover / the seam at all?

Q4. Steelman a WALL: is there ANY configuration (deep corner reached along a seam; rank-drop-by->=2;
    the exponent a sitting exactly at the threshold) where this reduction genuinely fails to deliver
    finiteness for a < a_c -- as opposed to merely a lossy bound? If yes, exhibit it; if no, say why.
</task>

<output_contract>
For each Q1-Q4: a PROVEN/DERIVED exact statement (mark inference vs fact). The exact a_c(b,m,q). A
clear YES/NO on whether a Beta/seam divergence survives (and whether it is a divergence of I(a) itself
or only of a particular bound). A clear YES/NO on whether the cleanest finiteness route needs the
dominant-minor cover. If you find a genuine wall, exhibit the exact witness.
</output_contract>

<grounding_rules>
Exact algebra (sympy/by-hand); MC only to guide, never as proof. If you introduce a local normal form
or blow-up, state it and verify the exponent by explicit integration. Do not assume the reduction is
clean; if it hides content or walls, show the smallest witness. Do not read my expectation into the
answer -- I have deliberately not stated which way I think it goes.
</grounding_rules>
