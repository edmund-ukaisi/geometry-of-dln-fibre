<task>
Analytic change-of-variables question about a determinantal (Gram) integral arising in
a resolution-of-singularities computation for deep linear networks. Adjudicate exactly.

Fix positive integers b, m, q. Let Y be a real b x m matrix and let Atail be a real m x q
matrix. Set Q := Y * Atail (a b x q matrix), and G := Q Q^T (b x b). Consider

    I(a) = ∫_{box} det(G)^{-a/2} d(Y, Atail)

integrated over a bounded box around a generic point, for a real exponent a>0. There is an
"abstract free-matrix core": if instead Q were a FREE b x q matrix (no product structure)
ranging over a box, then ∫ det(QQ^T)^{-a/2} dQ < ∞ iff a < q - b + 1.

The proposed reduction is: for fixed Atail (of rank >= b), change variables Q = Y*Atail in
the inner ∫_Y, producing a Jacobian J(Atail), so that
    I(a) = ∫_{Atail} J(Atail) * [free-core over the image] dAtail.

Answer these, with exact algebra (worked small instances encouraged):

Q1. Compute J(Atail) exactly for the map Y |-> Y*Atail (at fixed Atail). Handle three
    regimes separately: m = q (square), m > q, m < q. Express J via determinants/Gram
    matrices/singular values of Atail. Is J bounded, or singular somewhere?

Q2. Is the outer integral ∫_{Atail} J(Atail) * [free-core] dAtail a clean product of the
    free-core with a benign (bounded) factor, OR does J(Atail) constitute a new
    determinantal integral in its own right? If Atail = A2*A3*...*AL is itself a PRODUCT
    of matrices (so J is a function of that product), does the J-integral reduce to a
    strictly smaller/shorter problem of the SAME type (a recursion), and if so what is the
    shorter problem?

Q3. What is the exact convergence threshold on a for the ORIGINAL product integral I(a)
    (Q = Y*Atail), as a function of b, m, q? Compare it to the free-core value q - b + 1.
    Are they equal, or does the product structure change the threshold? Work the smallest
    non-trivial instances explicitly (e.g. b=1,m=1,q=2 ; b=1,m=2,q=3 ; b=2,m=2,q=3),
    computing det(QQ^T) as an explicit polynomial and finding the exact threshold.

Q4. The locus {rank Atail < min(m,q)} has measure zero but J may blow up there. Is this
    locus genuinely negligible for I(a), or does its contribution matter (and if so, how)?
    Distinguish m>=q from m<q.
</task>

<output_contract>
For each Q1-Q4: a PROVEN/DERIVED exact statement (mark any inference vs fact). J(Atail)
in closed form per regime. The exact threshold on a for I(a) as a formula in (b,m,q), with
at least one fully-worked explicit polynomial instance. A clear yes/no on whether the
reduction to the free-core is clean or hides extra content, with the mechanism.
</output_contract>

<grounding_rules>
Use exact algebra (sympy/by-hand). MC only to guide, never as proof. If you introduce a
local normal form / blow-up, state it and verify the exponent by explicit integration.
Do not assume the answer; if the threshold differs from q-b+1, show the smallest witness.
</grounding_rules>
