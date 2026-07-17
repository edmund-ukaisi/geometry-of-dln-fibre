<task>
You are red-teaming the finiteness proof of ONE Lean integral (a step in a formalisation of
Lehalleur–Rimanyi "Geometry of the fibers of the multiplication map of deep linear networks").
I need you to independently judge whether TWO analytic sub-steps close with only the stated
"banked" tools, or whether each hides genuinely-new content. WITHHOLD nothing about the math;
I am withholding MY tentative verdict on purpose.

SETUP (exact objects).
A DLN "chain" is a width vector M = (M0, M1, M2, ..., M_last), M : Fin (L+3) -> N.
"prod M A" = product of the layer matrices A_i (A_i is M_i x M_{i+1}), i.e. an M0 x M_last matrix.
frobSq(X) = sum of squares of entries. The paper's box-finiteness target is:
  RouteMBoxThresholdFinite(M): for all c' < minAdm(M)/2,
     INT_{A in box} frobSq(prod M A)^(-c') d A  <  infinity   (box = all entries in [-1,1]).
minAdm(M) is an integer "codimension" with the recursion
   minAdm(M) = min over t in [0, min(M0,M1)] of  (M0-t)(M1-t) + minAdm(redChain t M),
where redChain t M = (t, M2, ..., M_last)  (collapses the first TWO widths into one width-t layer).
peelCharge(M,t) = (M0-t)(M1-t). Cut-soundness (proved): minAdm(M) <= peelCharge(M,t) + minAdm(redChain t M).

We are proving RouteMBoxThresholdFinite(M) by strong induction on the number of layers, GIVEN the
"plain IH":  hIH : for every SHORTER chain M', RouteMBoxThresholdFinite(M').  The proof peels a cut t
(1 <= t <= min(M0,M1)); after a measure-preserving Schur weld + shear, the per-cut integral becomes
the "freed-Gamma triple integral" over (A', x, Gamma):

  INT_{A'} INT_{x=(P,B12,C) in outerDom} INT_{Gamma in shearbox}  (freedSchurLoss x Gamma Q)^(-c')

where, writing a = M0 - t, b = M1 - t (the "corank block" dimensions), u = t (pivot width),
  - P is t x t and INVERTIBLE on outerDom; B12 is t x b; C is a x t; Gamma is a x b (free).
  - Q = the tail product prod((M1,M2,...,M_last), A') reindexed to rows (Fin t (+) Fin b); q := M_last cols.
  - Q_p := top t rows of Q (t x q); Q_b := bottom b rows of Q (b x q).  [Q_p, Q_b are PRODUCTS of deeper layers, NOT free matrices.]
  - Qtil := Q_p + P^{-1} B12 Q_b   (t x q, "pivot-shifted tail", generically full row rank t).
  - freedSchurLoss = frobSq(P * Qtil) + frobSq(C * Qtil + Gamma * Q_b).
    NOTE: frobSq(P*Qtil) = frobSq([P|B12] * Q) = frobSq(X * Q), X := [P|B12] (t x M1, full row rank t).

The dispatch is on d := min(a,b).  d>=2 is CITED (Aoyagi product-corank) — NOT your concern.
Your concern is d <= 1, to be closed NATIVELY with the plain hIH + these BANKED lemmas ONLY:
  (G) gammaAtom:  INT_{Gamma:pxq'} (w + frobSq(Gamma*R + S))^(-c') dGamma
        = det(R R^T)^(-p/2) * Cresid(p*q') * (w + frobSq(S*(I - P_R)))^(-(c' - p*q'/2)),
        valid when R R^T is positive-definite (R full ROW rank), w>0, and c' > p*q'/2.  P_R = R^T (RR^T)^{-1} R.
  (Q) qbox:  INT_{Q in box of b rows in R^q} det(gram Q)^(-a/2) d Q < infinity  iff  b <= q and a < q - b + 1.
        [gram Q = Q Q^T; this is over a FREE box of rows, NOT a product.]
  (C) corner_block:  INT_{omega in sphere S^{N-1}} g(omega)^(-c') < infinity for a degree-2 homogeneous g
        bounded below on the sphere, when c' < N/2.  Used as INT_omega ||Qtil * omega||^(-a) < infinity  iff  a < u.
  (R) scaledRadialEuclid: INT_{x in R^a} (w + ||x||^2)^(-p) dx < infinity iff a < 2p (finite = c * w^{a/2 - p}).
  (S) sumSqND box radial (a single sum-of-squares leaf).
  hIH: plain RouteMBoxThresholdFinite of any shorter chain.
NOTE the hard constraint: hIH is a BLACK-BOX finiteness of the UNDECORATED reduced box integral
  INT frobSq(prod (redChain t M) A'')^(-c'') d A''  for c'' < minAdm(redChain t M)/2.
It does NOT give finiteness of a GRAM-WEIGHTED reduced integral
  INT det(leadingGram)^(-a/2) * frobSq(prod (redChain t M) ...)^(-c'') .
So: if a step leaves a NEGATIVE-POWER Gram weight det(Qtil Qtil^T)^(-a/2) (Qtil a deeper PRODUCT, not a free box)
riding ON TOP of the reduced box, that weight canNOT be discharged by the plain hIH (that would need a
"decorated" IH the design is trying to avoid), NOR by qbox (Q) unless it is over a FREE box at a single level.

===================================================================================================
QUESTION 1 (the d=1 "a >= u" residual — does it close with plain hIH + banked atoms, or need a decoration?).
Take d=1 with b=1 (so Q_b is a single row, 1 x q; Gamma = gamma is an a-vector; a >= 1). Split the corank energy
  frobSq(C*Qtil + gamma (x) Q_b) = ||C*v + sigma*gamma||^2 + ||C*Qtil*(I - P_{Q_b})||^2,
where omega = Q_b/||Q_b||, v = Qtil * omega^T (a t-vector), sigma = ||Q_b||.  Two known regimes:
  * a < u:  DROP the transverse term ||C*Qtil(I-P_{Q_b})||^2 >= 0; the Gamma+C integral collapses to
    |v_{j0}|^{-a} * scaledRadialEuclid(w, c'), w = frobSq(P*Qtil) is C-free; dispose INT_omega ||Qtil omega||^{-a}
    via (C) [finite iff a<u]; then w reduces to the reduced chain via hIH.  CLEAN, plain-hIH.
  * a >= u:  dropping the transverse is LOSSY (INT ||v||^{-a} DIVERGES for a>=u). One must KEEP the transverse and
    integrate C via gammaAtom (G) with R = Qtil (full row rank u), p = a, q' = u:
    this produces the PIVOT-GRAM weight det(Qtil Qtil^T)^(-a/2) times a reduced loss, spending a*u/2 on C.
For the a >= u regime, adjudicate SHARPLY:
  (1a) Is there ANY route (choice of integration order, which block to integrate via gammaAtom, what to drop)
       that closes the a>=u d=1 cut using ONLY plain hIH + the banked atoms (G,Q,C,R,S), WITHOUT leaving a
       det(product-Gram)^(-a/2) weight that needs a decorated IH?  If yes, give it concretely (dims + charges,
       and show the total charge stays <= minAdm(M)/2 via cut-soundness).  If no, say so and explain the obstruction.
  (1b) The proposed disposal is "det(Qtil Qtil^T)^(-a/2) is the reduced chain's OWN leading Gram, disposed by
       qbox (Q) at a single reduced level; the marginal cells recurse."  But Qtil = W' * Zdeep is a PRODUCT (W'
       the reduced leading layer, Zdeep the deep product), NOT a free box.  Can qbox (Q) legitimately dispose a
       Gram of a PRODUCT?  If not at one level, does the "recurse one more level" step actually terminate using
       only plain hIH — or does it require carrying the Gram weight through the recursion (a decoration)?
  (1c) VERDICT for Q1: EXPENSIVE-TRANSCRIPTION (route exists, only Lean labour) or OPEN-PROBLEM (genuinely-new
       content / needs a decorated IH). If OPEN, name the minimal missing lemma precisely.

===================================================================================================
QUESTION 2 (the d=0, a=0 "wide waist" density — native single-factor, or hidden joint incidence?).
d=0 occurs only at the deepest cut t = min(M0,M1). Take a = 0 (so M0 <= M1, t = M0, b = M1 - M0 >= 0).
Then Gamma has 0 rows, the corank term vanishes, and freedSchurLoss = frobSq(P*Qtil) = frobSq(X*Q),
X = [P|B12] is M0 x M1 of FULL ROW RANK M0 (P invertible), Q the tail product (M1 x q).  Reducing to
redChain M0 M = (M0, M2, ..., M_last) needs the pushforward of (X, A_1) |-> W := X*A_1 (A_1 = first tail layer,
M1 x M2), i.e. the density rho(W) of a product of a full-row-rank wide matrix X and a boxed matrix A_1.
peelCharge = 0 here, so NO charge is spent; the reduction must reach c' < minAdm(M)/2 directly against
redChain M0 M, whose threshold is HIGHER by Delta := (minAdm(redChain M0 M) - minAdm(M))/2 >= 0 (cut-soundness).
The claimed density order at rank-drops of W is A = max_{j>=1} j*(M2 - b - j) (b = M1 - M0).
Two arms are claimed: A <= 2*Delta -> pointwise "density fold" rho(W) <= K * frobSq(W*Zdeep)^(-A/2), single chain,
plain hIH;  A > 2*Delta -> a per-stratum determinantal blow-up of {rank W = r}, multi-chain, with
min over strata of [ (M0-s)(M1-s) + minAdm(redChain s M) ] = minAdm(M) (an exact-integer identity, verified).
Adjudicate SHARPLY:
  (2a) Since X is ALWAYS full row rank M0 (only the deeper factor A_1/Y drops rank), is the rank-drop of W a
       SINGLE-factor (submersive) determinantal event with the ordinary codim (M0-r)(M2-r) — or can it hide a
       JOINT (both-factor, non-submersive) product-corank incidence (codim k^2 - floor(k^2/4) < k^2) like the
       d>=2 cited case, on any sub-locus?  Give the cleanest discriminating check.
  (2b) Is the A <= 2*Delta pointwise density fold SOUND at the MEASURE level (not just pointwise): does
       rho(W) <= K * frobSq(W*Zdeep)^(-A/2) hold as a measure-domination that survives integration, given
       Zdeep is itself a boxed deep product that can degenerate?  Or is there a set where the fold fails?
  (2c) Is the A > 2*Delta per-stratum blow-up EXPENSIVE-TRANSCRIPTION (standard determinantal resolution +
       the verified min=minAdm arithmetic) or OPEN-PROBLEM (a genuinely-new measure-level theorem)?  Name the
       minimal missing lemma if OPEN.

Also flag: any place where the b=0 mirror (tall front [P;C], M1<=M0, corank empty, front full COLUMN rank M1,
Wishart det(P^T P + C^T C)^(-M2/2) via qbox with (b,q,alpha)=(M1,M0,M2)) is NOT a clean transpose of a=0.
</task>

<output_contract>
  Two sections, "Q1" and "Q2". For each: answer the numbered sub-parts (1a/1b/1c, 2a/2b/2c) tersely, then a
  one-line VERDICT tag per question chosen from {EXPENSIVE-TRANSCRIPTION, OPEN-PROBLEM, MIXED}. If MIXED, say
  exactly which arm is which. Name any minimal missing lemma in one precise sentence (dims + what it asserts).
  Distinguish PROVEN vs ARGUED vs GUESS for each claim. End with the single cheapest discriminating computation
  that would settle the biggest remaining uncertainty. Be concrete about dims and charges; no hedging prose.
</output_contract>

<grounding_rules>
  Reason from the exact objects above. The banked atoms (G,Q,C,R,S) are the ONLY analytic tools for the native
  arm besides plain hIH; do not assume a decorated/Gram-weighted IH is available (its avoidance is the whole
  point). "det(product-Gram)^(-a/2) riding on the reduced box" is disposable ONLY if (i) it is over a free box
  at a single level (then qbox), or (ii) it provably factors off without crossing into the hIH recursion.
  State inference vs fact. Do not rubber-stamp; if a step is unsound or a route is missing, say so.
</grounding_rules>
