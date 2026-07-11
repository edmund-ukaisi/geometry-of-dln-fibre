<task>
An exact question about the codimension / tube-exponent of a product-rank locus, arising in a
finiteness (RLCT lower-bound) computation for deep linear networks. Adjudicate exactly and
adversarially — I want to know if a certain leading-power claim can FAIL at some width class (a wall),
not a reassurance that it holds.

SETUP. Real matrices A_1,...,A_{L-1} with A_i of size (m_i x m_{i+1}); widths (m_1,...,m_L). Let
P = A_1 A_2 ... A_{L-1} (an m_1 x m_L matrix), a genuine PRODUCT (L-1 >= 2 factors). Fix a corank q,
put s = q-1, and consider the locus V_s = { (A_i) : rank(P) <= s } in the FACTOR space (Lebesgue
measure on the entries of all factors). Two objects:

  (a) the algebraic codimension  D = codim(V_s)  in the factor space;
  (b) the "tube leading power"  L such that  vol{ (A_i) : sigma_{s+1}(P) <= t }  ~  C t^L  (t->0),
      where sigma_{s+1}(P) is the (s+1)-th singular value of P (so sigma_{s+1}(P)->0 <=> rank P <= s).
      This is the exponent the integral  ∫ sigma_{s+1}(P)^{-alpha} d(factors)  actually rides on:
      it converges iff alpha < L.

There is a proposed closed form: with `minAdm(d_1,...,d_n)` the codimension of the ZERO-PRODUCT locus
{ B_1...B_{n-1} = 0 } of a chain of widths (d_1,...,d_n) (the type-A quiver / Lehalleur-Rimanyi "C",
= the QIP minimum for monotone widths), the claim is
    D = minAdm(m_1 - s, m_2 - s, ..., m_L - s)      (ALL widths reduced by s),
and moreover the tube leading power L EQUALS this D (any multiplicity from multiple top-dimensional
components contributing only a logarithmic factor, not a power reduction).

Answer these, exactly:

Q1. Is  codim{ rank(A_1...A_{L-1}) <= s }  =  minAdm(m_1-s,...,m_L-s)  for a general product (all L,
    all widths)? Prove or give the mechanism (a rank normal-form / reduction to a zero-product locus of
    reduced widths is a candidate). Does it equal the type-A quiver codimension C of the reduced chain
    (Lehalleur-Rimanyi rank-shift Lemma: C at rank r = C at rank 0 of widths reduced by r)? Verify on a
    2-layer product (widths (3,3,4), s=1) and a 3-layer product (widths (3,3,3,4), s=1).

Q2. Does the TUBE leading power L equal the algebraic codim D for a general product, or can it be
    STRICTLY SMALLER (a genuine power reduction, not a log) for some width class? In particular consider
    a NARROW INTERNAL WIDTH (e.g. widths (3,1,3): an internal width 1 forces rank(P)<=1 generically),
    and multiscale / several-factors-simultaneously-degenerate configurations. If L can drop below D
    for some widths, EXHIBIT the width class and the exponent; if not, prove L = D (with logs only).

Q3. The measure on P is the PUSHFORWARD of Lebesgue on the factors, not Lebesgue on P. Does this
    distinction change the tube exponent versus a single free matrix of the same shape? (For a single
    free matrix, the determinantal tube exponent is the classical determinantal codim.) Does the
    pushforward concentrate mass near the locus enough to lower the exponent?

Q4. Given `minAdm`, does the inequality  minAdm(m_0, m_1,...,m_L)  <=  D + m_0*(q-1)  hold for all
    widths and all coranks q (with D the product-rank codim of Q1)? Is it tight, and is it just the
    (j=q-1) term of the front-peel identity minAdm(M) = min_j [ m_0*j + minAdm(m_1-j,...,m_L-j) ]?
</task>

<output_contract>
For each Q1-Q4: PROVEN/DERIVED exact statement (mark inference vs fact). A clear YES/NO on whether the
tube leading power can drop STRICTLY below the algebraic codim for some width class (a wall) — with the
exhibited witness if yes. The closed form for D (confirm or correct minAdm(reduced)). Whether the
Core/quiver codim C(reduced) = D. Worked (3,3,4) s=1 and (3,3,3,4) s=1.
</output_contract>

<grounding_rules>
Exact algebra (sympy/by-hand); MC only to guide. For the tube exponent, either give a local normal
form and integrate the transverse exponent explicitly, or reduce to a known determinantal/zero-product
tube whose exponent is established. Watch the narrow-internal-width regime where rank drop is generic
rather than a null event. Do NOT read my expectation into the answer — I have deliberately not stated
which way I think the tube-vs-codim question goes; hunt for the wall.
</grounding_rules>
