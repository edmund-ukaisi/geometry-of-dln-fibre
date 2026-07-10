IMPORTANT: read-only sandbox. Do NOT run any shell/python/code — rejected. Reason by hand with exact
linear algebra; work small cases (2x2, 3x3) mentally.

<task>
Establish, by an EXPLICIT change of variables (normal form), a "normal-slice" isomorphism for a matrix
PRODUCT, and read off its Jacobian and exponent bookkeeping. This underpins a deep-linear-network RLCT
recursion; I need the explicit CoV, NOT an abstract existence argument.

SETUP. A "tail chain" of widths (m_1, m_2, ..., m_L) has real matrices X_i : m_i x m_{i+1} for i=1..L-1,
and product P = X_1 X_2 ... X_{L-1} : m_1 x m_{L}. Fix an integer q with 0 <= q <= min_i m_i.

I want the singularity structure of the locus {rank P <= q} (equivalently the behaviour of an integrand
that degenerates there), and specifically the claim:

  (*) Near a generic rank-q point, {rank P <= q} is isomorphic (by an explicit CoV with UNIT Jacobian
      determinant — no determinant inverse) to the DEEPEST locus Sigma^0 of the REDUCED chain
      (m_1 - q, m_2 - q, ..., m_L - q), i.e. {Y_1 Y_2 ... Y_{L-1} = 0} with Y_i : (m_i - q) x (m_{i+1} - q).

CONTEXT / what is already known (do not redo):
- For a SINGLE matrix (L=2, P = X_1 : m_1 x m_2), this is the Schur complement: on the chart where the
  top-left q x q block a is invertible, X_1 = [[a,b],[c,d]], and the Schur complement Gamma = d - c a^{-1} b
  ((m_1-q)x(m_2-q)) satisfies {rank X_1 <= q} = {Gamma = 0}; the map (a,b,c,d) -> (a,b,c,Gamma) is a shear,
  Jacobian 1, and a^{-1} appears only as a UNIT coefficient (never a Jacobian determinant). This is the base.
- The combinatorial "codimension budget" minAdm satisfies the exact recursion
  minAdm(m_0, m_1, ..., m_L) = min_{q} [ m_0 * q + minAdm(m_1 - q, ..., m_L - q) ]  (front-peel identity),
  and minAdm(a,b) = a*b. So the reduced chain's own budget is minAdm(m_1-q, ..., m_L-q).

<output_contract>
1. Give the EXPLICIT CoV for the PRODUCT case (L >= 3). Concretely: on the chart where a suitable q x q
   pivot of P (or of the running products) is invertible, block-decompose each X_i in a q + (m_i - q) row
   / q + (m_{i+1} - q) column splitting, and produce the reduced-chain matrices Y_i : (m_i-q) x (m_{i+1}-q)
   as explicit Schur-type complements. Show that {rank P <= q} <=> {Y_1 ... Y_{L-1} = 0}. Be fully explicit
   for L=3 (tail (m_1,m_2,m_3), P = X_1 X_2), and state the general recursion.
2. Compute the Jacobian of the CoV. Confirm it is a UNIT (its determinant is +/-1 or a nonvanishing
   product of pivot units — NO determinant inverse survives as a Jacobian factor). Identify exactly where
   pivot inverses appear and why they stay as unit coefficients (the base-case discipline extended).
3. The exponent bookkeeping. The front matrix X_0 : m_0 x m_1 is peeled against P by X_0 -> X_0 U
   (U : m_1 x q a basis of im P), an isotropic Morse block of dimension m_0 * q, giving an exponent shift
   m_0 * q / 2. Show this shift ADDS to the reduced chain's threshold (1/2) minAdm(m_1-q,...,m_L-q), i.e.
   the total is (1/2)[ m_0 q + minAdm(reduced) ], matching the front-peel identity. Explain why it is a SUM
   (additive on a common exceptional/normal-slice divisor), NOT a min of the two.
4. A subtlety to address: the raw codimension of {rank P <= q} in the tuple space is NOT equal to
   minAdm(reduced) for products (e.g. tail (3,3,3), q=1: codim{rank(X_1 X_2)<=1} = 4, but
   minAdm(2,2,2) = 3). So (*) must be an RLCT / singularity-type statement, not a codim-preserving
   embedding. Explain: which extra directions in {rank P <= q} are NON-singular (contribute nothing to the
   RLCT) so that RLCT({rank P <= q}) = (1/2) minAdm(reduced) even though the codim is larger. For (3,3,3),
   q=1: exhibit the reduced (2,2,2) product structure and account for the 4 vs 3.
5. Flag any step where the CoV is only LOCAL (chart-dependent) and what the finite chart cover is, and any
   place a genuine determinant inverse would appear if one took a wrong normalization.
Distinguish FACTS you derive by exact linear algebra from INFERENCE/heuristic.
</output_contract>

<grounding_rules>
- Exact linear algebra; explicit block matrices for L=3. Schur complements, unit-triangular (det 1)
  row/column operations only. Frobenius norm squared is a sum of squares.
- RLCT convention: rlct(sum of monomials) via the Newton polytope; disjoint-variable sums add.
- I have NOT told you my construction beyond the base case; derive the product CoV yourself. If (*) is
  false as stated, say so and give the corrected reduced structure.
</grounding_rules>
</task>
