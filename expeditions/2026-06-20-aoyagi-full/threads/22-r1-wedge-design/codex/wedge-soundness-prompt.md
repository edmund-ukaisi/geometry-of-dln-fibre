<task>
Adjudicate a measure-theory / resolution-of-singularities design question for a Lean formalisation.
We must prove a BOX-INTEGRAL DIVERGENCE (a lower bound on an integral, = ⊤), and want the
LIGHTEST honest construction. Give an independent verdict; do not rubber-stamp.
</task>

<setup>
Fix a tuple of natural-number "widths" M = (M_0, M_1, ..., M_L), L ≥ 1.
- Parameter space: tuples of real matrices A^(1) (size M_0×M_1), ..., A^(L) (size M_{L-1}×M_L),
  flattened into x ∈ ℝ^N where N = Σ_s M_{s-1}·M_s (the "flat coordinates").
- The loss F : ℝ^N → ℝ is F(x) = ‖A^(1)·A^(2)·…·A^(L)‖_F^2  (squared Frobenius norm of the matrix
  product), a polynomial, F(0)=0, F ≥ 0.  This is a deep-linear-network multiplication loss.
- A combinatorial invariant minAdm(M) ∈ ℕ is known (the minimal "admissible codimension"); it equals
  a layer-peeling recursion:
      minAdm(M_0,...,M_L) = min_{0≤t≤min(M_0,M_1)} [ (M_0−t)(M_1−t) + minAdm(t, M_2, …, M_L) ],
      leaf minAdm(M_0,M_1) = M_0·M_1.
  Example: minAdm(2,2,2)=3; minAdm(3,3,4)=8.

GOAL ATOM (the thing to prove):  for every real c' ≥ minAdm(M)/2 and every ε>0,
      ∫_{[−ε,ε]^N} |F(x)|^{−c'} dx = +∞.
This is the divergence (lower-bound) half of an RLCT computation; combined with a matching upper
bound it gives rlctAtOn(F) = minAdm(M)/2. We ONLY need this ⊤ divergence here (one direction).
</setup>

<what_is_already_proven>
For the SPECIAL case M=(2,2,2) (N=8, minAdm=3, threshold 3/2) the divergence is proven via a
COMPOSED BLOW-UP CHART phi: a composition of two pivot blow-ups (each of the form
  pivotBlowup: (y_pivot, y_1, ..., y_k) ↦ (y_pivot, y_pivot·y_1, ..., y_pivot·y_k))
plus one regular (det ±1) linear change. The proven facts:
  (1) phi(0)=0, phi continuous, and phi maps a small box [0,δ]^8 INTO the cube [−ε,ε]^8.
  (2) A factorization F(phi(u)) = u_0^2 · u_2^2 · U(u), where U(u) ≥ 1 everywhere (a sum of 1 and
      squares: a UNIT bounded below).
  (3) The Jacobian |det Dphi(u)| = u_0^3 · u_2^2 on the active set.
  (4) Change-of-variables turns ∫_{phi''(box)} |F|^{−c'} into ∫_{box} |det Dphi|·|F∘phi|^{−c'}
      = ∫_{box} u_0^3 u_2^2 (u_0^2 u_2^2 U)^{−c'}.  Since U≥1, U^{−c'}≤1, dropping it LOWER-bounds
      the integral by ∫ u_0^{3−2c'} u_2^{2−2c'}, which at c'=3/2 is ∫ u_0^0 · u_2^{−1} = ⊤ (the u_2
      axis is the binding axis; exponent 2−2·(3/2) = −1).  Then phi''(box) ⊆ cube and monotonicity
      give ∫_{cube}|F|^{−c'} = ⊤.
The COMBINATORIAL model says the general-M achiever leaf carries a SINGLE binding divisor with
(k,h)=(1, minAdm−1), so the resolved chart should give F∘phi = u_b^2·U (U≥c0>0) and
|det Dphi| = u_b^{minAdm−1}·(positive), making ∫ u_b^{minAdm−1}(u_b^2)^{−c'} = ∫ u_b^{minAdm−1−2c'}
diverge at c'=minAdm/2 (exponent = −1).
</what_is_already_proven>

<the_blocker>
A prior adjudication recorded: the (2,2,2) composed chart "is a depth-2 miracle that does NOT
generalise — the Jacobian tower loses triangularity after the first pivot." For (3,3,4) the achiever
is a CORANK-2 node (after peeling a rank-1 pivot, a free 2×2 residual block Δ remains, coupled to a
2×4 residual S); a per-node RANK-1 factorization fails there. minAdm(3,3,4)=8 is an ACCUMULATED codim
over a CHAIN of blow-ups, not a single blow-up.
</the_blocker>

<questions>
Q1. For the LOWER-BOUND atom only (we need ∫|F|^{−c'} ≥ a divergent integral; we may freely shrink
    the domain and drop positive factors), is there a LIGHTER construction than a full composed
    resolution chart?  Specifically evaluate this candidate "achiever wedge":
      - a monomial CURVE γ(s) → 0 (s∈(0,δ]) in flat coords with an explicit flat MONOMIAL UPPER
        BOUND F(γ(s)+tube) ≤ C·(binding monomial), valid on a TUBULAR box T_s around γ(s);
      - a Fubini reduction ∫_T |F|^{−c'} ≥ ∫_s vol(T_s)·(C·s^{a})^{−c'} ds reducing to a 1-D test
        integral ∫_0^δ s^{−1} ds = ⊤ at c'=minAdm/2.
    Does such a wedge SOUNDLY certify the divergence, and is it genuinely lighter (avoids the
    Jacobian-tower triangularity loss)? What is the soundness pitfall (e.g. the flat monomial upper
    bound failing to hold on a positive-MEASURE set, vs only on the curve)?

Q2. The corank-2 coupling at (3,3,4): does it HELP or HURT the lower bound? (Intuition: extra
    coupling makes F vanish FASTER along the achiever, which makes |F|^{−c'} LARGER, helping
    divergence — so the lower bound should be corank-IMMUNE. Is that right, or is there a trap where
    "F vanishes faster" actually RAISES the threshold and breaks divergence at c'=minAdm/2?)

Q3. There is a SECOND atom (the UPPER bound / completeness, "hfin": the recursively-generated charts
    cover the box up to null, giving rlctAtOn ≥ minAdm/2). Is the upper bound CORANK-SENSITIVE in the
    same way the refuted per-node rank-1 factorization was — i.e. does proving the upper bound REQUIRE
    the full coupled-diag(b) chart structure (as hard as the refuted route), or can it be done more
    cheaply? Give your best structural read.
</questions>

<output_contract>
For each Q: VERDICT (one line) + the load-bearing reason + the most likely failure mode. Distinguish
what is a theorem from what is heuristic. If the wedge is unsound, say exactly where. If a full chart
is unavoidable for either bound, say so and name why. Keep it tight.
</output_contract>

<grounding_rules>
Reason from the structure above. The "binding axis exponent = −1 at threshold" is the load-bearing
mechanism. Do not assume a Lean lemma exists; reason mathematically. State inference vs fact.
</grounding_rules>
