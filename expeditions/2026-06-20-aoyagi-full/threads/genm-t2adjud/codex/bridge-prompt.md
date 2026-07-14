<task>
Adjudicate a soundness question about an inequality between two Lebesgue integrals that
arises in a change-of-variables/stratification argument for a real-log-canonical-threshold
(RLCT) computation. Judge it as pure real analysis / measure theory. I want an INDEPENDENT
verdict — do not try to guess what answer I am hoping for.

SETUP (all objects are concrete; verify the logic, do not trust my naming).

Fix natural numbers M0, M1, n with 1 ≤ M0, M1 ≤ n, and a threshold ε > 0, and a cut u with
1 ≤ u ≤ M1. Write a = M0 − u, b = M1 − u (so u+a = M0, u+b = M1).

There is a "front product" W = A ⋅ Z where A is an M1×M2 matrix drawn from a box
[−1,1]^{M1×M2} and Z is an M2×n matrix (a deterministic function of other box parameters).
So W is M1×n. Let s_1 ≥ s_2 ≥ … be the singular values of W, and define
   weakEigCount(ε, W) = #{ i : s_i(W) < ε }   (number of singular values below ε).

For a clamp r ≥ 1 and 0 ≤ j ≤ r, the "singular shell"
   Shell_j = { W : min(weakEigCount(ε, W), r) = j }.
These shells partition W-space (over j = 0..r).

There is a MEASURE-PRESERVING bijection Φ (a row split + reassociation) taking the box
parameter A' (which determines A and hence W) to a pair (z, A_cor), such that the matrix
   Q(z, A_cor)  :=  fromRows( [pivot rows of A]⋅Z ; A_cor⋅Z )
equals W up to a fixed permutation of its M1 rows. In particular Q and W have the SAME
singular values (row permutation is orthogonal). Here A_cor are the "corank" rows.

Define the "pivot shell" (a DOMAIN restriction on (z, A_cor)):
   PivotShell = { (z, A_cor) : Q Qᵀ ⪰ ε²·I }  =  { (z,A_cor) : σ_min(Q) ≥ ε }
             =  { (z,A_cor) : weakEigCount(ε, Q) = 0 }.

There is a positive integrand of the shape
   F(W) = ∫_{T in a fixed box} frobSq(T ⋅ W)^(−c')  d(front block T)   (an M0×M1 block T),
   c' > 0,  frobSq(X) = Σ_{ij} X_ij²,   (·)^(−c') with the convention 0^(−c') = +∞.
Under Φ, F(W) equals the same-shape integrand G(z,A_cor) = ∫_T frobSq(T·Q)^(−c') dT
(because W and Q differ by a row permutation, which leaves frobSq(T··) invariant after
relabeling T's columns).

THE INEQUALITY IN QUESTION (for a FIXED j with 1 ≤ j ≤ r−1, i.e. j ≥ 1):

   ∫_{ A' : W(A') ∈ Shell_j }  F(W(A'))  dA'
        ≤   ∫_{ (z,A_cor) ∈ Box ∩ PivotShell }  G(z, A_cor)  d(z,A_cor).

The claim in the source is that this inequality holds "by pure measure reorganization":
apply the measure-preserving Φ, drop the shell indicator using nonnegativity, apply Tonelli,
and a row split. No analytic content is claimed.

FACTS I have established (verify or refute each):
- F1. Φ is measure-preserving and maps { W ∈ Shell_j } bijectively onto
      { (z,A_cor) : weakEigCount(ε, Q) = j }.
- F2. PivotShell = { weakEigCount(ε, Q) = 0 } = Shell_0 (in (z,A_cor) coordinates).
- F3. Hence for j ≥ 1 the LHS integration region (image under Φ) and the RHS region
      Box ∩ PivotShell are DISJOINT ({wec = j} vs {wec = 0}).

QUESTIONS (answer each explicitly and independently):
Q1. Can the stated inequality be established for j ≥ 1 by "pure measure reorganization"
    (measure-preserving CoV + dropping a nonneg indicator + Tonelli + row split)? If not,
    identify precisely which step fails and why.
Q2. Is the inequality even TRUE for j ≥ 1 (as a statement about real numbers in [0,+∞])?
    Consider the behaviour of G(z, A_cor) as σ_min(Q) → 0 (near-singular Q) versus on
    PivotShell (σ_min(Q) ≥ ε), and whether there is a regime of c' for which the LHS is
    +∞ while the RHS is finite (or otherwise LHS > RHS).
Q3. For the pure-front integral G(Q) = ∫_{T ∈ [−1,1]^{M0×M1}} frobSq(T·Q)^(−c') dT with Q
    of size M1×n: for which c' is G(Q) finite when σ_min(Q) ≥ ε (well-conditioned)? For
    which c' does G(Q) → +∞ as Q approaches a rank-(M1−k) matrix (k singular values → 0)?
    Give the exact thresholds in terms of M0, M1, k.
Q4. If the inequality is NOT a measure-reorganization fact, what is the correct way to
    dominate ∫_{Shell_j} F for j ≥ 1? In particular, is a floor on the DEEP factor Z of
    the form Z Zᵀ ⪰ ε'²·(U_s U_sᵀ) for an M2×m orthonormal frame U_s (m = min(M1,n) − j)
    — i.e. Z retains m singular values ≥ ε' even though W = A⋅Z has j small ones — the
    natural quantity to use, rather than a floor on the whole product W/Q?
</task>

<output_contract>
Five short sections: Q1, Q2, Q3, Q4, and a one-line VERDICT ("inequality sound for j≥1 via
measure reorganization" / "not sound; correct route is …"). For Q3 give exact numeric
thresholds. Keep total under ~600 words. Mark anything you are inferring vs. proving.
</output_contract>

<grounding_rules>
- Treat this as real analysis. Do not assume the inequality is true because it is "in a
  paper"; check it.
- If you need an ensemble/measure for the near-singular region, state your assumption and
  give the answer conditionally.
- Exact thresholds only (rationals in M0, M1, k); no floating-point.
</grounding_rules>
