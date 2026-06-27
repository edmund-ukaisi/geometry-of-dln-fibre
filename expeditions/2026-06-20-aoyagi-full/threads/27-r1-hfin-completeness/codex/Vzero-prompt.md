<task>
Red-team a feasibility verdict. I claim a determinantal singularity's RLCT upper bound is provable
"from scratch" using ONLY a normal-crossing→RLCT axiom (S2) + standard Euclidean radial integration,
with NO appeal to the general Aoyagi/Watanabe bound rlct ≥ codim/2. Find the hole if there is one.

SETUP. Loss F = ||A^(0)...A^(L-1)||_F^2 (deep linear net), near 0. After peeling clean rank-1 pivots,
the binding singular CORE of a corank-r cell is G = ||Δ·S||^2 with Δ an r×r residual matrix and S an
r×p free block (a matrix-multiplication / determinantal singularity). I want, for c' < rlct(G),
INT_{box} G^{-c'} < ∞, proven by an explicit resolution whose leaves are only:
  (S2)      product monomials prod x_i^{2k_i} (the cited normal-crossing→threshold axiom), OR
  (S2-FREE) Euclidean sum-of-squares ||y||^2 (Mathlib radial_ball_iff: INT_{ball} ||y||^{-2c'} < ∞
            iff c' < dim/2 -- standard, no citation).

MY CLAIMED RESOLUTION (verified by exact sympy for r=2, p=4; structure checked for r=3):
  radial Δ = a·R, R the r×r affine-chart matrix (one entry pivoted to 1, rest free), a the scale.
  Jacobian det D(Δ)/D(a, R-free) = a^{r^2-1} (≠0 off {a=0}). Then G = a^2 ||R·S||^2.
  The inner ||R·S||^2: on {R full rank} it is a nondegenerate quadratic (Morse) form in S
  (S2-free Euclidean); the singular sublocus is {rank R < r}, a corank-<r determinantal core -> RECURSE.
  Corank strictly drops each recursion -> depth ≤ r (bounded). For r=2, p=4 the exact resolved form is
  G∘π = a^2·[(1+v^2)||P'||^2 + (e^2/(1+v^2))||Q||^2], leaves {a^2,e^2}(monomial) × {||P'||^2,||Q||^2}(Morse),
  threshold 2 = rlct(||Δ S||^2). The cell F = ||T||^2 ⊕ ||ΔS||^2 (disjoint vars) -> rlct = 2+2 = 4 =
  minAdm/2 by Watanabe disjoint-sum additivity (Tonelli, S2-free).

MY VERDICT: the recursion terminates S2-only (mostly S2-free at the leaves; S2 only at the monomial
divisor axes), depth ≤ corank, giving the per-cell upper bound at threshold minAdm/2. So the RLCT
upper bound is provable from scratch — the Aoyagi/Watanabe cite is NOT needed.

QUESTIONS (find the hole):
  (1) Is the radial-blow-up-of-Δ + recurse-on-rank-drop a COMPLETE resolution? Specifically: does
      blowing up {Δ=0} (a point in Δ-space, the full r×r) and recursing on the rank-drop locus
      actually reach normal-crossing/Morse leaves, or is there a stratum (e.g. the intermediate-rank
      determinantal locus {rank Δ = j}, 0<j<r) that is NEITHER full-rank-Morse NOR a lower point-blow-up
      -- i.e. a determinantal singularity that the point-blow-up + rank-drop recursion does NOT resolve?
  (2) The inner ||R·S||^2 on {R full rank}: is it REALLY a clean Euclidean Morse form in S (so S2-free
      radial integration applies), or does the dependence on the R-chart-coordinates (u,v,w,...) make
      it a non-Morse / non-radially-integrable form (e.g. the coefficient matrix degenerating on a
      positive-measure set, breaking the ball domination)?
  (3) The UPPER bound (finiteness), not just the rlct VALUE: does INT |a|^{r^2-1} (a^2 I)^{-c'} d(...)
      genuinely converge for c' < minAdm/2 via the resolved leaves, or is there a cross-term / a
      non-disjoint coupling that makes the joint integral diverge earlier than the per-leaf thresholds
      suggest (the classic "Fubini/Tonelli only works for disjoint or dominated" trap)?
  (4) Net: is my "S2-only feasible" verdict SOUND, or is there a determinantal stratum / a coupling
      that forces a genuine non-S2 RLCT computation (where you'd have to cite rlct ≥ codim/2)?
</task>

<output_contract>
1. Answer (1)-(3): is the resolution complete + the leaves genuinely S2/S2-free + the upper bound
   joint-convergent? Point to any specific hole (a stratum, a coupling, a non-Morse leaf).
2. Answer (4): is "S2-only feasible" SOUND, or is there a forced non-S2 cite? If sound, confirm the
   mechanism; if not, the precise obstruction.
3. Distinguish derived vs conjectured. Be adversarial — I want the hole found if it exists.
</output_contract>

<grounding_rules>
- rlct(||Δ S||^2) for Δ r×r, S r×p (matrix-product, true rank 0) is known rational (e.g. (2,2,4): 2).
- A point-blow-up of {Δ=0} in r×r-space has exceptional divisor mult r^2-1.
- S2 = normal-crossing→RLCT (threshold min_j (h_j+1)/2k_j for a product monomial). Euclidean Morse
  ||y||^2 in dim n: INT_{ball}||y||^{-2c'} < ∞ iff c' < n/2 (Mathlib, S2-free).
- Watanabe disjoint-sum: rlct(f(x)+g(y)) = rlct(f)+rlct(g) for disjoint x,y (Tonelli, S2-free).
- I withhold nothing material; reason adversarially from the setup.
</grounding_rules>
