<task>
I am adjudicating a combinatorial-geometry claim about a coordinate chart arising from a "deep linear
network" RLCT (real log canonical threshold) resolution. Pure linear algebra + integer combinatorics;
no Lean. Give an independent analysis at the highest rigor: a proof sketch, OR a counterexample
structure with an explicit small instance.

SETUP. Fix L >= 1 and "ambient widths" M_0, ..., M_L (positive integers). The network's parameter
space has dimension flatDim = sum_{k=0}^{L-1} M_k * M_{k+1} (a tuple of matrices A_k : M_k x M_{k+1};
the "loss" is ||A_0 A_1 ... A_{L-1} - 0||^2 at the deepest singular point, so the target product is 0).

AOYAGI ADMISSIBLE EXPONENTS. Define an exponent vector T = (T_1, ..., T_L) of nonneg integers with the
convention T_0 := M_0, subject to: T weakly decreasing, T_L = 0, and per-layer caps
T_1 <= min(M_0, M_1), T_j <= M_j for j >= 2. The "candidate codimension" of T is
   Mval(T) = sum_{j=1}^{L} (T_{j-1} - T_j) * (M_j - T_j).
Define minAdm(M) = min over admissible T of Mval(T). (This is the codimension of the deepest blow-up
center; the RLCT is minAdm/2.) minAdm satisfies the layer-peeling recursion
   minAdm(M_0,...,M_L) = min_{0<=t<=min(M_0,M_1)} [ (M_0 - t)(M_1 - t) + minAdm(t, M_2, ..., M_L) ].

THE CHART (a "live-leaf" radial blow-up). For an achiever T* (one realizing the min), build a
coordinate chart with ONE shared radial scalar u and `flatDim` total free coordinates, of the form
   Phi(u, z, h) = P(z) + u * (r_0 + sum_a h_a r_a),
where z are "non-radial" coords (entering u-free), h_a are "angular" coords (entering ONLY multiplied
by u), and r_0, r_a are fixed output directions. The construction is a cascade of unipotent
"shear" blocks (determinant-preserving) plus one genuinely radial block. The chart is built so that the
rank drops along the descent T*: at layer j the surviving rank is T_j.

THE TWO CLAIMS TO ADJUDICATE (for the chart to be the correct RLCT-achieving resolution chart):
  (A) #angular = minAdm(M) - 1   (the number of free angular coords h_a equals minAdm - 1).
  (B) the chart is SQUARE and non-degenerate: #free coords = flatDim, and the Jacobian determinant is
      det = u^(minAdm - 1) * (an expression with zero partial derivative in u, generically nonzero).
So det's radial exponent is exactly minAdm - 1.

KEY STRUCTURAL FACTS I have established (exact symbolic Jacobian, sympy):
- For M = (3,3,3,3): T* = (2,1,0) unique, minAdm = 6, det = u^5 * (u-free monomial). #angular = 5. OK.
- For M = (2,2,2): minAdm = 3, det = u^2 * (u-free). #angular = 2. OK.
- For M = (3,3,4): minAdm = 8, det = u^7 * (u-free). #angular = 7. OK.
- For M = (4,4,2,2): minAdm = 4, a DIFFERENT-shaped chart (pure radial blow-up of the single deepest
  2x2 factor A_{L-1} = u * M2bar with M2bar = [[1,h1],[h2,h3]]) gives det = u^3, #angular = 3. OK.

A SUBTLETY I want your independent read on. The achiever T* determines, at the LAST descent layer, a
"surviving leaf rank" rho = T_{L-1} (the rank carried into the final matrix A_{L-1}). When rho >= 1 the
leaf factor is a genuine rho x M_L block that carries free angular coordinates (a "live leaf"). But for
some M, EVERY achiever T* has T_{L-1} = 0 (the rank drops to zero before the last layer) — e.g.
M = (2,2,4): the unique achiever is T* = (0,0) (drop to rank 0 at the first layer). For such M the
"leaf" of the cascade is empty.

<output_contract>
1. Is claim (A) #angular = minAdm - 1 a THEOREM for all M (for a correctly-built chart of the displayed
   affine-in-u form)? Give the clean reason: which set of coordinates is "angular", and why its
   cardinality equals minAdm - 1 (NOT minAdm). I expect the "minus 1" is the single fixed pivot of the
   radial blow-up (one active center coordinate is normalized to 1). Confirm or correct, and identify
   the bijection: {angular coords} <-> {active-center coords} minus {one pivot}, with |active center| =
   minAdm. Is the active center always exactly minAdm-dimensional?
2. Is claim (B) squareness automatic once (A) holds and the cascade blocks are invertible, or is there a
   genuine extra obstruction (a degenerate/rank-deficient diagonal block) for some widths? Pay special
   attention to L >= 4 with TWO OR MORE interior layers that each drop rank by >= 2 (multiple t>=2
   cores), and to MIXED widths (non-constant M_k).
3. THE LEAF SUBTLETY. When every achiever has T_{L-1} = 0 (no live leaf, e.g. (2,2,4) or (2,2,2,4)),
   does the displayed "live-leaf" chart still exist and satisfy (A)+(B)? Or must the chart be re-shaped
   (the angular coords relocating from the empty leaf to an interior block, like the (4,4,2,2) deepest-
   factor blow-up)? Is there a clean dichotomy: "the angular coords live in whichever block carries the
   active center", and the leaf-vs-interior distinction is cosmetic? Or can the no-live-leaf case
   genuinely FAIL squareness / the minAdm-1 count for some widths?
4. If (A) or (B) can FAIL: exhibit the minimal M (L, widths) and the exact mis-counted or degenerate
   block, with the leaking/missing coordinate identified. If they always hold: the invariant that forces
   #angular = minAdm - 1 regardless of where the active center sits.
</output_contract>

<grounding_rules>
- Treat Mval, minAdm, and the layer-peeling recursion as exact (transcribe carefully).
- "Active center" = the deepest blow-up center, of codimension minAdm; the radial blow-up of a
  codim-c center introduces c-1 angular coords + 1 radial pivot (the standard projective-chart count).
- Do not assume the conclusion. If for some M the minimal admissible T forces a chart that is NOT a
  single clean radial blow-up of a codim-minAdm center (e.g. the center splits across layers), say so
  and analyze whether #angular still totals minAdm - 1.
- Give explicit small integer instances. Distinguish "I can prove" from "I expect".
</grounding_rules>
</task>
