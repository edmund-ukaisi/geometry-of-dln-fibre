<task>
Independently work out an algebraic-geometry correspondence; do NOT rubber-stamp — derive it yourself.

SETTING. A deep linear network has widths M = (M_0,...,M_L). The Aoyagi "codim" of a descent path is
defined as follows. An exponent vector T = (t^1, ..., t^L) (nonneg integers) is "admissible" iff it is
weakly decreasing (t^1 >= t^2 >= ... >= t^L), t^L = 0, and t^j <= admBound_j where admBound_1 = min(M_0,M_1)
and admBound_j = M_{j+1} for j>=2. Its value is
   Mval(M,T) = sum_{j=1}^{L} (t^{j-1} - t^j) * (M_{j+1} - t^j),    with the convention t^0 := M_0
   [indices: M_{j+1} means the width after the j-th matrix; for j=1 the term is (M_0 - t^1)(M_2 - t^1)... 
    wait, careful: M_{j.succ} in 0-indexed is M_{j} for the j-th exponent. Use: term_j = (t^{j-1}-t^j)(M_j - t^j)
    where M_j is the (j)-th width counting M_0 as the 0th -- I will give concrete examples to disambiguate.]
The "minimal admissible codim" is minAdm(M) = min over admissible T of Mval(M,T).

CONCRETE (these are FACTS, computed):
- M=(4,4,2,2): minAdm=4, unique minimizer T=(4,2,0), per-layer terms [0,0,4].
- M=(3,3,4):   minAdm=8, unique minimizer T=(1,0),   per-layer terms [4,4].
- M=(2,2,1):   minAdm=2, two minimizers T=(1,0) terms [1,1] and T=(2,0) terms [0,2].
- M=(2,2,2):   minAdm=3, unique minimizer T=(1,0),   per-layer terms [1,2].

THE CHART. For an "achiever" resolution chart phi : R^N -> R^N (N = sum_k M_k M_{k+1}) resolving the codim-m
achiever center (m = minAdm), the radial blow-up factor is `pivotBlowupOn(active, p)`: pivot p maps to itself
(identity), each active coord j != p maps x_j -> x_p * x_j, spectators unchanged. Its Jacobian determinant is
x_p^{|active| - 1}. The chart needs |det Dphi| = |x_p|^{m-1} * (spectator monomials), so the RADIAL factor's
active set must have |active| = m = minAdm (giving x_p^{minAdm - 1}).

BANKED CHART FACTS (validated, sorry-free):
- (4,4,2,2): radial = pivotBlowupOn({0,1,2,3}, 0), |active|=4=minAdm. (All codim in the deepest layer: [0,0,4].)
- (3,3,4):   radial = pivotBlowupOn({0,6,7,8,9,10,11,12}, 0), |active|=8=minAdm. PLUS a separate
             pivotBlowupOn({1,2,3}, 1) (a "b=a*beta" Schur substitution, det |u_1|^2, a spectator monomial).

QUESTIONS (derive, show work):
1. Is it ALWAYS true that |active| = minAdm M for the radial factor of the achiever chart? Argue from the
   geometry: the achiever center is the locus where the product attains the rank pattern of the descent path
   T*; its codimension in parameter space is exactly Mval(M,T*) = minAdm. The radial blow-up resolves this
   center, so it blows up exactly minAdm "normal" directions at one pivot. Confirm or refute: |active| = minAdm
   is the correct UNIFORM rule (not per-case).
2. What ARE the minAdm normal coordinates concretely, per layer? The per-layer term (t^{j-1}-t^j)(M_j - t^j)
   is the codim contributed at boundary j. Are these the entries of an (r_j x c_j) residual block where
   r_j = t^{j-1} - t^j (rows dropped) and c_j = M_j - t^j (residual columns)? Verify r_j * c_j matches the
   per-layer terms above for all 4 examples. Is the radial active set the disjoint union over j of these
   r_j * c_j residual-block coordinates (total = sum_j r_j c_j = minAdm)?
3. The pivot scales a FIXED 1-entry. In a per-layer residual block of size r_j x c_j, which single entry is the
   "fixed 1" (the pivot's target) and which are the m-1 free actives? Is there ONE global pivot across all
   layers, or one pivot per layer? (The banked (3,3,4) uses ONE pivot 0 for all 8 radial actives.) Reason about
   whether a single global pivot scaling one fixed-1 entry, with the other minAdm-1 normals as free actives, is
   consistent with the rate F = (x_p)^2 * U (the loss vanishing to order 2 along the radial ray).
4. KILL-CHECK: is there any M where NO single uniform rule "active = the minAdm residual-block normals, one
   global pivot" works -- e.g. multiple minimizers (like (2,2,1) with two T*) forcing a choice, or a layer
   structure where the per-layer blocks cannot be simultaneously blown up at one pivot? If the rule is only
   per-case (no uniform formula), say so sharply.
</task>

<output_contract>
- Q1: confirm/refute |active|=minAdm as the uniform rule, with the geometric argument. FACT vs INFERENCE.
- Q2: the per-layer block sizes r_j x c_j; verify r_j*c_j = per-layer term for all 4 examples (show arithmetic).
- Q3: the fixed-1 entry + the global-vs-per-layer pivot question, reasoned against the rate.
- Q4: a sharp yes/no on whether a uniform rule exists ∀M, with any obstruction named.
</output_contract>

<grounding_rules>
- The 4 minAdm/minimizer facts and the banked chart facts are FACTS. Derive the general rule from them.
- Do not assume a uniform rule exists; if multiple minimizers or layer obstructions break it, surface that.
- Work the r_j*c_j arithmetic concretely for all 4 examples.
</grounding_rules>
