<task>
A poset question about a resolution's pole multiplicity ρ. Derive; do not assume my answer.

SETUP. On a normal-crossing resolution ATLAS (leaves of a recursion tree), the pole multiplicity is
ρ = max over charts of #{binding divisors present in that chart} (binding = the exceptional divisors whose
ratio equals the RLCT). Each binding divisor carries a combinatorial "profile" — a vector t (a lattice
point). Empirically: (i) within ANY single chart, the binding profiles present are pairwise
componentwise-comparable (they form a CHAIN under ≤); (ii) the recursion accumulates exponents so a
later-born binding divisor's profile dominates or is dominated by earlier ones. The set of ALL binding
profiles forms a poset P under componentwise ≤; it has a unique minimum T̃ and unique maximum T̃'.

DATA: a closed form ρ = a(ℓ−a)+1 is conjectured (1 ≤ a ≤ ℓ). Example: widths [2,2,2,2,2] give a=2, ℓ=4;
the binding poset is {(1,0,0,0),(1,1,0,0),(1,1,1,0),(2,1,0,0),(2,1,1,0),(2,2,1,0)}; the longest chain has
5 elements (=a(ℓ−a)+1); (1,1,1,0) and (2,1,0,0) are incomparable.
</task>

<output_contract>
≤200 words. Commit:
1. Is ρ the max CHAIN length or the max ANTICHAIN length of the binding poset P? Derive it from "within
   one chart the binding profiles form a chain" + "ρ = max over charts". State which, and why the OTHER
   (Dilworth-dual) is wrong.
2. Given unique min T̃, max T̃', is the poset GRADED (all maximal T̃→T̃' chains equal length)? If so the
   height = ρ = a(ℓ−a)+1. Say whether the natural grading is by coordinate-sum of the profile, or by some
   other rank (and if coord-sum can fail).
</output_contract>

<grounding_rules>
- Reason from: within-a-chart chains + ρ=max-over-charts + the poset having unique bounds. Distinguish
  "longest chain" from "largest antichain". Commit; don't hedge.
</grounding_rules>
