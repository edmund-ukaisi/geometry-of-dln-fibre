<task>
A pole-multiplicity counting question from a normal-crossing resolution of singularities (Aoyagi 2023,
deep linear networks). Derive the answer; do not assume mine.

SETUP. A sum-of-squares loss F is resolved by an ATLAS of coordinate charts (leaves of a recursion tree).
In each chart the pulled-back loss is a monomial ∏_j u_j^{2k_j} and the Jacobian is ∏_j u_j^{h_j}; each
exceptional divisor {u_j = 0} carries a ratio (h_j+1)/(2k_j). The real log-canonical threshold is
λ = min over ALL divisors in ALL charts of (h_j+1)/(2k_j). The POLE MULTIPLICITY (order of the largest
pole of the zeta function ∫|F|^{-z}) is, by the standard monomial formula,
   ρ = max over points u of the resolved space of  #{ j : (h_j+1)/(2k_j) = λ  and  u ∈ {u_j=0} }.
So ρ counts BINDING divisors (ratio = λ) that pass through a common point.

STRUCTURE of this atlas. Each chart's divisors are a subset of its coordinate hyperplanes {u_j=0}. A
"binding profile" is a combinatorial label t (a lattice point) with an associated value Mval(t); a divisor
is binding iff Mval(t) = minAdm := min_t Mval(t). The SAME binding profile-value minAdm can be realised by
SEVERAL distinct profiles t, and different charts (leaves) realise different SUBSETS of these minimising
profiles as actual divisors. Let:
  - naive := the total number of DISTINCT minimising profiles t (Mval(t)=minAdm), across the whole lattice;
  - the per-chart binding count := #{binding divisors present in that one chart}.

CALIBRATION DATA (widths → known ρ). (2,2,2)→ρ=1; (3,3,4)→ρ=1; (2,2,3,2)→ρ=1; (2,2,2,2)→ρ=3; (2,1,2)→ρ=2.
A closed form is conjectured: ρ = a(ℓ−a)+1, where (a,ℓ) are integers from the width data (ℓ+1 smallest
reduced widths participate; a = the "surplus" of a balanced ℓ-part split). KNOWN ANOMALY: for widths
[3,3,1,1] there are TWO distinct minimising profiles (naive = 2) but ρ = 1.
</task>

<output_contract>
≤ 300 words, committing:
1. WHICH count is ρ: the naive total number of minimising profiles, OR the max over charts of the
   per-chart binding count, OR something else? Derive it from the max-over-points definition and the fact
   that within one coordinate chart any set of distinct coordinate-hyperplane divisors shares the origin.
2. WHY the naive total is the WRONG object (use [3,3,1,1]: two minimisers, ρ=1).
3. Does ρ = a(ℓ−a)+1 hold EXACTLY for the object you identified? Argue BOTH directions: (upper) no chart
   can carry more than a(ℓ−a)+1 binding divisors; (attainment) some chart carries exactly a(ℓ−a)+1. If you
   suspect the printed a(ℓ−a)+1 could be wrong for the true object, say so and name where.
</output_contract>

<grounding_rules>
- Reason from the max-over-points pole formula + the chart/divisor structure. Distinguish "how many
  minimising divisors exist in total" from "how many meet at one point of one chart."
- Commit to one identification of ρ. Do not restate my setup; give the derivation and verdict.
</grounding_rules>
