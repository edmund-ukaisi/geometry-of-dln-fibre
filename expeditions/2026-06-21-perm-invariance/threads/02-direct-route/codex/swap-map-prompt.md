<task>
Combinatorics. I want an ELEMENTARY (no cohomology / no generating functions) proof that the
MINIMUM of a quadratic form over Kostant partitions, and the NUMBER of minimisers, are unchanged by
a single adjacent transposition of the dimension vector. Work it from scratch — I want your
independent construction of the map, not a confirmation.

SETUP. Fix N. A dimension vector is d = (d_0,...,d_N) of nonneg integers. An "interval" (or "lace")
is [a,b] with 0 <= a <= b <= N. A Kostant partition of d is a multiset of intervals such that
exactly d_k of them cover vertex k (cover = a <= k <= b), equivalently nonneg integer multiplicities
m([a,b]) with, for all k: sum_{a<=k<=b} m([a,b]) = d_k. Restrict to m([0,N]) = 0 (the r=0 case).

THE FORM (non-symmetric, bilinear).
   F(m) = sum over ORDERED pairs of intervals (A=[a,b], B=[c,e]) with
          ( a < c <= b+1 ) AND ( b < e )    of    m(A)*m(B).
Call such an ordered pair (A,B) a "pairing" / "A pairs B". Define C(d) = min_m F(m),
theta(d) = #{minimisers}.

ESTABLISHED FACTS (exact integer computation, exhaustive; you may USE these, do not re-derive):
 - C and theta are invariant under any permutation of the entries of d (the surprise).
 - CORNER-PAIR RIGIDITY: in ANY minimiser m of any d, every pairing (A,B) has A=[0,b] (left end 0)
   and B=[c,N] (right end N). I.e. all the F-value comes from "corner pairs" ([0,b],[c,N]) with
   b<N (since m([0,N])=0) and 0<=b, c<=N, and the pairing condition a=0<c<=b+1, b<e=N becomes
   c <= b+1 (and c>=1). So a corner pair ([0,b],[c,N]) pairs iff 1 <= c <= b+1.
 - Minimisers may ALSO contain non-pairing intervals (including interior [a,b], 0<a, b<N) that
   contribute 0 to F.
 - The Kostant-partition SETS for d and for swap_i(d) generally have DIFFERENT cardinalities, and the
   multiset of F-values is NOT preserved; only min and #minimisers are preserved. So NO
   value-preserving bijection on the full partition sets exists. A min-LEVEL map is needed.

TARGET. Let swap_i(d) exchange d_i and d_{i+1}. Construct, concretely on the laces:
 (1) a map Phi from {Kostant partitions m of d} to {Kostant partitions of swap_i(d)} such that
     F(Phi(m)) <= F(m), AT LEAST on minimisers (giving C(swap_i d) <= C(d); run both directions for
     equality). Describe EXACTLY which laces crossing columns i, i+1 you modify and how F changes.
 (2) For theta: refine Phi (or restrict to minimisers) to a BIJECTION between the minimiser sets,
     so #minimisers is preserved.

OUTPUT CONTRACT. In this order, briefly + concretely:
 1. THE MAP. Define Phi by what it does to the multiplicities m([a,b]) near columns i,i+1. Be fully
    explicit (a finite list of lace re-routings). What is the inverse?
 2. F-CHANGE. Compute F(Phi(m)) - F(m) and argue it is <= 0 on minimisers (or = 0). Where does
    corner-pair rigidity enter? Give the inequality concretely enough to check on an example.
 3. THETA. Does Phi restrict to a bijection of minimisers? If not, what extra map fixes the count?
 4. HONEST DIFFICULTY. The single hardest sub-lemma, and whether you believe the map exists at all
    or whether you suspect an obstruction (some d where no local lace-reroute can be value-non-
    increasing). Flag conjecture vs argued.

GROUNDING. Distinguish argued from guessed. If you assert the map works, give the lace manipulation
concretely enough to check on, e.g., d=(1,2,3) -> swap_1 -> (1,3,2), whose minimisers are
{(0,0):1,(1,2):2,(2,2):1} and {(0,1):1,(1,2):2} respectively (both C=2, theta=1). Do not restate the
setup.
</task>
