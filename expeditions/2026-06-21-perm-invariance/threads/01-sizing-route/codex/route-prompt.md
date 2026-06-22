<task>
Combinatorics question about a quadratic minimisation over Kostant partitions of a vector, and
whether permutation-invariance of the minimum has an elementary proof. Work it from scratch; I want
your independent read of the proof routes, not a confirmation.

SETUP. Fix N and an integer vector d = (d_0,...,d_N) of nonneg integers. An "interval" is a pair
[a,b] with 0 <= a <= b <= N. A "Kostant partition of d" is an assignment m([a,b]) of a nonneg
integer to each interval such that for every vertex k in 0..N:
        sum over intervals [a,b] with a <= k <= b of m([a,b])  =  d_k.
(Equivalently: a multiset of intervals ("laces") such that exactly d_k of them cover vertex k.)
Restrict to partitions with corner multiplicity m([0,N]) = 0 (the r=0 case).

THE FORM. For a partition m define the (non-symmetric, bilinear) quadratic form
        F(m) = sum over ordered pairs of intervals (A=[a,b], B=[c,e]) with
               ( a < c <= b+1 )  AND  ( b < e )   of   m(A) * m(B).
Define C(d) = min over Kostant partitions m of d (corner 0) of F(m), and
       theta(d) = number of minimisers.

OBSERVED (exact integer computation, exhaustive over small d):
 - C(d) and theta(d) are invariant under ANY permutation of the entries of d. (This is the surprise.)
 - In particular invariant under a single adjacent transposition d_i <-> d_{i+1}.
 - Under a single adjacent transposition, the MULTISET of F-values over all Kostant partitions is
   generally NOT preserved (the partition sets even have different CARDINALITIES). Only the minimum
   and the count of minimisers are preserved.
 - So there is provably no value-preserving bijection on the full Kostant-partition sets.

CONTEXT (do not need to verify): this F is the "Ext^1(M,M)" / orbit-codimension form for equioriented
type-A quiver representations; the published proof of the permutation invariance of (C,theta) goes
through a Poincare series in equivariant cohomology (an inverse-q-Pochhammer product that is
manifestly symmetric in the multiset of d), and the authors explicitly write that they do NOT know a
proof using only the form F and the combinatorics of Kostant partitions. A separate explicit closed
form for C(d) and theta(d) is known but only for WEAKLY INCREASING d (it is built from prefix sums of
the sorted vector).
</task>

<output_contract>
Answer these, briefly and concretely, in this order:

1. ADJACENT SWAP. Is there a plausible ELEMENTARY (no topology/cohomology) proof that
   C(d) = C(swap_i d) and theta(d) = theta(swap_i d) for a single adjacent transposition? Sketch the
   most promising mechanism. Given the value-multiset is NOT preserved, what kind of map would carry
   it (e.g. a value-non-increasing injection from minimisers of d into partitions of swap_i d, run
   both directions; or a direct manipulation of the laces crossing the swapped columns)? Be concrete
   about what crosses columns i, i+1 and how F changes.

2. REDUCE-TO-SORTED. Alternatively: the closed form for C is known for weakly increasing d. Could one
   prove C(d) = C(sorted d) directly (general d -> its sorted rearrangement) by a single argument,
   rather than swap-by-swap? What would that argument need?

3. theta. For the MINIMISER COUNT specifically, what is the extra difficulty beyond C, and is it
   harder or easier than C under the adjacent swap?

4. VERDICT. Rank the routes by tractability for a from-scratch elementary proof: (a) adjacent
   transposition, (b) reduce-to-sorted, (c) a full Kostant bijection, (d) "you genuinely need the
   cohomology / generating-function argument." Say which one you would attempt and the single hardest
   sub-lemma you foresee.
</output_contract>

<grounding_rules>
Distinguish what you can argue from what is a guess. If you assert a mechanism works, give the lace
manipulation or the inequality concretely enough that it could be checked on an example; flag
anything you are only conjecturing. Do not just restate the setup.
