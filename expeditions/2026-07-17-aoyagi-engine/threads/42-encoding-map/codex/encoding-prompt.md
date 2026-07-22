<task>
A finite-poset order-isomorphism question. Derive; do not assume my answer.

SETUP. Fix integers ℓ ≥ a ≥ 1. Two posets:
- P = binding minimisers: profiles T = (t¹,…,t^L) (weakly-decreasing, t^L=0, each tʲ ≤ running-min of the
  first widths) with a codimension value Mval(T) equal to its minimum minAdm; ordered COMPONENTWISE (≤).
- BoxPart(ℓ,a) = antitone f : {1..a} → ℕ with f(i) ≤ ℓ−a (Young diagrams in the a×(ℓ−a) box), ordered
  pointwise. Its longest chain has a(ℓ−a)+1 elements; |BoxPart| = C(ℓ,a).

EMPIRICALLY P is a graded distributive lattice with C(ℓ,a) elements, unique min/max, longest chain
a(ℓ−a)+1 — matching BoxPart. We want an explicit encoding enc : P → BoxPart and to know it is an ORDER
ISOMORPHISM. A candidate "encoding" that ranks elements only by coordinate-SUM (∑ tʲ) is tempting.

KNOWN HAZARD: the profile coordinate-sum is NOT a valid graded rank of P — a covering step in P can jump
∑tʲ by several units (e.g. min=(0,0,0), max=(1,1,0) is a single cover but ∑ jumps by 2). So a sum-based
encoding can map INCOMPARABLE profiles to COMPARABLE boxes.

<output_contract>
≤220 words. Commit:
1. To certify enc : P → BoxPart as an ORDER ISO, which conditions must be checked, and specifically why is
   the REVERSE implication (enc T ≤ enc T' ⟹ T ≤ T') the load-bearing one — what failure does a merely
   forward-monotone (e.g. coord-sum-based) enc exhibit? Give the failure in terms of incomparable elements.
2. If P is verified to be a graded distributive lattice isomorphic to BoxPart(ℓ,a) (same size, rank
   function, cover structure), does a canonical order-iso exist and is it unique? Name the canonical
   construction (Birkhoff / join-irreducibles).
3. If the admissibility bound is LOOSENED (allow tʲ up to a larger cap than the running-min), what breaks
   first — the min value minAdm, the element count C(ℓ,a), or the order-embedding — and why does that make
   the tight (running-min) domain load-bearing?
</output_contract>

<grounding_rules>
- Reason from order theory (order-embedding = mono both ways; distributive lattice ≅ down-sets of its
  join-irreducibles). Commit; don't hedge.
</grounding_rules>
