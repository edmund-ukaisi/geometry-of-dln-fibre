# Contract: verify (or refute) a combinatorial "shortest-covering" claim, give the cleanest proof skeleton

## Setup (type-A interval combinatorics; all integers; N a fixed natural)
Intervals are pairs [a,b] of integers with 0<=a<=b<=N. A multiset of intervals is given by
multiplicities m([a,b]) >= 0. "Active" = m>=1. Define the (ordered) PAIRING predicate:
  pair(A=[a,b], B=[c,d])  :⟺  (0<=a) ∧ (d<=N) ∧ (a<c) ∧ (c<=b+1) ∧ (b<d).
(This is the type-A Ext-pairing: A is the "left" member, B the "right" member.)
Length ℓ([x,y]) := y - x (>=0). "Y covers vertex k" :⟺ Y.1 <= k <= Y.2.

## The selection
Assume at least one active pair exists. Among ALL ordered active pairs (A,B) with pair(A,B), pick one
(A*,B*) MINIMIZING min(ℓ(A), ℓ(B)) (the length of the shorter member). Let I be the shorter member:
- if ℓ(A*) <= ℓ(B*): I := A* (the LEFT member), and set k := c* - 1  where B*=[c*,d*];
- else: I := B* (the RIGHT member), and set k := b* + 1 where A*=[a*,b*].

## CLAIM A (to verify and give a clean proof of)
With I=[a,d'] and k as above:
(1) a <= k <= d'  (I covers k);
(2) I is a SHORTEST active covering interval of k: for every active Y covering k, ℓ(I) <= ℓ(Y).

I have numerically verified (1) and (2) for N<=2 over all full-coverage configs (0 failures), and the
"partner coeff = -1" companion fact (the split of I at k assigns the partner exactly -1) for N<=4.

## What I need from you
(a) Confirm CLAIM A is TRUE, or give a concrete counterexample (m, the pair, I, k, and a shorter
    active Y covering k).
(b) If true, give the CLEANEST proof of (2), structured as an interval-arithmetic case split that an
    `omega`-driven Lean proof can follow. In particular: suppose for contradiction some active Y=[x,y]
    covers k with ℓ(Y) < ℓ(I). Show Y forms a pair (as left or right member) with one of A*,B* (or with
    a third interval) whose shorter member has length < min(ℓ(A*),ℓ(B*)), contradicting minimality.
    The certificate I'm following suggests the case split is on "y < d*" vs "y >= d*" (for the I=A* case).
    Pin down EXACTLY which interval Y pairs with, in each case, and the precise inequalities
    (in terms of a*,b*,c*,d*,x,y,k,N) that omega needs. Be concrete and exhaustive about the cases.
(c) Flag any case where Y covering k with ℓ(Y)<ℓ(I) does NOT immediately yield a shorter pair — i.e.
    whether the minimality must be over min(ℓ(A),ℓ(B)) or whether a different extremal choice
    (e.g. lexicographic, or minimize ℓ of a single distinguished member) makes the contradiction cleaner.

Answer concretely with the inequalities; this is going straight into a Lean 4 proof.
