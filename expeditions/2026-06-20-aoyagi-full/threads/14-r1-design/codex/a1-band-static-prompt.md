<task>
A finite combinatorial-optimization lemma. I need either (i) a clean structural proof, or (ii) a
counterexample, for the BAND inequality below. I am formalizing this in Lean; I want the proof to
reduce to band-FREE static facts (head counts / pointwise dominations), not a circular re-statement.

SETUP (all integers, exact arithmetic):
- M = (M[0], M[1], ..., M[L]) a tuple of L+1 nonnegative integers (L >= 1). NOT sorted.
- a = sort(M) ascending. Sprefix(n) = a[0]+...+a[n-1].
- c = the largest c in [0,L] such that for all i in [1,c]: i*a[i] <= Sprefix(i+1) + i - 1.
- P = Sprefix(c+1). b = P div c, r = P mod c (when c>=1).
- Y is a length-L integer list (the "pool"):
    for j in [0,c): Y[j] = b if j < c-r else b+1   (a "balanced split" of P into c parts)
    for j in [c,L): Y[j] = a[j+1]                   (the largest L-c widths, sorted)
  (Y is monotone nondecreasing.)
- Widths W = (M[1], M[2], ..., M[L])  -- the POSITIONAL tail of M, length L, NOT sorted.
- It is GIVEN (proven) that Dom(W, Y) holds: |Y|=|W|=L and for every threshold t,
    #{y in Y : y < t}  <=  #{w in W : w < t}.   (head-count domination)
- backwardGreedy(W, Y): process positions L-1 down to 0; at position j pick the SMALLEST
  remaining pool value >= W[j]; remove it; place it at position j. Output q = (q[0],...,q[L-1]).
  Under Dom this never stalls and q is a permutation of Y with q[j] >= W[j] for all j.
- admBound[j] = min(M[0], M[1]) if j==0, else M[j+1].
- S(n) = M[0]+...+M[n-1].

THE BAND (to prove for all j in [0,L-1]):
    prefix_{j+1}(q) := q[0]+...+q[j]  >=  S(j+2) - admBound[j].

EQUIVALENT FORMS I have verified numerically (0 failures over ~3200 cases, L<=5):
- u_{j+1} <= admBound[j], where u_{j+1} := S(j+2) - prefix_{j+1}(q)  (a "level" telescoping).
- SUFFIX LOCALITY (band-free, abstract): q[j+1:] = backwardGreedy(W[j+1:], Y) exactly
  (right-to-left greedy fills suffix positions first from the full pool).
- EXCESS BOUND: sum(q[j+1:]) <= sum(W[j+1:]) + admBound[j]   (algebraically identical to the band).

KNOWN GREEN TOOL (already proven, reusable):
- backwardGreedy_suffix_le: for ANY list p that is a permutation of Y with p[i] >= W[i] for all i,
  and any k: sum(backwardGreedy(W,Y)[k:]) <= sum(p[k:]).  (greedy minimizes every suffix sum.)

WHAT FAILED (refuted numerically, do NOT propose these):
- "min-suffix = sum of the k smallest Y values" is FALSE (feasibility forces larger elements in;
  CX M=(0,0,1), j=0: q=[0,1], suffix=[1], but smallest Y is [0]).
- Using the monotone arrangement Y itself as a fixed witness p FAILS: it is often infeasible for the
  POSITIONAL widths W (Y sorted ascending need not dominate the unsorted W), and even when feasible
  its prefix undershoots the bound (CX M=(1,0,0), j=0).
- Per-position "q[k] >= u_{k+1}" is NOT abstractly true under Dom alone (fails for non-greedy
  feasible arrangements, ~20% of cases) — it holds for the GREEDY q but the proof would be circular
  with the band.
</task>

<output_contract>
1. State whether the BAND is TRUE as stated, or give an exact counterexample (M, j).
2. If true, give the cleanest proof you can find that bounds sum(q[j+1:]) WITHOUT assuming the band.
   Specifically: either
   (a) exhibit a CONCRETE feasible witness arrangement p (a permutation of Y, p[i]>=W[i] for all i)
       whose suffix sum sum(p[j+1:]) <= sum(W[j+1:]) + admBound[j], constructed explicitly from
       (M, a, c, b, r, j) — so backwardGreedy_suffix_le finishes it; OR
   (b) a head-count / pointwise-domination argument (in the spirit of Dom) that bounds the greedy
       suffix sum directly, naming exactly which inequality on (Y, W, admBound) does the work and
       why it is band-free; OR
   (c) an induction on the suffix length that closes WITHOUT the per-position circular step.
3. Identify the single load-bearing inequality and whether the achiever conditions on c
   (the "goodAch" / good_i facts: i*a[i] <= Sprefix(i+1)+i-1) are NEEDED, and where.
4. Flag explicitly any step where you suspect hidden circularity with the band.
</output_contract>

<grounding_rules>
- This is exact integer arithmetic; no floats, no asymptotics.
- Distinguish what you PROVE from what you CONJECTURE. Mark conjectures.
- If you propose a witness or inequality, it must hold for ALL the data, not one example.
- Do not assume W is sorted. Do not assume Y dominates W positionally.
- The achiever c and goodAch conditions are the ONLY structural constraints linking Y to M beyond
  Dom; if your proof does not use them, say so (and then it should also work for any Dom pool, which
  I can test).
</grounding_rules>
