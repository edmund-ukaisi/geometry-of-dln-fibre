<task>
Independently determine a combinatorial fact about optimal solutions of an integer program.
I am WITHHOLDING my own answer; derive yours from scratch (exact integer arithmetic / exact DP)
and report it, so I can compare.
</task>

<facts>
Define minAdm on tuples of nonnegative integers by:
  minAdm((a,))  = 0
  minAdm((a,b)) = a*b
  minAdm(M)     = min over t in 0..min(M[0],M[1]) of [ (M[0]-t)*(M[1]-t) + minAdm( (t,) + M[2:] ) ]   (len(M) >= 3)

A "peel" of a length>=3 node M at cut t produces the corank block of size (M[0]-t) x (M[1]-t).
Define the block's index  d(M,t) = min(M[0]-t, M[1]-t).

An "optimal peel path" of a length-4 tuple (n,n,n,n) is a sequence of cuts, one per node, where at
every node the chosen cut t attains the minimum in the minAdm recurrence (i.e. it realises
minAdm of that node). Peeling (n,n,n,n) yields a length-3 node, then a length-2 node (the terminal
"base", which is not peeled). So a path has exactly two peel blocks, each with an index d.
</facts>

<subquestions>
Q1. For n = 3,4,5,6,7: list every optimal peel path of (n,n,n,n), and for each path give the pair
    of peel-block indices (d1, d2) = (d at the first peel, d at the second peel). (Ignore the base.)
Q2. For each n, compute  B(n) = min over optimal peel paths of  max(d1, d2)
    (the best achievable "largest corank-block index" over all optimal paths).
    Report B(n) for n = 3..7.
Q3. What is the SMALLEST n such that EVERY optimal peel path of (n,n,n,n) has max(d1,d2) >= 2
    (equivalently B(n) >= 2)? For n below that threshold, exhibit one optimal path whose peel-block
    indices are both <= 1.
Q4. Sanity: at any node M, is the recurrence value  (M[0]-t)(M[1]-t) + minAdm((t,)+M[2:])
    STRICTLY greater than minAdm(M) for every NON-optimal cut t (strict, not just >=)? Check for the
    nodes appearing in n=4..7.
</subquestions>

<output_contract>
For Q1-Q4: the exact values you computed and the method. State B(n) for n=3..7 as a table, the
threshold n from Q3, and a yes/no for Q4. End with a bare list of anything you'd want double-checked.
Do not speculate about "resolution" / "RLCT" / "native vs cited" downstream meaning — just the
combinatorics of the integer program.
</output_contract>

<grounding_rules>
- Exact integer DP only. If you cannot execute code, do the DP by hand/symbolically and SHOW the
  per-node recurrence values so the argmins are auditable.
- Derive B(n) and the threshold yourself; do not assume any value.
</grounding_rules>
