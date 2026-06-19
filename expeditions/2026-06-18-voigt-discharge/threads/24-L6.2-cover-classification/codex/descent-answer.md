**Verdict**

Partial, but effectively **no** for the Lean-planning question. The descent lemma is not merely adjacent to the Abeasis-Del Fra cover classification: in full generality it **implies** the rank-cover part of that classification. So a direct proof may exist as a new elementary proof, but it cannot avoid proving the core cover-classification subfact.

**Obstruction**

The forced subfact is:

> If `u < r` is a cover in the rank-pattern poset, then `u = r - 1_D` for one linked box move applicable to `m(r)`.

Indeed, apply your descent lemma with `s = u`. It gives a move `r' = r - 1_D` with `u <= r' < r`. Since `u` is covered by `r`, this forces `r' = u`. Thus the descent lemma immediately classifies covers.

Conversely, the usual “choose maximal `u` with `s <= u < r`” argument derives the descent lemma from cover classification. So, over finite rank-pattern fibers, the two are equivalent in logical strength.

**Constructive Rule That Is Safe But Not Lighter**

A natural direct rule is:

1. Let `g = r - s`.
2. Choose the north-east defect corner  
   `a = min { i | exists j, g(i,j) > 0 }`,  
   `e = max { j | g(a,j) > 0 }`.
3. Then
   `m_r(a,e) - m_s(a,e) = g(a,e) > 0`,
   because the north/east boundary terms in the second finite difference vanish. Hence `m_r(a,e) > 0`.
4. Search pairs `a < c <= b+1 <= e` with
   `c = b+1 or m_r(c,b) > 0`,
   and
   `D(a,c,b,e) subset supp(g)`,
   and take the lexicographically first one.

If the search succeeds, correctness is immediate: applicability is exactly the multiplicity condition, and `D subset supp(g)` gives `s <= r - 1_D`. The hard theorem is precisely that this search always succeeds. Proving that nonemptiness is the cover-classification subfact above.

**Weaker Targets**

A “chain of downward linked moves whose total drop stays in `supp(g)`” is not really weaker: the first move already has its drop rectangle inside `supp(g)`, so it gives the original descent step.

A genuinely weaker statement, connectivity of two decompositions with the same dimension vector using linked moves in both directions, is elementary via interval straightening / toric fiber moves. But it does not preserve `s <= current_rank`, so it does not prove the orbit-closure descent.

**Sanity Check**

Your listed `m_r = [(0,3):1,(1,2):1,(1,1):1,(2,2):1]` has dimension vector `(1,3,3,1)`, not `(1,2,2,1)`.

For the corrected same-`d` example, take

`m_s = [(0,2):1,(1,3):1,(1,1):1,(2,2):1]`.

Then `g` is supported only at `(0,3)`. The first move is

`(a,c,b,e) = (0,1,2,3)`,

using `[0,3]` and `[1,2]`:

`[0,3] + [1,2] -> [0,2] + [1,3]`.

Its drop rectangle is `D = {(0,3)}`, so `D subset supp(g)`, and the result is exactly `s`.

**Status**

Proven: the descent lemma is equivalent in strength to rank-cover classification.  
Heuristic only: the north-east-corner finite search is a good constructive implementation strategy. Its total-correctness proof is not a lightweight substitute for cover classification.