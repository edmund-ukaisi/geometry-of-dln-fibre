<task>
We are formalising (in Lean 4) the orbit-closure order on rank patterns of the equioriented type-A_n
quiver. I need to decide whether one combinatorial lemma has a DIRECT, elementary, constructive proof
or whether it genuinely requires the Abeasis-Del Fra lace-diagram "cover classification" theorem.

SETUP (exact, all integer-valued; this is the combinatorial shadow of representation degenerations):
- Vertices 0..N. Intervals [a,b] with 0<=a<=b<=N. A "multiplicity array" is m[(a,b)] >= 0 (a Kostant
  partition / lace data). The dimension vector is d_t = sum_{a<=t<=b} m[(a,b)].
- The "rank pattern" of m is r[(i,j)] = sum over intervals with a<=i and j<=b of m[(a,b)], for i<=j
  (this is the 2D cumulative sum / "cumul"). The diagonal r[(i,i)] = d_i. The map m <-> r is a bijection
  (inverse = second finite difference: m[(a,b)] = r[a][b]-r[a][b+1]-r[a-1][b]+r[a-1][b+1], out-of-range r=0).
- Order: s <= r  iff  for all i<=j, s[(i,j)] <= r[(i,j)]. (s,r both rank patterns of achievable m,m'>=0,
  SAME dimension vector d.)
- "Linked box move" with indices a < c <= b+1 <= e, applied to multiplicities m:
      m[(a,e)] -= 1;  (if c<=b) m[(c,b)] -= 1;   m[(a,b)] += 1;  m[(c,e)] += 1.
  (split case c=b+1: omit the [c,b] term.) It is APPLICABLE to m if m[(a,e)]>=1 and (c=b+1 or m[(c,b)]>=1).
  EXACT FACT (verified by exhaustive sympy over many m): this move sends r to r' = r - 1_D where the
  "drop rectangle" is D(a,c,b,e) = { (i,j) : a<=i<c  and  b<j<=e }, and it preserves the dimension vector.

THE LEMMA I NEED (the "descent step"):
  Given achievable rank patterns with s < r (strict, same d), there EXISTS a linked box move applicable
  to m(r) whose drop rectangle D is contained in supp(g) where g = r - s (i.e. D only touches cells with
  g>0). Then r' = r - 1_D satisfies s <= r' < r, and one inducts on Phi = sum_{i<j}(r[(i,j)]-s[(i,j)]).
  (Move-existence verified by exhaustive sympy: ZERO failures over d=(2,2,2),(1,2,2,1),(2,2,2,2),(1,2,3,2,1)
   etc., all s<r pairs.)

WHAT I OBSERVED:
- Single-cell drops are NOT always available: a single-cell drop at (p,q) needs BOTH m[(p,q')]... ; in
  general the minimal valid drop is a genuine RECTANGLE.
- A "maximal u in [s,r)" route would reduce move-existence to "r covers u => the cover is a linked move",
  which is exactly the Abeasis-Del Fra cover-classification theorem (heavy).

THE QUESTION:
  Is there a DIRECT construction of the witnessing (a,c,b,e) from r and g alone (no enumeration of the
  poset, no "maximal u", no cover-classification), whose CORRECTNESS PROOF is elementary (induction /
  extremal-corner / pigeonhole on the integer arrays m, r, g)? Specifically I want a construction +
  proof sketch that a Lean formaliser can build in ~2-3 modules without reproving the lace/multisegment
  cover theorem.
</task>

<output_contract>
1. VERDICT: does a direct elementary construction exist? (yes / no / partial). One paragraph.
2. If yes: give the explicit rule choosing (a,c,b,e) from (r, g=r-s, m=m(r)), and the KEY LEMMA whose
   proof makes it work — state precisely WHY the chosen move is (i) applicable to m(r) and (ii) has
   D subset supp(g). Identify the extremal/pigeonhole principle doing the work.
3. If no / partial: name precisely the obstruction — the exact sub-fact that forces cover-classification,
   and whether a WEAKER target (e.g. allowing a chain of moves with total drop in supp(g), not a single
   move) is elementarily provable.
4. Sanity check your construction against this instance: N=3, d=(1,2,2,1).
   r = cumul of m_r=[(0,3):1,(1,2):1,(1,1):1,(2,2):1]  (so r[(0,3)]=1, r[(1,2)]=2,...).
   s = cumul of m_s=[(0,1):1,(1,2):1,(2,3):1,(1,2):...]  -- pick any achievable s<r you like with same
   d=(1,2,2,1) and show your rule's first move.
5. Distinguish clearly: which of your claims are PROVEN facts vs heuristic/conjectural.
Be concise and concrete. Prefer an explicit index formula over prose.
</output_contract>

<grounding_rules>
- Do not claim a construction works without giving the proof mechanism; if you are unsure, say so.
- "supp(g)" means cells (i,j), i<=j, with g[(i,j)]>0; note g[(i,i)]=0 since d is fixed.
- The reduction to "maximal u + cover" is known; I am asking specifically whether it can be AVOIDED.
- This is a real formalisation decision: an over-optimistic "yes" that needs cover-classification anyway
  costs us a multi-module detour. Be calibrated.
</grounding_rules>
