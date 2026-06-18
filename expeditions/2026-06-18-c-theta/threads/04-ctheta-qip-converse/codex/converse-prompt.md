<task>
Setting: equioriented type-A quiver, vertices 0,1,...,N. A "Kostant partition" of a
dimension vector d=(d_0,...,d_N) is a function m on intervals [a,b] (0<=a<=b<=N) with
m_{a,b} a nonnegative integer, satisfying, for every vertex k:
    d_k = sum_{a<=k<=b} m_{a,b}      (column/Kostant constraint).
Fix corner m_{0,N}=0 and assume d is WEAKLY INCREASING (d_0<=d_1<=...<=d_N).

Define the quadratic form (this is the proven Ext-codimension / Cor 3.5 form):
    F(m) = sum_{1<=i<=u<=j<=v<=N} m_{i-1,j-1} * m_{u,v}.
Equivalently with a bilinear kernel: F(m)=sum_{P,Q} K(P,Q) m_P m_Q where for
P=(a,b),Q=(u,v): K(P,Q)=1 iff (0<=a<=b<=N-1 and a<u<=b+1<=v<=N).

Call an interval "horizontal-lace" if it touches an endpoint: a=0 OR b=N. Call a KP
"horizontal-lace (HL)" if all its support intervals touch an endpoint.

GOAL (the load-bearing converse of the QIP, Lehalleur-Rimanyi Thm 6.1 / Lemma 6.4):
prove that EVERY minimiser of F over the Kostant partitions of weakly-increasing d
with corner 0 is horizontal-lace. (The easy half -- HL KPs biject with e in N^N,
sum e = d_0, and F = G_d(e) = sum_{1<=j<=i<=N} e_i(e_j + d_j - d_{j-1}) -- is done.)

I have computed the EXACT change of F under the "uncrossing / outward swap":
take intervals [a,b],[c,d] with a<=c<=b<=d (a crossing/overlapping pair), replace one
copy of each by [a,d] and [c,b]. Symbolic result (verified all N<=7): 
    Delta F = 1 - m_{a,b} - m_{c,d} - (other nonnegative terms).
So at a KP with both sources present (m_{a,b}>=1, m_{c,d}>=1) and the swap nondegenerate,
Delta F <= 1 - 1 - 1 = -1 < 0: a strict decrease.

PROBLEM I hit: not every non-HL KP admits such a crossing swap. E.g. for d=(2,2,2)
the KP {[0,0]^2,[1,1]^2,[2,2]^2} (all singletons) is non-HL (the [1,1]'s are interior)
but has NO crossing/overlapping pair to uncross -- the singletons are pairwise
non-overlapping. It is not a minimiser (F=8 vs C=3), but the single-swap descent
does not reach it.
</task>

<output_contract>
1. State the STANDARD proof that QIP minimisers are horizontal-lace (Lemma 6.4 +
   the top-dimensional/minimality argument in Lehalleur-Rimanyi sec 6), in
   PURELY COMBINATORIAL terms on the multiplicity array / lace diagram -- NOT via
   orbit-closure geometry (I want to avoid the Voigt/closure interface).
2. What is the COMPLETE move set that drives an arbitrary KP to an HL KP with
   F non-increasing? In particular, what move reduces an ISOLATED interior interval
   like [1,1] that has no overlapping partner? (Candidates: a "merge+split" using a
   neighbouring interval, or a move that uses the weakly-increasing hypothesis to add
   an [i-1,i] edge "for free".) Be concrete about indices and which intervals change.
3. Is the cleanest Lean structure a WELL-FOUNDED DESCENT (on what measure -- total
   off-lace mass? sum of interval interior-lengths? a potential like
   sum m_{a,b}*(stuff)?) with a per-move strict-decrease lemma, OR is it cleaner via
   a direct CONVEXITY / rearrangement argument on G_d over the simplex
   {e in N^N : sum e = d_0}? If descent, give the measure that strictly decreases on
   every move and is minimised exactly on HL KPs.
4. Flag the single hardest sub-step for a Lean 4 / Mathlib formalisation, and whether
   the weakly-increasing hypothesis is essential to the move (where does it bite?).
</output_contract>

<grounding_rules>
- Distinguish what is a THEOREM (cite the mechanism) from what is your INFERENCE/guess.
- The orbit-closure "adding an edge back keeps it in Sigma^0 and contradicts maximality"
  argument is exactly what I must replace with a form-level (F-level) argument. If the
  only known proof is the geometric one, say so plainly.
- Do not paste long code; give the move + index bookkeeping in math.
- If you think descent on a single move type cannot work (because of isolated-interior
  configurations) and a 2-parameter family of moves is needed, say which family.
</grounding_rules>
