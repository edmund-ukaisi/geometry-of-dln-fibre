<task>
Equioriented type-A quiver (linear chain 0 -> 1 -> ... -> N, all arrows one direction).
Representations decompose into INTERVAL (lace) modules M_[a,b] (a<=b), Gabriel's theorem.
A representation is encoded by its multiplicity array m: m_{ab} = # copies of M_[a,b] (a<=b, so 0<=a<=b<=N).
Its RANK PATTERN is r_{ij} = sum_{k<=i, j<=l} m_{kl}  (i<=j); equivalently m = second finite difference of r.
The dimension vector is d_k = r_{kk} = sum_{a<=k<=b} m_{ab}.

Orbit-closure order (Abeasis-Del Fra, equioriented type A): for two reps r, s with the SAME dimension vector d,
  O_s ⊆ closure(O_r)  iff  s <= r  entrywise on rank patterns: forall i<=j, s_{ij} <= r_{ij}.
The "hard" direction is s <= r  ==>  O_s ⊆ closure(O_r), proved via "lace diagram combinatorics".

I want to prove this hard direction by exhibiting, for s <= r, a FINITE CHAIN of ELEMENTARY DEGENERATIONS
(box moves) from r down to s, each a one-parameter polynomial family realizing the closure containment,
then induct. I need the precise combinatorial engine.

The candidate elementary "box move" on the multiplicity array, on two interval modules:
   M_[a,e] (+) M_[c,b]  ~~>  M_[a,b] (+) M_[c,e]    for  a <= c <= b <= e
(nested outer [a,e] ⊇ inner [c,b] degenerates to "linked" [a,b],[c,e]; preserves d; drops rank).
There is also a SPLIT M_[a,e] ~~> M_[a,p] (+) M_[p+1,e].

Questions (be concrete and rigorous, cite the standard statement if you know it):
1. What is the EXACT, standard set of elementary/minimal degenerations (covers of the rank order) for
   equioriented type A? Is the nested box move above (with which precise index condition) the right one,
   and is the split a special/limit case or a separate generator?
2. For the induction "s <= r, s != r  ==>  there EXISTS an elementary box move r ~~> r' with s <= r' < r
   (strictly below r, still >= s)": what is the UNIFORM, CONSTRUCTIVE move-existence lemma? i.e. given the
   gap r - s, how do you CHOOSE which two bars of r to recombine (and the parameters a,b,c,e) so that the
   resulting r' still dominates s? A naive "split the longest bar at the first deficient column" can overshoot
   below s. What is the correct deterministic choice?
3. What is the right INDUCTION MEASURE that strictly decreases at each step (e.g. sum_{i<j}(r_{ij}-s_{ij}),
   or a statistic on the multiplicity array / a lace-diagram crossing number)?
4. Does this reduce to a CLEAN induction provable without heavy lace-diagram bookkeeping (just on the
   multiplicity/rank arrays), or does the move-existence step genuinely require the lace-diagram structure
   (e.g. tracking individual "lace strands" / a matching) to choose the recombination? Be honest about which.

Cite Abeasis-Del Fra "Degenerations for the representations of an equioriented quiver of type A",
or Bruns-Vetter / rank-variety minimal-degeneration results, if you can.
</task>

<output_contract>
Sections, terse:
1. Elementary degenerations (exact statement + index condition; split vs nest).
2. Move-existence lemma (the constructive choice rule; how to avoid overshoot below s).
3. Induction measure.
4. Verdict: clean multiplicity/rank induction, OR genuinely needs lace-strand bookkeeping. Which step is the crux.
5. Citations.
</output_contract>

<grounding_rules>
Distinguish what you KNOW (standard theorem, citable) from what you INFER. If you are not certain the
nested box move generates all covers, say so. If the constructive move-choice is subtle, give the actual
construction, not a hand-wave. Do not claim a clean induction if the move-choice genuinely needs the lace structure.
</grounding_rules>
