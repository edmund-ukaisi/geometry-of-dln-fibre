<task>
Adjudicate TWO truth-values with exact reasoning. Do NOT write or run code. Reason on paper.

SETTING. Real RLCT (log canonical threshold) of F = ||C^(1)...C^(L)||^2_Frobenius at the origin, for a
chain of real matrices C^(s) of size M^s x M^{s+1} (the "deep linear network" zero-product core; B=0).
The zero-locus {prod = 0} is stratified by rank vectors t=(t_1,...,t_L), t_j = rank of the partial
product C^(1)...C^(j). On {prod=0} the last rank t_L = 0. A rank vector is ADMISSIBLE if
weakly-decreasing (t_1>=...>=t_L), t_L=0, t_j <= M^{j+1}. The stratum S(t) has codimension
Mval(t) = sum_{j=1}^L (t_{j-1}-t_j)(M^{j+1}-t_j), with t_0 := M^1.

KNOWN/PROVEN in this project:
- The closed form: rlctAt(F) = lambdaCore = (1/2) * min_{t admissible} Mval(t). (Aoyagi 2013, Watanabe.)
- A flag-resolution resolves F by iterated blow-ups of the (coordinate-subspace) rank strata. Each
  blow-up of a stratum S(t) gives an exceptional divisor with (k,h)=(1, Mval(t)-1), ratio Mval(t)/2.
- The recursion-closing step (Schur complement = smaller matrix chain) is verified.
- For (2,2,2) (M=(2,2,2)), an explicit 24-leaf resolution was built and verified: rlctAt = 3/2.
  IMPORTANTLY, one branch (the "delta-branch", resolving the rank-1 stratum S(1,0)) bottomed out in a
  RESIDUAL SMOOTH BLOCK of dimension 4 (a nondegenerate sum of 4 squares), giving a cone-divisor of
  ratio 4/2 = 2 -- which is NOT a stratum-divisor, and which exceeded the binding ratio 3/2.

FACTS I have established by exact computation:
- (3,3,3) admissible strata and Mval: S(0,0)=9, S(1,0)=7, S(2,0)=7, S(3,0)=9. min = 7,
  so lambdaCore(3,3,3) = 7/2, with TWO achievers S(1,0) and S(2,0).
- The strata {S(0,0),S(1,0),S(2,0),S(3,0)} PARTITION {A1 A2=0} (indexed by t_1=rank(A1) in {0,1,2,3});
  every fibre point has a unique t_1 (numerically confirmed on 20000 samples).
- At the deepest representative of S(1,0) for (3,3,3), the generator-map Jacobian has rank 7 = Mval(1,0).
- Stratum-divisor ratios for (3,3,3): {7/2, 9/2}, min 7/2.
</task>

<sub_question>
(G3.4 — COVER EXHAUSTIVENESS) For GENERAL M (use (3,3,3) as the first non-trivial multi-stratum L=2
case, and reason about the general L>=2 pattern), does the iterated pivot-branch resolution COVER a
neighbourhood of the origin in {prod=0}, up to a null set -- i.e. does every admissible stratum get
resolved by SOME branch, leaving no stratum uncovered? Specifically: is the strata partition
{prod=0} = union_t S(t) (over admissible t) COMPLETE, and does the iterated pivot atlas have a branch
reaching each S(t)? Rule out ALL strata being missed, not just one. Is there any admissible stratum
that NO pivot-branch reaches?

(G3.5 — CHART<->VALUE SEAM, the lower bound) The lower bound rlctAt(F) >= (1/2) min_Adm Mval requires
EVERY exceptional divisor (across the whole resolution) to have ratio >= (1/2) min_Adm Mval. There are
TWO kinds of divisor:
  (A) stratum-divisors: ratio Mval(t)/2, t admissible. min over these = (1/2) min_Adm Mval by definition.
  (B) RESIDUAL SMOOTH-BLOCK cone-divisors: when a branch bottoms out in a residual nondegenerate
      sum-of-n-squares (like (2,2,2)'s dim-4 delta-block), monomializing it gives a cone-divisor of
      ratio n_block/2.
The lower bound is SOUND iff every residual smooth-block dimension n_block satisfies
n_block >= min_Adm Mval. QUESTIONS:
  (i)  Is there a structural reason a residual smooth block at a leaf must have dim n_block >=
       min_Adm Mval? (In (2,2,2): n_block=4 >= min_Adm Mval=3, held. Does it ALWAYS hold?)
  (ii) The deeper worry: could a branch produce an INTERMEDIATE divisor (not a terminal stratum-divisor,
       not a clean smooth-block) whose ratio is < (1/2) min_Adm Mval, breaking the lower bound? (E.g. a
       blow-up of a NON-admissible or lower-codim locus.) Or are all centers provably admissible strata?
  (iii) Is the binding monomialThreshold realised by the A1 ACHIEVER stratum (the min-Mval t)? I.e. does
       the chart-exponent min EQUAL (1/2) min_Adm Mval exactly -- no chart beats it, and the achiever's
       stratum-divisor attains it? Is this purely a fact about the resolution + Mval, or does it secretly
       require the separate A1 arithmetic (lambdaCore = clean closed form)?
</sub_question>

<output_contract>
- G3.4 verdict: COVER-EXHAUSTIVE (every admissible stratum reached, partition complete) or a SPECIFIC
  uncovered stratum / gap. Distinguish FACT (partition is complete) from INFERENCE (atlas reaches each).
- G3.5 verdict for each of (i),(ii),(iii): SOUND / a SPECIFIC counterexample-shaped worry. In particular
  give the cleanest argument (or the obstruction) for n_block >= min_Adm Mval, and for "all centers are
  admissible strata, no divisor < min/2".
- Be explicit whether the chart<->value match (binding = (1/2) min_Adm Mval) needs the A1 arithmetic
  (lambdaCore = closed form) or is independent of it.
- FACT vs INFERENCE labels throughout.
</output_contract>

<grounding_rules>
- Ground strictly in the facts above + standard resolution-of-singularities / RLCT theory (Watanabe,
  Aoyagi 2013, Lin). Reason on paper ONLY; do NOT read files or run code.
- "ratio of a divisor" = (h+1)/(2k) where the pullback is unit * prod |u_i|^{2k_i}, Jacobian prod|u_i|^{h_i}.
- min_Adm Mval is the minimum codimension over admissible strata.
- Preserve FACT vs INFERENCE. If a claim needs a hypothesis, name it.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication
as text. Rely solely on the facts given.
</important>
