<task>
I am designing a FORMALISATION-READY proof (target: Lean 4 + Mathlib) of the type-A
(equioriented A_N) Gabriel decomposition, in a concrete matrix-tuple encoding. NO Lean code
needed from you — I want the cleanest PROOF STRATEGY for a human formaliser.

SHARED OBJECTS (the frame).
- Fix a dimension vector d = (d_0, d_1, ..., d_N) of natural numbers.
- A representation is a tuple of composable matrices A_* = (A_1, ..., A_N) over a field k,
  with A_i : k^{d_{i-1}} -> k^{d_i}. (This is "Rep_d"; equivalently a chain
  k^{d_0} --A_1--> k^{d_1} --A_2--> ... --A_N--> k^{d_N}, a representation of the
  equioriented type-A quiver 0 -> 1 -> ... -> N.)
- The group G_d = prod_{i=0}^{N} GL_{d_i} acts by simultaneous base change at each vertex:
  (P_0,...,P_N) . (A_1,...,A_N) = (P_1 A_1 P_0^{-1}, ..., P_N A_N P_{N-1}^{-1}).
  Two tuples are isomorphic as quiver representations iff they are in the same G_d-orbit.
- The interval module M_{ij} (for 0 <= i <= j <= N) is the chain that is 1-dimensional (=k)
  on vertices i, i+1, ..., j with identity maps along the interval, and 0 outside; the maps
  in and out of the interval are 0.
- The "rank pattern" of A_* is the array r_{ij} = rank(A_j A_{j-1} ... A_{i+1}) for i < j,
  with r_{ii} = d_i (rank of the empty/identity composite). r_{0N} = rank of the full product.
- Already proved (abstract, available as API): the cumulative map S and the second finite
  difference T are mutually inverse on arrays supported off the i<0, j>N half-plane:
  r_{ij} = S(m)_{ij} = sum_{k <= i <= j <= l} m_{kl}, and inversely
  m_{ij} = T(r)_{ij} = r_{ij} - r_{i,j+1} - r_{i-1,j} + r_{i-1,j+1}.

THE THEOREM TO PROVE (type-A Gabriel / interval-module decomposition).
Every representation A_* is isomorphic, via a G_d base change, to a direct sum of interval
modules  ⊕_{0<=i<=j<=N} M_{ij}^{⊕ m_{ij}},  with the multiplicities m_{ij} unique and given
by m = T(rank pattern of A_*). Equivalently: the rank pattern is a complete, base-change-
invariant isomorphism invariant of A_*, and the orbit decomposition follows.

WHAT I HAVE ALREADY ESTABLISHED / TRIED (facts in).
- The abstract inclusion-exclusion inversion S<->T is fully formalised and available.
- The rank pattern is clearly base-change invariant (rank(P_j C P_i^{-1}) = rank C for any
  composite C of the tuple, since the inner P's telescope and outer P's are invertible).
- For the simplest case d=(1,1,...,1) (a single chain of scalars) the reduction is easy.
- I want the EXISTENCE (normal form) half to be the cleanest possible inductive argument that
  a formaliser can grind, ideally reusing standard Mathlib linear algebra (rank, kernel, image,
  splitting a subspace as a complement, partial-permutation / staircase matrices) rather than
  building abstract abelian-category / Krull-Schmidt machinery from scratch.

QUESTIONS (I am withholding my own candidate skeleton on purpose).
1. What is the cleanest INDUCTIVE statement and induction variable for the existence/normal-form
   half (every tuple base-changes to a direct sum of interval modules)? Compare candidate routes:
   (a) induction on N (depth) peeling the last map A_N; (b) induction on the total dimension
   sum d_0+...+d_N peeling one interval summand at a time; (c) a Smith-/staircase- normal-form
   reduction bringing each A_i simultaneously to a 0/1 partial-permutation matrix compatible
   with its neighbours; (d) the standard "kernel/image filtration" or coefficient-quiver argument.
   For each viable route give: the exact inductive statement, the key lemma at the inductive step,
   the base-change moves used, and the single hardest step to formalise.
2. How does uniqueness of the multiplicities follow, given base-change invariance of the rank
   pattern and the abstract S<->T inversion already in hand? Is uniqueness essentially free once
   existence is known and we observe rank_pattern(⊕ M_{ij}^{m}) = S(m)?
3. Which steps, if any, would you recommend a formaliser CITE (e.g. Krull-Schmidt, Gabriel's
   theorem in general) rather than prove, and which are cheap enough to prove directly in the
   type-A case? Justify by formalisation cost, not by mathematical depth.
4. Any standard Mathlib facts (matrix rank, complements, splitting, partial permutations) that
   make one route dramatically cheaper than the others?
</task>

<output_contract>
Structure your answer as:
A. RECOMMENDED ROUTE — name it (a/b/c/d or a hybrid), one paragraph why it is cleanest to
   formalise.
B. THE INDUCTIVE STATEMENT — stated precisely, with the induction variable and the
   strengthened hypothesis if needed.
C. THE INDUCTIVE STEP — the key lemma(s), the base-change moves, and the single hardest step.
D. UNIQUENESS — how it falls out (3–6 sentences).
E. PROVE-vs-CITE — a short list, each item tagged PROVE or CITE with a one-line justification
   keyed to formalisation cost.
F. MATHLIB LEVERS — concrete reusable facts (rank/kernel/image/complement/permutation) that
   make the recommended route cheap; flag any you are UNSURE exist in Mathlib as INFERENCE.
Keep it tight. Distinguish clearly between mathematical FACT and your INFERENCE/RECOMMENDATION.
</output_contract>

<grounding_rules>
- This is a design review. You may assert standard representation-theory / linear-algebra facts,
  but flag anything that is a recommendation or a guess about Mathlib's contents as INFERENCE.
- Do not assume any particular Lean API beyond standard Mathlib matrix/linear-algebra. If you
  rely on a Mathlib lemma existing, say so and mark it INFERENCE.
- Prefer routes that minimise dependent-type / cast pain in a Fin-indexed matrix encoding.
- Concrete over vague: name the induction variable, the splitting, the exact composite whose
  rank is being tracked.
</grounding_rules>
