<task>
Adjudicate ONE architecture question for a Lean build, with exact reasoning. Do NOT run code.

SETTING. Resolving F = ||prod(C)||^2 (zero-product matrix-chain core, B=0) at the origin, prod=C^(1)...C^(L),
C^(s) of size M^s x M^{s+1}. The RLCT = (1/2) min over admissible rank vectors t of Mval(t). A formaliser
team (fm-2 + a separate model) found the resolution is: det-1 GL-straightening of regular blocks, THEN
explicit blow-ups along rank-defect strata (monomial Jacobian prod u^{h}), giving RLCT = min_j (h_j+1)/(2k_j)
= inf monomialThreshold. The (2,2,2) case provably needed the blow-up (Jacobian (x 0)^n).

THE QUESTION: is the det-1 GL-straightening (a "Schur reduction": using a unit pivot minor, det-1 row/col
ops clear the pivot row/col and reduce the chain to a smaller chain) a GENUINELY NEEDED PIECE of the
build, or is it ELIMINABLE (a pure blow-up cover does everything)?
  (C2) GL-straighten THEN blow-up: the det-1 Schur is needed.
  (C1) pure blow-up cover: the det-1 Schur is not needed.

FACTS I established by exact computation (anchor (2,2,2), F=||A1 A2||^2):
- NODE 1: blow up {A1=0}. {A1=0} is ALREADY a coordinate subspace (the 4 entries of A1 = 0). So the
  first blow-up is a clean coordinate-subspace blow-up, Jacobian x^3 (codim 4), F = x^2 ||Ahat A2||^2,
  Ahat[0,0]=1 (a unit). NO straightening needed for node 1.
- NODE 2: the residual ||Ahat A2||^2 with Ahat[0,0]=1 a unit. The det-1 Schur clear (unit pivot
  Ahat[0,0]=1: row op R2 -= q R1, col op C2 -= p C1) reduces Ahat to [[1,0],[0, r-pq]], Schur complement
  w = r-pq. The residual rank-defect center becomes {w=0, ...}. But {r-pq=0} (in the (p,q,r) coords) is a
  BILINEAR HYPERSURFACE, NOT a coordinate subspace. After the det-1 change of variable w := r-pq
  (unit-Jacobian, dr/dw=1), it BECOMES the coordinate {w=0}, on which the coordinate-subspace blow-up
  applies. So at node>=2 the rank-defect center is NOT a coordinate subspace until straightened.
- The det-1 Schur is unit-Jacobian (no monomial weight); the monomial weights come only from the blow-ups.
</task>

<sub_question>
1. Is the build (C2) GL-straighten-then-blow-up (det-1 Schur a needed step) or (C1) pure blow-up cover
   (det-1 Schur eliminable)? Decide, with the explicit reason.
2. The crux: at node>=2, the rank-defect center is a bilinear hypersurface (e.g. {r-pq=0}), NOT a
   coordinate subspace. Can a coordinate-subspace blow-up machinery (the (2,2,2) pivotBlowup style,
   which blows up COORDINATE subspaces) be applied to a non-coordinate (bilinear) center directly, or
   must the det-1 Schur FIRST straighten it to a coordinate subspace? If straightening is required, the
   det-1 Schur is needed (C2). If the blow-up can directly handle the bilinear center (e.g. by blowing
   up the ideal, not a coordinate subspace), then it might be eliminable (C1) -- but does Lean/the
   chosen machinery support blowing up a non-coordinate ideal, or only coordinate subspaces?
3. A separate consideration: can a pure sequence of COORDINATE-subspace blow-ups (without any det-1
   straightening) resolve ||prod(C)||^2? (I.e. is the determinantal/rank-defect variety resolvable by
   coordinate blow-ups alone?) Or is the GL-straightening intrinsic to keeping the centers coordinate?
4. Give the cleanest exact statement of the recursion NODE for fm-2's #111 chart family: the explicit
   chart Jacobian, and whether each node = [det-1 Schur straighten (unit Jac)] then [coordinate-subspace
   blow-up (Jacobian u^{Mval(t)-1})].
</sub_question>

<output_contract>
- Verdict: (C1) or (C2), with the explicit reason.
- Whether the chosen blow-up machinery (coordinate-subspace blow-up) can handle a bilinear/non-coordinate
  center directly, or needs the det-1 straightening first.
- The cleanest exact recursion-node statement for the Lean chart family.
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard resolution / RLCT theory (Aoyagi 2013, Watanabe), and what a
  "coordinate-subspace blow-up" can vs cannot do (it blows up {y_1=...=y_c=0}, a coordinate subspace).
- Reason on paper ONLY; do NOT read files or run code.
- "det-1 Schur" = unit-pivot row/col ops, unit Jacobian, reduces the chain; "blow-up" = monomial Jacobian.
- Preserve FACT vs INFERENCE. Be blunt.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
