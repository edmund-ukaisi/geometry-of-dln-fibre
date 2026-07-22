<task>
Work ONLY from this prompt. Do NOT read any repository files. Write and run a FRESH self-contained
sympy script in /tmp and report. Adjudicate one truth-value by exact algebra.

SETUP (2x2 matrices, all entries independent symbols). Three matrices:
  A0, A1, A2, each 2x2; A_L[r][c] is an independent real symbol; write coords u_(L,r,c).
Product  M = A2 * A1 * A0  (2x2). coreGen = the 4 entries M[i][j].

A "fold" resolves the product by clearing A0 first. The residual family = coreGen composed with a
chain of coordinate maps. Per-edge maps (blow-up OUTERMOST):
  blockBlowupMap(S,p,w)[j]    = w[p] if j==p ; w[p]*w[j] if j in S ; else w[j]
  blockBlowupCoordQuot(p,w)[j]= 1 if j==p ; else w[j]
  edgeShear = identity for a "case11"/"rollover" edge; = (u |-> u + phi(u)) for "case2"/"case12",
  where phi = canonShear(s):  for coord k=(L,r,c),  phi[k] = -u_(L,r,s.cleared)*u_(L,s.cleared,c)
     if  L==s.layer and s.cleared<r and s.cleared<c,  else 0.
  stepMap = blockBlowupMap(center,pivot) . edgeShear ;  qm = blockBlowupCoordQuot(pivot) . edgeShear.
Recursion (delta = [parent.cleared==0]):  foldResid(root)=coreGen ;
  child(j)(u) = parent(j)(qm(u))  if delta==1 ;  = parent(j)(stepMap(u))  if delta==0.
So foldResid at depth n = coreGen(map_ed1(map_ed2(...map_edn(u)))), ed1 OUTERMOST (applied last).

THE PATH (verified separately; take as given). Three edges to node p:
  ed1: case2, delta=1, parent state (layer=0,cleared=0), pivot = coord (0,0,0),
       shear = canonShear(layer0,cleared0)  [writes only coord (0,1,1) = -u_(0,1,0)*u_(0,0,1)].
  ed2: case2, delta=0, parent (0,1), pivot=(0,1,1), center={(0,1,1)}, shear=canonShear(0,1)=0.
  ed3: rollover, delta=0, parent (0,2), center={}, pivot=none.
At p the resolution does a "case11" boost reusing the divisor born at corner (0,1) [coord (0,1,1)],
with runLen=1.  Boost data:  pivot = u_(0,1,1);  partial block = layer-1 col<1 = {u_(1,0,0),u_(1,1,0)};
extra block = layer-1 col 1 = {u_(1,0,1),u_(1,1,1)};  center C = {u_(0,1,1)} ∪ partial.

COMPUTE and REPORT:
1. foldResid at p (the 4 polynomials). Which of ed1/ed2/ed3 act nontrivially?
2. Is each residual entry `Deg1SupportedOn C`, i.e. lies in the ideal (C) with every EXTRA-block coord
   appearing ONLY multiplied by u_pivot=u_(0,1,1)?  Tests: (A1) vanishes when all C=0; (A2) deg<=1 in C;
   (A3) each extra coord's coefficient vanishes at u_(0,1,1)=0.  Give True/False + breaking monomials.
3. If it FAILS: what minimal ingredient, ADDED to the maps above, makes it boost-ready? Test explicitly:
   (i) a fuller clear of A0's pivot with the elementary L,U factors zeroing the pivot ROW and COLUMN
       (not just the Schur interior cross-term canonShear gives); AND/OR
   (ii) a recoordinatization of the DEEPER matrix A1 -> A1 * Q^{-1}, Q the pivot-column-clearing factor;
   AND/OR (iii) taking the boost pivot to be the Schur-reduced coordinate rather than the literal corner.
   Build the corrected residual and RE-RUN A1/A2/A3.
4. Is the underlying claim TRUE for a faithful clear of A0 (i.e. is there SOME correct realization on
   which the layer-1 residual is degree-1 on the boost center)? YES/NO + the construction.
</task>
<output_contract>
Terse, numbered 1-4. For each load-bearing claim, paste the exact sympy and its printed output.
State the final verdict: is foldResid-at-p (maps EXACTLY as given) boost-ready? and is the underlying
claim true for a corrected clear? Flag inference vs computed fact.
</output_contract>
<grounding_rules>
Do NOT read repo files; everything you need is above. Compute with sympy, do not hand-wave. If a step
is ambiguous, try both readings. Do not assume the answer.
</grounding_rules>
