<task>
Independently adjudicate whether a specific polynomial "split" property CAN hold for a residual
family arising from a blow-up resolution, and if not, locate the exact obstruction. Exact algebra
only. Do NOT rubber-stamp; construct/verify.
</task>

<context>
Setting: Aoyagi-style recursive block blow-up resolution of the product map of a deep linear
network. Coordinates u_{L,r,c} are the entries of matrices A_L (L=0..N-1), A_L of size d_{L+1} x d_L.
The "core" is coreGen = the entries of the full product P = A_{N-1}···A_1·A_0.

A resolution walks a tree of edges. Each edge carries a change of coordinates ("step map") applied
to the argument of coreGen; foldResid(node)(u) = coreGen( T_1(T_2(...T_n(u)...)) ), T_1 the root edge
(outermost). Each step map is  blockBlowupMap(center,pivot) ∘ shear   (δ=0) or
blockBlowupCoordQuot(pivot) ∘ shear (δ=1, δ=1 iff parent has cleared=0). Here:
 - blockBlowupCoordQuot(pivot): sets coord=pivot -> 1, else unchanged (strict transform).
 - blockBlowupMap(center,pivot): pivot -> w_pivot; center members j -> w_pivot·w_j; spectators fixed.
 - shear = the "canonNormalizationOf" displacement u -> u + phi(u), a 3-branch formula at pivot (a,b),
   layer S, cleared J (scoped: sums exclude indices < J):
     branch (i)   interior Schur:   for layer S, row!=a, col!=b, row>=J, col>=J:
                    phi = - u_{S,row,b} · u_{S,a,col}
     branch (ii)  +gamma output recoord: for layer S+1, col == a:
                    phi = sum_{i != a, i>=J}  u_{S,i,b} · u_{S+1,row,i}
     branch (iii) input recoord: for layer S-1, row == b:
                    phi = sum_{k != b, k>=J}  u_{S,a,k} · u_{S-1,k,col}
   The shear is applied for "case2"/"case12" edges; it is the IDENTITY for "case11"/"rollover" edges.
   NOTE: the shear does NOT zero the pivot's own row/column in layer S (only the interior Schur on the
   strict-interior). A separate "row-clear" device is applied elsewhere in the proof, NOT in the fold.

The canonical branch for d=(2,2,2,2) (N=3 layers, all 2x2) up to the parent p of the first "case11"
(merge) edge is: [case2 @(layer0,cleared0,δ=1,pivot(0,0,0)), case2 @(layer0,cleared1,δ=0,pivot(0,1,1)),
rollover @(layer0,cleared2)]. The parent state is (layer1, cleared0).

The CHILD case11 edge (merge) reuses the divisor born at layer0/cleared1; its data:
  pivot e2 = (0,1,1)  [the reused divisor's diagonal birth corner],
  center = {(0,1,1), (1,0,0), (1,1,0)}   [ {e2} ∪ (layer-1, col 0, all rows) ],
  supportAt(parent) = all of layer 1 = {(1,0,0),(1,0,1),(1,1,0),(1,1,1)},
  part  = supportAt ∩ center = {(1,0,0),(1,1,0)},
  extra = supportAt \ center = {(1,0,1),(1,1,1)}.

THE SPLIT PROPERTY to adjudicate (for the PARENT residual foldResid(p), each output slot j):
  foldResid(p)_j (u) = ( sum_{i in part} alpha_i(u)·u_i ) + u_{e2} · ( sum_{i in extra} beta_i(u)·u_i )
  with alpha_i, beta_i polynomial/continuous and NOT depending on the "center" coordinates.
Equivalently: foldResid(p)_j is in the ideal <center>, and the coefficient of each extra coordinate
u_i is divisible by u_{e2}.
</context>

<facts_computed_exactly>
Computing foldResid(parent) with the 3-branch scoped shear on the (2,2,2,2) branch above gives
(P = A_2·A_1·A_0, slot j = entry (j//2, j%2)):

 slot 0 = u_100·u_200 + u_110·u_201 + 2·u_010·u_101·u_200 + 2·u_010·u_111·u_201
 slot 1 = u_001·u_100·u_200 + u_001·u_110·u_201 + u_011·u_101·u_200 + u_011·u_111·u_201
 slot 2 = u_100·u_210 + u_110·u_211 + 2·u_010·u_101·u_210 + 2·u_010·u_111·u_211
 slot 3 = u_001·u_100·u_210 + u_001·u_110·u_211 + u_011·u_101·u_210 + u_011·u_111·u_211
 (u_LRC written u_{LRC}; e.g. u_010 = coord (0,1,0).)

Exact Gröbner results (grevlex, ideal membership):
 - every slot ∈ <supportAt> = <u_100,u_101,u_110,u_111> : TRUE (degree-1 in layer 1).
 - slot 0, slot 2 ∈ <center> = <u_011,u_100,u_110> : FALSE.  slots 1,3 ∈ <center> : TRUE.
 - <center ∪ {u_010}> contains ALL slots (u_010 = (0,1,0) is the single obstruction coord for 2,2,2,2).
 - coefficient of extra coord (1,0,1) in slot 0 = 2·u_010·u_200  (factors through u_010, NOT u_011=e2);
   coefficient of extra coord (1,0,1) in slot 1 = u_011·u_200  (factors through u_011=e2).
 So the coordinate that the "extra" block factors through DEPENDS ON THE OUTPUT COLUMN:
   output col 0 (slots 0,2) -> factors through u_010 = (0,1,0);
   output col 1 (slots 1,3) -> factors through u_011 = (0,1,1)=e2.
</facts_computed_exactly>

<questions>
1. Can the split property hold for the PARENT residual foldResid(p) with a SINGLE fixed e2 (here (0,1,1))
   across all slots, given the computed forms? If not, prove it cannot (exhibit the obstruction cleanly).
2. Identify the STRUCTURAL source of the obstruction. Note the factor "2·u_010" in slots 0/2. What are
   the two contributions summing to that 2, and what does that say about the interaction between the
   branch-(ii) shear and the (un-zeroed) pivot column of A_0?
3. The coordinate u_010 = (0,1,0) is the below-pivot entry of A_0's cleared column 0. In the FULL
   Aoyagi resolution, clearing pivot (0,0) makes A_0's column 0 a unit vector [1,0]. If A_0's columns
   were unit vectors (input layer fully reduced), would the single-e2 split hold? What minimal
   modification to foldResid(p) (e.g. composing an input-column clear before reading coreGen) would
   make the single-e2 split TRUE, if any?
4. State precisely, in one sentence, what the correct SPLIT-carrying object is: raw foldResid(p), or
   foldResid(p) after an input/row clear, or a different center. Be concrete.
</questions>

<output_contract>
- A verdict on Q1 (CAN single-e2 split hold on raw foldResid(p)?) with an exact justification.
- The structural diagnosis for Q2 (the "2" decomposition).
- A concrete answer to Q3/Q4: the object on which the split DOES hold, if the raw one fails.
- Flag clearly what is a mathematical FACT (you verified) vs an INFERENCE about the intended construction.
- Show any algebra you rely on; do not paste code you did not mentally execute.
</output_contract>

<grounding_rules>
Exact algebra only. If you assert an ideal membership or divisibility, justify it. Distinguish
"the given forms imply X" (fact) from "the construction probably intends Y" (inference).
</grounding_rules>
