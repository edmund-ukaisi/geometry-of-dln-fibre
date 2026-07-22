<task>
Adjudicate a sharp algebraic truth-value about a resolution-of-singularities fold (Aoyagi's blow-up
recursion for deep-linear-network loss). Exact algebra only. I withhold my own tentative conclusion;
give me your independent read.

SETUP (all facts, verified against the source Lean/paper; take them as given):

Coordinates u live on R^flatDim, partitioned into per-layer blocks. For a depth-N net with widths
d_0..d_N, layer s (0<=s<N) contributes a block of coordinates u_{(s, row, col)}, row in Fin d_{s+1},
col in Fin d_s. Write layer-s block = { u_{(s,·,·)} }.

The "core generators" are the entries of the matrix product  M = A_{N-1}·A_{N-2}·...·A_1·A_0, where
A_s is the d_{s+1} x d_s matrix whose entries ARE the layer-s coordinates. So each generator
coreGen[i][j] = sum over multi-index of a product with EXACTLY ONE factor from each layer:
it is MULTI-AFFINE — degree exactly 1 in each layer block separately (bilinear for N=2, trilinear N=3).

A "fold step" at a node with state (layer S, cleared J) transforms the residual family by composing
with a coordinate change and (when J=0, "delta=1") dividing out a pivot. The three exact operations,
each a map R^flatDim -> R^flatDim or -> R:

  1. blockBlowupMap(center S_set, pivot p):  w |-> ( k |-> if k=p then w_p ; else if k in S_set then w_p*w_k ; else w_k ).
     center S_set is (a subset of) the current layer-S block; pivot p is one layer-S coordinate.
  2. blockShear(phi):  w |-> w + phi(w),  where phi = canonShearOf is the "canonical Schur shear":
        phi(w)_k = -w_gamma * w_beta   if k = (S, row, col) with row>J and col>J  (strict interior of layer-S block),
                    where gamma = (S,row,J) [pivot-column tail], beta = (S,J,col) [pivot-row tail];
                 = 0 otherwise.
     So blockShear(canonShearOf) sends the interior entry d_{row,col} |-> d_{row,col} - d_{row,J}*d_{J,col}
     (a Schur-complement update on the layer-S block interior), fixing all other coordinates.
  3. strict transform qm(w)_k = if k=p then 1 else (blockShear(phi) w)_k   [pivot set to 1, shear applied to the rest].

The step map at delta=1 is: child_residual(u) = parent_residual( qm(u) ).   (blow-up outermost; pivot divided out.)

THE INVARIANT the fold must preserve at each node, call it Deg1SupportedSlot(resid, S_supp, fromLayer):
  (a) resid(u) = sum_{i in S_supp} c_i(u) * u_i   with each c_i CONTINUOUS and IGNORING the S_supp coords
      (support-decomposition: resid is a linear form in the S_supp coordinates);
  (b) resid is per-layer total-degree <= 1 in every layer block at index >= fromLayer.

At the PARENT (delta=1 node, cleared J=0): S_supp = layer-S block, fromLayer = S.
At the CHILD (after a fresh/inherited append, cleared 1): S_supp = layer-(S+1) block, fromLayer = S+1.
(The support DESCENDS one layer per clear, per the elder's ruling.)

THE TWO SHARP QUESTIONS:

Q1 (descent/cofactor). Is it TRUE that, for a residual that is MULTI-AFFINE (degree 1 per layer) and
Deg1-supported on the layer-S block, the child residual  parent(qm(u))  is Deg1-supported on the
layer-(S+1) block with per-layer-degree<=1 from layer S+1 up? Concretely: does the strict transform
(pivot->1, Schur-clear layer-S interior) turn the layer-S support-decomposition into a layer-(S+1)
support-decomposition? Give the mechanism (which factor of the multi-affine product supplies the
layer-(S+1) linear factor after the pivot is divided out).

Q2 (is the SHEAR load-bearing for Q1). Consider replacing canonShearOf by the IDENTITY shear (phi=0,
so the layer-S interior is NOT Schur-cleared). Does the child STILL satisfy the invariant (both (a) and
(b))? If YES for both, the Schur shear is not needed for the descent. If the identity shear BREAKS (b)
(per-layer degree <=1 from S+1 up), identify the surviving degree-2 monomial and which layers it lives
in. Be precise about whether the broken degree-2 term lives in a layer >= fromLayer (a real violation)
or a layer < fromLayer (allowed, below threshold).

Q3 (boost variant). Separately: at a "case-1(1) boost" node the append REUSES a pivot u_p born at an
EARLIER layer S'<S, and the support-decomposition must hold on a SMALLER center {u_p} union (partial
layer-S block of only the "dominant" rows i<J_1), NOT the full layer-S block. The residual there has the
form  resid[i][j] = r_i * (D·H)[i][j],  r_i = b_i/b_1  a monomial in earlier pivots with the property
u_p | b_i  iff  i > J_1 (dominant rows i<J_1 are u_p-free), D = layer-S block, H = deeper product.
Is the support-decomposition on {u_p} union partial-block a consequence of the SHEAR (canonShearOf), or
of the b-chain divisor combinatorics (the r_i structure), or both? Which mechanism supplies which part?
</task>

<output_contract>
Answer Q1, Q2, Q3 in that order, each a short paragraph. For Q1 give the explicit factor that becomes
the layer-(S+1) linear part. For Q2 give a YES/NO on whether identity shear preserves the invariant, and
if NO the explicit surviving degree-2 monomial and its layers. For Q3 attribute each needed piece to
SHEAR vs B-CHAIN-COMBINATORICS. End with a one-line verdict: are Q1's descent and Q3's boost the SAME
underlying fact discharged by one mechanism, or DISTINCT facts needing distinct mechanisms?
</output_contract>

<grounding_rules>
Reason from the exact algebra above; do not invent Lean lemma names. Flag any step where you are
inferring vs computing. If a claim depends on an assumption about the residual's structure not stated
above, name the assumption explicitly. Small worked examples (N=2 bilinear, N=3 trilinear, a 2x2 layer
block) are encouraged and are the kind of evidence I trust.
</grounding_rules>
