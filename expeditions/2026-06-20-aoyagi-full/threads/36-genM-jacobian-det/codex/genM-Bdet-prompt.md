<task>
SHARP VERDICT on a parametric construction; do NOT explore a repo. Confirm/refute a specified decoder + flag any research wall.

SETTING. A deep-linear-network resolution chart over widths M=(M_0,...,M_L). A "chain" decoder `B_det M`
produces L layer matrices via a recursion (the radial scalar is u=x_p):
   C_L = u * Rfin_L                              (leaf transition, Text_L x Wext_L = Text_L x M_L)
   C_k = Bmat_k * chainQ(N_k) + u * Rmat_k        (interior Schur frame, k=1..L-1)
   A_k = chainA(N_k, W_k, C_{k+1})                (layer matrix, a block stack [C_{k+1} - N_k W_k ; W_k])
where Text_k = the chain rank after k matrices (Text_0=M_0, Text_{k+1}=tStar_k, the achiever descent,
strictly decreasing to Text_L = ... small), Wext_k = M_k. r_k = Text_k - Text_{k+1}, c_k = Wext_k - Text_{k+1}.
The identity boundary k=0 MUST be Bmat_0 = reindex(I), Rmat_0 = 0 (so a banked decoder-agnostic rate
theorem `routeMCore_phiGen` and the boundary lemma hC0 = (C_0 = 1) survive untouched).

THE GOAL: a FULL-RANK decoder B_det M whose chart phi = phiGen(u, B_det M x) has:
  - RATE  routeMCore(phi x) = (x_p)^2 * U  (FREE: banked routeMCore_phiGen at B_det, re-check only hC0);
  - DET   |det D phi| = |x_p|^{minAdm-1} * spectators, via a radial pivotBlowupOn on `active.card = minAdm` coords.

THE EARLIER BUG (D1): the prior decoder had Rfin_L = 0 (dead leaf) -> det IDENTICALLY ZERO. The fix: Rfin_L
nonzero (LIVE leaf) + a designated FIXED-1 pivot residual entry that u scales.

TWO CONCRETE BANKED ANCHORS (the FACTS your formula must reproduce):
- B_det222 (M=(2,2,2), tach=(2,1,0), Text=[2,2,1], Wext=[2,2,2], minAdm=3):
   Bmat_0=I_2; Bmat_1=[x4;x5] (2x1); Nblk_1=[x1]; Wblk_1=[x2,x3]; Rmat_1=[[0,0],[0,x6]] (E-block 1x1=x6);
   Rfin_2=[1, x7] (1x2): entry (0,0)=FIXED 1 (the pivot, scaled by u=x0), (0,1)=x7.
   ACTIVE = {pivot at Rfin_2(0,0), x7 at Rfin_2(0,1), x6 at Rmat_1 E} -> card 3 = minAdm.
- B_det3333 (M=(3,3,3,3), tach=(3,2,1,0), Text=[3,3,2,1], Wext=[3,3,3,3], minAdm=6):
   Bmat_0=I_3; Bmat_1 (3x2); Bmat_2=[x9; x10*x9] (2x1); Nblk_1=[x7;x8]; Nblk_2=[x11,x12];
   Wblk_1=[x15,x16,x17]; Wblk_2 (2x3); Rmat_1 = e_{22} (3x3, bottom-right (2,2)=FIXED 1, the pivot);
   Rmat_2=[[0,0,0],[0,x13,x14]] (E-block 1x2=x13,x14); Rfin_3=[x24,x25,x26] (1x3, all active).
   ACTIVE = {pivot at Rmat_1 E(2,2), x13,x14 at Rmat_2 E, x24,x25,x26 at Rfin_3} -> card 6 = minAdm.

THE EXTRACTED PARAMETRIC PATTERN (verify it):
- The minAdm active residual normals = the per-boundary E-blocks: for interior k=1..L-1 the Rmat_k bottom-
  right r_k x c_k block, PLUS the leaf Rfin_L (Text_L x Wext_L). Total = (sum_{k=1}^{L-1} r_k c_k) + Text_L*Wext_L.
  This equals minAdm (verified: 222->1+2=3; 3333->1+2+3=6; 221->1+1=2; 334->4+4=8).
- The FIXED-1 pivot sits in ONE chosen E-block entry (222: leaf Rfin_2(0,0); 3333: interior Rmat_1(2,2)).
- Bmat_k carries the Schur K-frame [K ; X*K]; Nblk_k, Wblk_k carry the chaining/lift coords (NON-active spectators);
  the angular coords (x_p * angular) are the non-pivot active E-entries.

QUESTIONS:
1. Is the parametric pattern CORRECT and does it SPECIALIZE to both anchors (222 leaf-pivot, 3333 interior-pivot)?
   The pivot location DIFFERS between the two (leaf vs interior). Is there a CANONICAL uniform choice (e.g.
   "the first nonempty E-block, top-left entry" or "always the leaf Rfin_L(0,0)") that reproduces a VALID chart
   for both, or must the pivot location be a free choice per M? Does the choice affect the det |x_p|^{minAdm-1}
   (it should NOT — only active.card matters)?
2. The `minAdm <= flatDim` (= sum_k M_k M_{k+1} = the ambient dim N) question: is it needed to define
   `active : Finset (Fin N)` with active.card = minAdm? (active is a subset of the N flat coords.) Confirm
   minAdm <= N always (the active normals are a subset of the residual coords, which are a subset of all N).
3. The PARAMETRIC NONZERO-UNIT witness: the rate gives F = x_p^2 * VvalGen, and the node bundle needs
   VvalGen > 0 a.e. + bounded (Ubound/Umeas). The anchors proved this via an explicit nonzero MvPolynomial
   (UPoly222_ne_zero) + zero-set-nullity. For the PARAMETRIC B_det M, is "VvalGen is a nonzero polynomial in x"
   provable uniformly, or does each M need its own witness point? (VvalGen = ||H||^2 where prod = u*H, H the
   telescoped quotient.) Is there a uniform witness — e.g. the point where all Bmat_k = canonical full-rank,
   all angular coords = 0, the fixed-1 pivot giving H != 0? Sketch the uniform nonzero-VvalGen argument or
   flag it as the genuine per-M residual.
4. KILL-FLAG: is any sub-piece (the parametric B_det, the active Finset, the nonzero-VvalGen) a genuine
   RESEARCH wall (not just substantial dependent-width engineering)? Be sharp.
</task>

<output_contract>
- Q1: confirm/refute the pattern + specialization to both anchors; the canonical pivot choice; det-invariance. FACT vs INFERENCE.
- Q2: confirm minAdm <= N, with the subset argument.
- Q3: a sketch of the uniform nonzero-VvalGen witness OR a sharp flag that it's per-M.
- Q4: a clear yes/no on whether any sub-piece is a research wall.
</output_contract>

<grounding_rules>
- Reason about the ABSTRACT construction; do NOT explore any repository.
- The two anchor decoders + the extracted pattern + (active.card = minAdm = sum r_k c_k + Text_L Wext_L) are FACTS.
- Be decisive; if the nonzero-unit witness is the one genuine per-M residual, say so.
</grounding_rules>
