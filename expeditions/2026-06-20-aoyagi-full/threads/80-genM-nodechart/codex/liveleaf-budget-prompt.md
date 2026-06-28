<task>
Lean 4 + Mathlib, DLN RLCT formalisation. I must build a general-M (opaque-width) "LIVE-leaf" achiever
chart decoder for an interior-node determinant route, and I need a decorrelated check on the cleanest
construction + the budget identity. Facts (verified by reading code):

THE FLAT COORD BUDGET (fixed, opaque-width): the chart's free coords are `Fin N`, N = routeMAmbient M =
flatDim M. There's a bijection `chartIdxEquiv : Fin N ≃ ChartIdx M t`, where
  ChartIdx = Σ k : Fin L, Fin(schurDim k) ⊕ Fin(liftDim k),
  schurDim k = t_k · Wext(k+1)  [the per-boundary Schur frame K/X/N/E roles],
  liftDim k  = (k+1<L) ? (Wext(k+1) − t(k+1))·Wext(k+2) : 0  [chain lift; 0 at the leaf].
card(ChartIdx) = flatDim = N EXACTLY. So the budget is ENTIRELY consumed by per-boundary schur+lift; there
is NO separate slot for a leaf `Rfin` block. (chartIdxEquiv is Classical/Fintype.equivFin, not rfl.)

TWO DECODERS (both produce a GenBlk M t = {Bmat, Nblk, Wblk, Rmat per boundary, Rfin at leaf}; the chart is
phiGen u B = paramsEquivFlat (chartParamsGen u B); the chain has C_k = Bmat_k·chainQ(N_k) + u·Rmat_k
interior, C_L = u·Rfin leaf; A_k = chainA(N_k, W_k, C(k+1))):

- DEAD-leaf `genBlkFlatStruct` (what the banked rate + interior witness use): reads K/X/N/E via the frame
  slot, W via the lift slot; Rmat(k+1) = rmatPad(readE) [the E-block FREE], Rfin := 0. So the u-carriers are
  the interior free E-blocks. Its unit can ≡ 0 (e.g. L=1).
- LIVE-leaf `B_det` (the (3,3,3,3) worked instance B_det3333, and the radial-separability cert's model):
  Rmat_1 = e_{last} [a FIXED 0/1 pivot, NOT free], Rmat_2 has some free entries, Rfin_L = free leaf block.
  Hand-built with literal Fin-27 indices; its monomial det |u0|^5·|u1|^4·|u4|^2·|u9|^3 is verified.

THE PROBLEM: the radial-separability cert (det = u^{minAdm−1}·(u-free)) + the verified monomial are for the
LIVE-leaf decoder. The cert's budget identity is "#angular = minAdm−1 free R/Rfin entries, one pivot fixed =
the u-direction, square chart". But the live-leaf needs a FREE Rfin block, and the flatDim budget has no slot
for it — the live-leaf B_det3333 reuses Fin-27 coords in a bespoke layout that does NOT match
genBlkFlatStruct's reader slots.

minAdm is the layer-peeling Aoyagi recursion (NOT ∑ r_k c_k); the per-boundary E-block dims are
(Text k − Text(k+1))(Wext k − Text(k+1)), summing to LESS than minAdm in general (at 3333: 0+1+2=3 vs
minAdm=6). So the "angular = E-blocks" (dead) and "angular = Rfin + some Rmat" (live) layouts give DIFFERENT
free-coord counts, and only one can equal minAdm−1 within the flatDim budget.
</task>

<output_contract>
Answer in 4 short sections:

1. THE BUDGET RECONCILIATION: with card(ChartIdx)=flatDim EXACTLY consumed by schur+lift slots (no Rfin
   slot), HOW does a live-leaf decoder with a FREE Rfin block fit the budget? Options: (a) the leaf
   boundary's schur-slot E-block coords are RE-ROUTED to feed Rfin (the leaf E-block IS the Rfin home);
   (b) flatDim genuinely doesn't budget a free Rfin and the live-leaf needs a DIFFERENT coord count
   (so it's NOT a chart on the same Fin N). Which is correct, and does #angular = minAdm−1 hold for the
   live-leaf within flatDim? Flag if the live-leaf chart is simply NOT square on Fin N=flatDim.

2. Given the difficulty, RANK two construction routes for the general-M live-leaf decoder:
   (A) Build genBlkFlatLive : GenBlk M t reusing genBlkFlatStruct's readers but routing the LEAF boundary's
       E/lift slots to a free Rfin + fixing the interior Rmat pivots (a re-routing of the SAME chartIdxEquiv
       slots). Cost: the re-routing + re-deriving the rate (decoder-agnostic, cheap) + the witness.
   (B) Keep the DEAD-leaf decoder and instead PROVE the radial-separability + budget DIRECTLY for the
       dead-leaf (the interior E-blocks as angular), NOT relying on the live-leaf cert. The radial math
       (affine-in-u, unipotent chainA shear) is decoder-INDEPENDENT (it only needs C linear in u + chainA
       affine, true for ANY GenBlk). So does the dead-leaf ALSO satisfy det = u^{minAdm−1}·(u-free), just
       with a DIFFERENT angular layout (E-blocks not Rfin)? If the radial math is decoder-agnostic, the cert's
       MECHANISM transfers; only the budget count (#angular = minAdm−1) must be re-checked for the dead-leaf.
   Which is less work + less risk?

3. THE DECODER-AGNOSTIC RADIAL MECHANISM: the cert's structural argument (Phi affine in u, angular columns
   carry factor u, chainA unipotent shear det-preserving) — does it depend on Rfin being free vs the E-blocks
   being free, or ONLY on "C is linear in u and the free u-scaled directions are independent"? If the latter,
   the dead-leaf (E-blocks u-scaled via u·rmatPad(readE)) gets det = u^q·(u-free) too, with q = #independent
   u-scaled free directions. Is q = minAdm−1 for the dead-leaf, or does the dead-leaf q differ (making the
   threshold wrong)?

4. RECOMMENDATION: which decoder to build the det-route on, given (i) the rate + witness are banked for the
   dead-leaf, (ii) the cert is stated for the live-leaf, (iii) the flatDim budget. Is the cleanest path
   actually to PROVE the dead-leaf radial-separability directly (route B), sidestepping the live-leaf
   reconstruction entirely?
</output_contract>

<grounding_rules>
Only my summary. Mark unstated-fact dependencies "ASSUMPTION: …". Distinguish "follows from your summary"
vs "verify X". No Lean >5 lines.
</grounding_rules>
