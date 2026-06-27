<task>
MATH adjudication for a Lean RLCT formalisation: does a frame conjugation preserve the Schur-core
identification needed to close a producer? Reason from the stated algebra. Concise (<500 words). This
blocks a build — be decisive and honest if there's a real extra obligation.
</task>

<setting>
L=2 deep-linear-net gauge chart. Per-layer FRAMED reconstruction F_s = Pf_s · (raw layer A_s) · Qf_s
(Pf_s, Qf_s general invertible gauge frames). The telescoped framed product:
  prod F = P0 · prod(A) · QL,  P0 = Pf_0 (left, on H0), QL = Qf_1 (right, on H_last), general units.
The producer's Rcore is the GLOBAL Schur complement (wrt the r⊕M block split, front pivot rThr) of
  Mw := reindex(rThr, rThr)( P0 · (prod(A) − B) · QL )   [the FRAMED, conjugated loss product].
A banked LDU lemma `schur_product_ldu` gives, FRAME-FREE: Schur(reindex(C0·C1)) = S'_0·(1−K)·S'_1 with
the FRAME-FREE per-layer Schur cores S'_s = T_s − Z_s·A_s⁻¹·Y_s (A_s,Y_s,Z_s,T_s = the rThr-blocks of
the RAW layer (A)_s). A banked core functional coreΦ = frobSq(S'_0·S'_1) uses these SAME frame-free cores.

ESTABLISHED (numeric): the global Schur is NOT invariant under conjugation by general units P0,QL — even
block-DIAGONAL P0,QL break it (M11⁻¹ doesn't commute), max|Schur(P0 N QL)−Schur(N)| ≫ 0.

So Rcore (Schur of the FRAMED Mw) ≠ S'_0(1−K)S'_1 (the FRAME-FREE Schur) in general — UNLESS the frames
are stripped first or have special structure.
</setting>

<questions>
1. Is the producer's Rcore (Schur of the FRAMED Mw) actually what the loss squeeze needs, or does the
   loss two-sided bound (`dlnLoss_two_sided_of_frame`) ALREADY absorb the frames P0,QL into its CONSTANTS
   (the endpoint-frame energies KP, Ki) — so the squeeze compares dlnLoss to frobSq of the FRAME-FREE
   product blocks, and Rcore should be the FRAME-FREE Schur (of reindex(prod(A)−B)), NOT the framed Mw?
   If so, h2 is CLEAN: apply the LDU to the frame-free prod(A), the cores are S'_s by construction, and
   P0,QL never enter the Schur (they're in the leaf-lemma constants).
2. OR: is Rcore genuinely the FRAMED Schur, and h2 needs an explicit frame-cancellation argument? If so,
   what is its structure — do P0,QL preserve the r-block FILTRATION (front pivot: the first r columns of
   B·... are the pivots) so that, while not Schur-invariant pointwise, the Schur is invariant up to a
   BOUNDED-similarity that folds into the germ charge's constant C?
3. The deepest-point structure: at front pivot, P0 maps the deepest layer-0 to the corner; does P0
   preserve the r⊕M split (block-triangular) BECAUSE the deepest point's layer-0 has the rank-r structure
   (last M columns vanish)? i.e. is Pf_0 block-LOWER-triangular (so it's a valid Schur-preserving
   unipotent-class strip after all), even though a GENERIC unit isn't? Check the deepest-frame structure.
4. NET: is h2 CLEAN (Rcore is frame-free by the leaf-lemma absorbing P0/QL, OR the frames are
   block-triangular Schur-preservers), or is there a REAL unbuilt frame-cancellation obligation? If real,
   estimate it.
</questions>

<output_contract>
1. Does the leaf lemma absorb P0/QL (⇒ Rcore frame-free)? 2. If not, frame-cancellation structure. 3.
   Are the deepest-point frames block-triangular (Schur-preserving)? 4. NET: h2 CLEAN or real extra
   obligation + estimate. Mark exact vs inference. End: "h2 is [CLEAN via ___ / has a REAL frame obligation: ___]."
</output_contract>
