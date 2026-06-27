<task>
Decorrelated design review of a Lean-proof DECOMPOSITION (not asking for a proof — asking whether my
sub-lemma breakdown is COMPLETE and correctly ordered, and which step is the real risk). Re-derive the
dependency structure independently; tell me what I've mis-scoped.
</task>

<setting>
Deep linear net, L layers (L≥2), widths H, target rank r. Deepest point = a rank-r block-normal chain.
A gauge chart `split : flat-params ≃ DeepestSplit = (reg) × (core × spec)`. There is a per-layer frame
family (P_s, Q_s) carrying the deepest layer to the block-normal corner (`P_s · deepestPoint_s · Q_s =
corM`, banked as `deepestPoint_frame_normal`).

GOAL (a single theorem body, `framedParams_split_eq_frame_raw`): produce constant endpoint frames
P0, QL (+ inverses) and a neighborhood U of the deepest point s.t. for w ∈ U, with blocks P00,P01,P10,P11
from the conjugated loss:
  (a) reindex(P0·(prod(paramsSymm w) − B)·QL) = fromBlocks (P00−1) P01 P10 P11      [hconj]
  (b) ∑(E_full(split w))² = ∑(P00−1)² + ∑P01² + ∑P10²   (Sreg)                       [reg-energy identity]
  (c) ∑(P10·P00⁻¹·P01)² ≤ t²·Sreg                                                    [leak bound]
  (d,e) core comparability: ∑(P11 − P10 P00⁻¹ P01)² ≍ deepestCoreF(coreAbsorb(split w))  [γ₁,γ₂]
where E_full(split w) = the reg blocks (packed by a bijection regResidualPack) of
reindex(prod(framedParamsPivot(split w))), and framedParamsPivot is the per-layer reconstruction
`framedLayer_s = corM + P_s·reindex(fromBlocks readX_s readY_s readZ_s T_s)·Q_s`.
</setting>

<banked_atoms_available>
1. reindex_fromBlocks_reads_eq_deviation: reindex(fromBlocks readX readY readZ readT)(deepestSplit w)
   = ((paramsEquivFlat).symm (w − wstar)) s   — ENTRY-WISE, THRESHOLD split on BOTH row & column sides.
2. deepestPoint_frame_normal: P_s · deepestPoint_s · Q_s = corM.
3. endpoint_telescoping: if C_s = P_s·A_s·Q_s and all INTERIOR interfaces collapse (Q_s=1 ∧ P_{s+1}=1
   for (s)+1<L), then prod C = P0 · prod A · QL, with P0 = P_first, QL = Q_last.
4. deepestPoint_frame_Qf_eq_one / _Pf_eq_one (boundary), deepestPoint_interior_frame_id (interior, L≥3).
5. exists_deepest_lastLayer_pivotFrame: ∃ J,Q: reindex(rThr, pivotThr J)(deepestPoint_last · Q) =
   fromBlocks 1 0 0 0, with the (2,2) block a unit.
6. core_comparability_squeeze: from P11 = leak + Rcore entrywise + ∑leak² ≤ t²∑E², get the two-sided
   ∑E²+‖Rcore‖² ≍ ∑E²+‖P11‖².
7. fullProduct_core_split: the Frobenius block split + P11 = (P10 P00⁻¹ P01) + (P11 − P10 P00⁻¹ P01).
8. regResidualPack: a bijection Fin nReg ≃ (the three reg block index types).
9. pivotThresholdSplit_symm_inl/inr: the pivot column-split inverse decode.
NOTE atom 1 (reindex_fromBlocks_reads_eq_deviation) uses rThresholdSplit on the COLUMN side; but
framedParamsPivot's LAST layer uses pivotThresholdSplit (pivotJSucc J) on the column side instead.
</banked_atoms_available>

<my_proposed_decomposition>
S1 (per-layer round-trip): framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s.
   = framedLayer = corM + P_s·reindex(fromBlocks reads)·Q_s; corM = P_s·deepestPoint_s·Q_s (atom 2);
     reindex(fromBlocks reads) = (paramsSymm w − deepestPoint)_s (atom 1); so framedLayer =
     P_s·deepestPoint_s·Q_s + P_s·(paramsSymm w − deepestPoint)_s·Q_s = P_s·(paramsSymm w)_s·Q_s.
   NON-last layers only (last layer has the pivot column split — see S1').
S1' (last-layer pivot variant): the SAME identity but the column reindex is pivotThresholdSplit, so
   atom 1 must be re-proved with pivot column split. (THE FLAGGED RISK.)
S2 (telescope): prod(framedParams(split w)) = P0·prod(paramsSymm w)·QL (atom 3 + 4).
S3 (B-normalize): reindex(P0·B·QL) = fromBlocks 1 0 0 0 (atom 5), same J. So
   reindex(P0·(prod(paramsSymm w) − B)·QL) = fromBlocks (P00−1) P01 P10 P11 [= hconj, conjunct (a)].
S4 (reg-energy identity (b)): ∑(E_full(split w))² = Sreg. E_full reads the reg blocks of
   reindex(prod(framedParamsPivot(split w))) = (by S2) reindex(P0·prod(paramsSymm w)·QL) = (S3) the SAME
   P00,P01,P10 blocks as hconj. So packing by regResidualPack (atom 8) gives the energy = Sreg.
S5 (leak (c) + core (d,e)): fullProduct_core_split (atom 7) + core_comparability_squeeze (atom 6) +
   the per-layer Schur ↔ global Schur ideal membership for the core comparability.
</my_proposed_decomposition>

<questions>
1. Is the decomposition S1–S5 COMPLETE for conjuncts (a)–(e)? What's missing or mis-ordered?
2. S1' (last-layer pivot column variant of atom 1): is this genuinely a SEPARATE lemma, or does atom 1
   transfer by a column-relabel? The pivot split is rThresholdSplit precomposed with a column PERMUTATION
   (pivot columns to front). Does the entry-wise decode survive the permutation, or is it a fresh proof?
3. The endpoint frames: S2 needs P0=P_first, QL=Q_last CONSTANT (independent of w). They ARE (the frame
   is the deepest-point frame, w-independent). But S3 needs the SAME J/Q as exists_deepest_lastLayer_
   pivotFrame, and S1/S2 use the deepest-point frame's last-layer Q. Is there a consistency obligation
   that the deepest-point frame's last-layer arm EQUALS the pivot frame Q from atom 5? (i.e. are the two
   frame sources reconciled, or is that an open gap?)
4. Which single step is the genuine exact-algebra / highest-risk one? My guess: S1' (the pivot decode).
</questions>

<output_contract>
Per question: VERDICT + reasoning. Mark exact-algebra vs structural inference. Flag any missing
sub-lemma or hidden consistency obligation I omitted (esp. the frame-source reconciliation in Q3).
End with: "The highest-risk step is ___ because ___; the decomposition is [COMPLETE / missing ___]."
</output_contract>

<grounding_rules>
Reason about the dependency structure + the matrix algebra. Distinguish a genuine new lemma from a
relabel of a banked one. If a consistency obligation between two frame sources is unstated, name it.
</grounding_rules>
