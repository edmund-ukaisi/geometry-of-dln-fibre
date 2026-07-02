<task>
Lean 4 + Mathlib formalisation design review. I close the general-L deepRank=0 interior box-divergence atom in a DLN-fibre RLCT project.

DONE sorry-free (module RouteMInteriorDeepRank0Gen): eDeepRank0PhiGen (chart), eDeepRank0UnitGen := fun x => VvalGen (x p0) M (tach M) (genBlkFlatEfpGen k (kLDU x)) hle, eDeepRank0_abs_detGen, eDeepRank0_diffGen, routeMCore_eDeepRank0PhiGen (rate), eDeepRank0PhiGen_factor. Here p0 = eBlockPivotGen k (an interior E-active slot at boundary k, with k.val ≠ L-1), and genBlkFlatEfpGen k x is the live decoder (rfin=0) with the pivot boundary (k+1)'s Rmat overridden to rmatPad (EfixedReaderGen k x); EfixedReaderGen k x pins the E (0,0)-entry to 1 and reads readE x ⟨k⟩ elsewhere.

To assemble the atom I need FIVE analytic facts for eDeepRank0UnitGen: (1) continuity, (2) measurability, (3) image_subset, (4) box-bound, (5) ae-positivity.

Analogues are proven in two places:
- LEAF-pivot general-L (RouteMInteriorLiveGenAnalytic): continuity via genBlkContinuous_liveGen + continuous_Hmat0_gen + VvalGen_eq_sqSumHmat0; ae-pos via a named nonzero MvPolynomial UPolyLiveGen (sqSumHmat0 of the poly live-decoder chain over kLDUGen(Xvec)), eval_UPolyLiveGen, and interiorLiveUnitGen_wInt_ne_zero (nonzero at interior-drop witness wInt M ha p) + MvPolynomial.ae_eval_ne_zero.
- L=2 deepRank=0 (RouteMInteriorDeepRank0 + RouteMInteriorDeepRank0AePos): same pattern, CommRing-generic genBlkFlatEfpGen poly decoder + UPolyEfp + eDeepRank0Unit_wInt_ne_zero at witness wInt M ha 1.

KEY QUESTION on ae-pos (5) at general L for the E-fixed chart. The L=2 route uses witness wInt M ha 1 where the Efp decoder COLLAPSES to plain genBlkFlatLive ha 0 (wInt 1), because at p=1 readE(wInt 1)⟨0⟩ = EfixedReader(wInt 1) (both the (0,0)-pivot indicator). At general L my E-pivot sits at ARBITRARY interior boundary k (k.val ≠ L-1). wInt M ha p is parameterized by pivot p. kLDU fixes wInt (kLDU_wIntGen), so eDeepRank0UnitGen(wInt) = VvalGen(...)(genBlkFlatEfpGen k (wInt)). I want to choose witness p = k+1 (the pivot boundary), so readE(wInt(k+1))⟨k⟩ = EfixedReaderGen k (wInt(k+1)) (both the (0,0) indicator at that boundary), forcing genBlkFlatEfpGen k (wInt(k+1)) = genBlkFlatLive ha 0 (wInt(k+1)), then reuse the survival machinery Hmat_pivot/Hmat_row_thread/suffix_carrier exactly as interiorLiveUnitGen_wInt_ne_zero.

InteriorDrop M gives SOME interior pivot p*, but my k is fixed by the deepRank=0 chart choice. eBlockPivotGen exists because chart hyps hr : 0 < Text(k+1) - Text(k+2) and hc : 0 < Wext(k+1) - Text(k+2) hold; also deepRank=0 means Text L = 0; and InteriorDrop M holds.

Assess:
(A) Is the cleanest ae-pos route "witness at p = k+1 forces Efp collapse to the live decoder, then reuse the general-L survival machinery"? Or is there a subtlety because the survival machinery interiorLiveUnitGen_wInt_ne_zero needs the full descent chain of row/col drops for ALL boundaries from p to L, not just at k+1?
(B) Are the drop conditions needed for wInt M ha (k+1) to be a valid nonzero-survival witness — namely 1 ≤ k+1, k+1 < L, row drop Text(k+2)<Text(k+1), tail col drops Text(b+1)<Wext b for k+1 ≤ b < L, and leaf Wext L > 0 — all DERIVABLE from {chart hr, hc; Text L = 0; InteriorDrop M; k.val ≠ L-1}? In particular: hr gives the row drop at k+1. hc gives ONE col drop at k+1. But the tail col drops for b > k+1 up to L-1 are NOT obviously implied by hr/hc. Does InteriorDrop M supply a monotone descent that gives them, or could a deepRank=0 interior config have Text(b+1) ≥ Wext b for some k+1 < b < L, breaking the survival witness at pivot k+1?
(C) If (B) fails (tail col drops not guaranteed at k+1), what is the correct witness/route? E.g. keep the InteriorDrop-supplied pivot p* and prove eDeepRank0UnitGen(wInt p*) ≠ 0 WITHOUT the Efp-collapse (i.e. the Efp override at boundary k does not interfere with the surviving Hmat 0 entry threaded from pivot p* to leaf, provided the surviving entry does not read the E-block at boundary k)? Is the surviving Hmat entry E-block-blind at the overridden boundary?

Flag any soundness trap.
</task>

<output_contract>
Answer (A),(B),(C) in order, each ≤ 8 sentences. Then a 3-line RECOMMENDATION: the single cleanest witness/route to pursue, and the one lemma most likely to resist. Be concrete and Lean-oriented; distinguish what you can INFER structurally from what you'd need to CHECK against the actual definitions.
</output_contract>

<grounding_rules>
You do not have the source; reason structurally from the described lemmas. Explicitly mark each claim as (INFER) structural inference or (CHECK) needs verification against definitions. Do not fabricate lemma names beyond those I gave.
</grounding_rules>
