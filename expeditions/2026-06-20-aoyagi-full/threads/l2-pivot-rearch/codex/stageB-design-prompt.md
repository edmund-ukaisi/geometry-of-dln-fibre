<task>
Lean 4 + Mathlib v4.29 formalisation. I am migrating a coupled set of lemmas to discharge a `sorry`
("PIN1") in a deep-linear-network RLCT proof. I need a DECORRELATED design read on the cleanest
Stage-B migration path and whether a sub-staging green-banks something, BEFORE I sink a multi-hundred-
line coupled edit. Diagnosis is what I want; do not write Lean proofs.

## The objects (all real, already in the repo, types verbatim)

`deepestEPivot H r hr hL Pf Qf : (Fin nReg → ℝ) × (Fin nGauge → ℝ) → (Fin nReg → ℝ)` is defined as:

    fun p =>
      let P := reindex (rThresholdSplit r (H 0)) (rThresholdSplit r (H (Fin.last L)))
                 (prod H (framedParamsReg H r hr hL Pf Qf p))
      fun i => match regResidualPack H r hr i with
        | inl (a,b)       => (P.toBlocks₁₁ - 1) a b      -- the (r×r) P11−I block
        | inr (inl (a,b)) => P.toBlocks₁₂ a b            -- the (r × (Hlast−r)) P12 block
        | inr (inr (a,b)) => P.toBlocks₂₁ a b            -- the ((H0−r) × r) P21 block

`rThresholdSplit r a : Fin a ≃ Fin r ⊕ Fin (a−r)` sends the FIRST r indices left.
`pivotThresholdSplit r a J : Fin a ≃ Fin r ⊕ Fin (a−r)` sends the r PIVOT columns (Set.range J,
sorted) left.

## What is proven (bedrock, sorry-free, axiom-clean)

1. STAGE A (just landed): `deepestPoint_frame_pivot_exists` produces the whole per-layer frame family
   (P_s, Q_s): first/interior arms = the existing `deepestPoint_frame` (carry to threshold corner corM),
   last-layer arm = a B-determined pivot Q, with:
     - IsUnit(P_s), IsUnit(Q_s); Q(first)=1, P(last)=1;
     - first/interior: P_s · deepestPoint_s · Q_s = corM (threshold);
     - LAST layer: reindex (rThresholdSplit r Hlast.castSucc) (pivotThresholdSplit r Hlast.succ J)
       (deepestPoint_last · Q_last) = fromBlocks 1 0 0 0  (the PIVOT corner);
     - IsUnit ((reindex (pivotThresholdSplit r Hlast.succ J)² (Q_last)).toBlocks₂₂)   [= 1, B22 unit].

2. `prod_regSlice_collapse` (sorry-free): prod(framedParamsReg (r0,0)) = firstShapeF (last).castSucc ·
   framedParamsReg (r0,0) last.  firstShapeF = corM + Pf_first · reindex(fromBlocks readX 0 readZ 0) ·
   Qf_first riding on the corner.

3. `framedParamsReg_regSlice_last` (sorry-free): framedParamsReg (r0,0) last =
   reindex (rThresholdSplit Hlast.castSucc).symm (rThresholdSplit Hlast.succ).symm (fromBlocks 1 0 0 0)
   + Pf_last · reindex(...).symm (rThresholdSplit Hlast.succ).symm (fromBlocks 0 readY 0 0) · Qf_last.

4. `devXZ_corner_devY` (sorry-free): the cross term reindex(X 0 Z 0)·corM·reindex(0 Y 0 0) =
   reindex(0 (X·Y) 0 (Z·Y)); each entry quadratic in r0, strict deriv 0 at 0.

5. `regBlockCLE e0 A B21 B22 (hA:IsUnit A) (hB22:IsUnit B22) : (Y×(X×Z)) ≃L (Y×(X×Z))` realises
   (Y,(X,Z)) ↦ (Y·B22, (A11 X+A12 Z + Y·B21, A21 X+A22 Z)); block-triangular; invertible.

6. `regStraightenTotalCLM_equiv_of_regBlock_isUnit` (sorry-free): from F:R≃L R with ↑F = D_E.comp regInCLM,
   builds the invertible total shear. This is the FINAL consumer of PIN1.

PIN1 (the sorry) is `deepestEPivot_regSlice_fderiv`: ∃ F : (Fin nReg→ℝ) ≃L (Fin nReg→ℝ),
HasStrictFDerivAt (fun r0 => deepestEPivot Pf Qf (r0,0)) F 0. PROVEN-FALSE from IsUnit(Pf first)/
IsUnit(Qf last) ALONE (the P12 = Y·B22 block needs B22 invertible, which a unit Qf last need not have
when B's pivots are not front). The fix is to migrate `deepestEPivot`'s LAST-LAYER codomain split from
rThresholdSplit to pivotThresholdSplit J (last-layer-only; first/interior keep rThresholdSplit), then
discharge B22-invertible from Stage A's pivot corner.

## The coupling (the hard part)

Migrating `deepestEPivot`'s last-layer column split to pivotThresholdSplit J breaks:
  (a) `deepestEPivot_base` (deepestEPivot 0 = 0): its proof uses `prodAux_framedParamsReg_zero`, which
      lands the rThreshold corner FRAME-INDEPENDENTLY (the origin product is the corner regardless of
      frame). With a pivot column split the outer reindex no longer cancels to fromBlocks 1 0 0 0 in the
      same way.
  (b) `deepestEPivot_sq_sum_eq_blocks`: RHS blocks become the pivot reindex.
  (c) PIN2 `framedParams_split_eq_frame_raw` consumed by `deepest_loss_squeeze`: identifies Sreg (built
      from P00/P01/P10 via h00/h01/h10, all rThresholdSplit) with ∑(regStraighten).1². The `rw [h00,h01,h10]`
      typechecks ONLY if deepestEPivot's blocks use the SAME split as PIN2's P00/P01/P10. So PIN2 must
      migrate its last-layer column split to pivotThresholdSplit J with the SAME J.

J is B-determined; the SAME J must thread from the call site (deepest_gauge_construction) into BOTH
deepestEPivot (via Pf/Qf and an extra J arg) AND framedParams_split_eq_frame_raw.

## Specific questions

1. Is `deepestEPivot` better re-parametrised by adding an explicit `(J : Fin r ↪ Fin (H (Fin.last L)))`
   argument and using `pivotThresholdSplit r (H (Fin.last L)) J` for the column split (last-layer-only),
   OR is there a cleaner factoring (e.g. keep deepestEPivot on rThresholdSplit but post-compose a
   B-determined column permutation σ on the P12 block only)? Which minimises the PIN2 coupling?

2. For `deepestEPivot_base` (deepestEPivot 0 = 0): with the pivot column split, does the origin product
   still read 0 in all three residual blocks? The origin product is the rThreshold corner fromBlocks
   1 0 0 0 (frame-independent). Under pivotThresholdSplit J the (r×r) leading block is the pivots, the
   off-diagonal blocks are 0. Is `deepestEPivot 0 = 0` still TRUE with the pivot split, and what is the
   cleanest discharge (does the pivot corner of fromBlocks 1 0 0 0 stay 0 off the P11 diagonal)?
   CRITICAL: is there a soundness trap where deepestEPivot_base becomes FALSE (so the migration is
   unsound), or does it stay true?

3. Can the migration be SUB-STAGED so that something green-banks independently of the full PIN1 landing?
   E.g. (i) prove the value-fold matrix identity `deepestEPivot (r0,0) = (regBlockCLE-shaped linear) +
   (quadratic, deriv 0)` as a standalone lemma on ARBITRARY Pf/Qf/J with hQf22 as a hypothesis (no
   migration of base/sq_sum/PIN2 yet); (ii) the strict-derivative wrapper; THEN (iii) the coupled
   migration of base/sq_sum/PIN2. Which sub-lemmas are GREEN-BANKABLE on their own (additive, no red
   span) vs which force the coupled red span?

4. The brief says "twist only the final read" (L2) is UNSOUND (yields Y·(reindex rThreshold eJ Q)₂₂,
   not the certified Y·(reindex eJ eJ Q)₂₂), and the correct move (L1) is: the last layer's .succ-side
   reindex AND deepestEPivot's final-read codomain split BOTH use eLast := pivotThresholdSplit J. Is this
   the right read? Concretely, in `framedParamsReg_regSlice_last` the last layer is built with
   `reindex (rThresholdSplit Hlast.castSucc).symm (rThresholdSplit Hlast.succ).symm (...)`. Does L1
   require also changing THIS lemma's .succ-side reindex to pivotThresholdSplit J, or only the OUTER
   reindex in deepestEPivot's `P`? Explain which reindex must change for the discriminating identity
   `(reindex eR eJ ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0 0)) * Q)).toBlocks₁₂ = Y · (reindex eJ eJ Q)₂₂`
   to fire.
</task>

<output_contract>
Five sections, terse:
1. RECOMMENDED FACTORING (Q1): the cleanest re-parametrisation of deepestEPivot + the minimal PIN2 touch.
2. deepestEPivot_base SOUNDNESS (Q2): TRUE or FALSE under pivot split + the cleanest discharge or the
   soundness trap. This is the gate — be definitive.
3. SUB-STAGING (Q3): a numbered list, each item flagged GREEN-BANKABLE (additive) or RED-SPAN (coupled),
   in dependency order. Identify the largest green-bankable prefix.
4. L1-vs-L2 + WHICH REINDEX (Q4): which reindex(es) must migrate to pivotThresholdSplit J for the
   discriminating identity to fire; confirm or correct the L1 read.
5. SINGLE CHEAPEST DISCRIMINATING CHECK before committing to the full coupled red span.
</output_contract>

<grounding_rules>
Flag inference vs. fact explicitly. You do NOT have the repo; reason from the types and statements given
above. If a claim depends on a Mathlib lemma you are not sure exists at v4.29, say so. Do not invent
lemma names as if confirmed. If question 2's soundness cannot be settled from the given info, say what
single fact would settle it.
</grounding_rules>
