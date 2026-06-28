# theorem-ledger.md - source to Lean dependency ledger

This table is controller memory. Every source theorem or lemma that can affect
the final statement gets one row. Keep source references page-pinned; avoid
holding PDF line numbers only in context.

| Source item | Local claim | Source ref | Dependencies | Reproduction/status | Lean target/status | Review/status |
|---|---|---|---|---|---|---|
| Retained-passive target edge-pair raw-tuple linear equivalence package | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; equivalence package is local Lean algebra around the target edge-pair shear | target edge-pair linear map package; formal raw `(F2,C)` inverse; raw side-field projections; backward target-recovered `F2` recurrence | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-target-edge-pair-raw-tuple-equivalence.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-target-edge-pair-raw-tuple-equivalence.md` | `retainedPassiveTargetEdgePairShearRawTupleLinearMapAt`, `retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_apply`, `retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt`, `retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_apply`, `retainedPassiveFormalRawF2CLinearEquivAt_symm_targetEdgePairShearAt_fst`, `retainedPassiveTargetEdgePairShearRawTupleInverseLinearMapAt_leftInverse`, `retainedPassiveTargetRecoveredF2At_rawTupleInverse`, `retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_rightInverse`, `retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt`, `retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_apply`, and `retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build passed; `scripts/sorries`, `git diff --check`, code-only forbidden-marker search, and direct axiom audits passed with footprint `[propext, Classical.choice, Quot.sound]`; not yet a determinant-one theorem | reviewed by xhigh `Mendel the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-target-edge-pair-raw-tuple-linear-inverse.md`; PASS for inverse algebra and no-overclaim boundary; xhigh proof audit by `Pascal the 2nd` supplied the staged recurrence proof route; final equivalence review by xhigh `Gauss the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-target-edge-pair-raw-tuple-linear-equivalence.md` passed; formal inverse second component is not a raw `C` recovery for arbitrary tuples; no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive target-side all-edge `(F2,C)` linear-map package | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | existing target-recovered `F2` recurrence, successor family, and target edge-pair shear; raw edge-block readouts; finite matrix left/right multiplication linearity; `LinearEquiv.cast` for `Fin.succ_castSucc` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-target-edge-pair-linear-map.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-target-edge-pair-linear-map.md` | `retainedPassiveTargetRecoveredF2LinearMapAt`, `retainedPassiveTargetRecoveredF2LinearMapAt_apply`, `retainedPassiveTargetRecoveredSuccessorF2LinearMapAt`, `retainedPassiveTargetRecoveredSuccessorF2LinearMapAt_apply`, `retainedPassiveTargetEdgePairShearLinearMapAt`, and `retainedPassiveTargetEdgePairShearLinearMapAt_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build and full `DLNFibre` build passed; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Lovelace the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-target-edge-pair-linear-map.md`; PASS; terminal/nonterminal recurrence, successor cast/zero, and target edge-pair formula match the existing functions; no target-side `LinearEquiv`, raw-tuple normalizer, determinant theorem, measure transport, normal crossings, pole order, or RLCT |
| Generic product/shear abs-det-one wrappers | A2 target-normalizer determinant support | finite-dimensional linear algebra; local infrastructure for Aoyagi PDF pp. 11-13 coordinate algebra | existing `linearEquiv_prodCongr_det_eq_mul`, `linearEquiv_det_skewProd_toLinearMap_eq_mul`, `linearEquivUpperShear_det_eq_one`, and `abs_mul` under `[CommRing R] [LinearOrder R] [IsOrderedRing R]` | reproduced at `threads/03-block-product-reduction/reproduction-a2-generic-shear-product-abs-det-wrappers.md`; statement card `threads/03-block-product-reduction/statement-card-a2-generic-shear-product-abs-det-wrappers.md` | `linearEquiv_prodCongr_abs_det_eq_one`, `linearEquiv_skewProd_refl_refl_det_eq_one`, `linearEquiv_skewProd_refl_refl_abs_det_eq_one`, and `linearEquivUpperShear_abs_det_eq_one` proved in `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`; focused `MatrixLinearDeterminant` build passed; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Avicenna the 2nd` in `threads/03-block-product-reduction/review-a2-generic-shear-product-abs-det-wrappers.md`; PASS; product lemma has necessary factor abs-det-one hypotheses; order hypotheses match Mathlib v4.29 absolute-value API; no target normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive positive-tail `F3` bridge with target-only `dEarly` | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | existing positive-tail recursive `F3` bridge and recovery; target-only lower-left recursion; comparison theorem `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged` at `m=0` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-positive-tail-target-only-dearly.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-positive-tail-target-only-dearly.md` | `F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` and `F3_tail_pos_targetOnly_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build and full `DLNFibre` build passed; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Poincare the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-f3-positive-tail-target-only-dearly.md`; PASS; target-only call uses `(M := M)` and index `0`; rewrite orientation is target-only equals source-staged; `dLast#` and `- dEarly * solvedA1(last)` order are unchanged; no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive recursive target-only lower-left derivative and solved-`A1` suffix staging | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | target-only current solved-`A1` tangent; target-staged stored-`C` suffix and `Cnext`; existing source-staged lower-left recursion; solved-`A1` suffix product rule; positive solved/seed suffix equality for `1 <= m` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-only-lower-left-tail.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-recursive-target-only-lower-left-tail.md` | `retainedPassiveSolvedA1_residualFactorProduct_eq_A1seed_of_pos` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`; `retainedPassiveSolvedA1TargetStagedTangentAt`, `retainedPassiveSolvedA1TargetStagedTangentAt_zero`, `retainedPassiveSolvedA1TargetStagedTangentAt_succ`, `retainedPassiveSolvedA1TargetStagedTangentAt_fderiv_eq_source`, `retainedPassiveSolvedA1SuffixTargetStagedFDerivAt`, `retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_self`, `retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_step`, `retainedPassiveSolvedA1SuffixProductAt`, `fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply`, `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt`, `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_self`, `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step`, `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_zero`, `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_succ`, `retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged`, and `fderiv_retainedPassiveLowerLeftProductTailSum_targetOnly_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build and full `DLNFibre` build passed; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Meitner the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-recursive-target-only-lower-left-tail.md`; PASS; `dPsucc` starts at `p.succ.val`, `Cnext` starts at `r.succ`, terminal base is `M+1`, matrix order is preserved, and the theorem claims only derivative target-staging; no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive target-staged stored-`C` suffix derivative and `Cnext` plug-in | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | target-recovered source `C`; stored `C` residual-factor product rule; empty suffix derivative; existing target-only lower-left step core | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-target-staged-c-suffix.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-target-staged-c-suffix.md` | `retainedPassiveCTailTargetOnlyStepAt`, `retainedPassiveCTailTargetOnlyStepAt_fderiv_eq_sourceStep`, `retainedPassiveCSuffixTargetStagedFDerivAt`, `retainedPassiveCSuffixTargetStagedFDerivAt_self`, `retainedPassiveCSuffixTargetStagedFDerivAt_step`, `retainedPassiveCSuffixProductAt`, `fderiv_retainedPassive_C_residualFactorProduct_targetStaged_apply`, `retainedPassiveCnextTargetStagedFDerivAt`, `retainedPassiveCnextTargetStagedFDerivAt_fderiv_eq_source`, `retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt`, and `retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt_fderiv_eq_sourceStepCore` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build and full `DLNFibre` build passed; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Maxwell the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-target-staged-c-suffix.md`; PASS; keeps `dAcur`, `dPsucc`, and `dNext` explicit; no full target-only lower-left recurrence, determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive target-only lower-left one-step core | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | recursive target-staged `Ctop` branch; target-recovered source `(F2,C)` pair; passive `A1` target-staging; formal raw-order map identity on passive lower-left components; existing source lower-left step core | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-target-only-lower-left-step-core.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-target-only-lower-left-step-core.md` | `retainedPassiveTargetRecoveredSourceCtopAt`, `retainedPassiveTargetRecoveredSourceCtopAt_fderiv_eq_sourceCtop`, `retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt`, `retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_zero`, `retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_succ`, `retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt_fderiv_eq_source`, `retainedPassiveLowerLeftTailTargetOnlyStepCoreAt`, and `retainedPassiveLowerLeftTailTargetOnlyStepCoreAt_fderiv_eq_sourceStepCore` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build and full `DLNFibre` build passed; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Halley the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-target-only-lower-left-step-core.md`; PASS; keeps `dCnext`, `dAcur`, `dPsucc`, and `dNext` explicit; no full target-only recurrence, no target-staged `dCnext`, no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive target-recovered source `(F2,C)` pair and product determinant helper | A2 target-normalizer support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; determinant helper is finite-dimensional linear algebra | target-side normalized edge-pair shear; point-specialized formal raw `(F2,C)` linear equivalence and inverse recovery; product-map determinant lemma | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-target-recovered-source-pair-det-helper.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-target-recovered-source-pair-det-helper.md` | `linearEquiv_prodCongr_det_eq_mul` proved in `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`; `retainedPassiveTargetRecoveredSourcePairAt`, `retainedPassiveTargetRecoveredSourcePairAt_fderiv_eq_sourcePair`, `retainedPassiveTargetRecoveredSourceCAt`, and `retainedPassiveTargetRecoveredSourceCAt_fderiv_eq_sourceC` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused builds of both modules and full `DLNFibre` build passed; `scripts/sorries`, `git diff --check`, and forbidden-marker search passed | reviewed by xhigh `Epicurus the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-target-recovered-source-pair-det-helper.md`; PASS; no target normalizer, determinant equality, lower-left target-only recurrence, source-prior transport, normal crossings, pole order, or RLCT |
| Retained-passive recursive passive top-left `A1` suffix derivative and `Ctop` plug-in | A2 first top-left branch derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | passive `A1` target-staged recovery; residual-factor product suffix product rule; source-staged `Ctop` tail derivative bridge; target-recovered successor `F2`; raw `A3` readout under successor `F2`; formal raw-order `Ctop` recovery | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-a1-tail.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-recursive-a1-tail-ctop-plugin.md` | `retainedPassiveTargetStagedA1passiveTangentAt`, `retainedPassiveTargetStagedA1passiveTangentAt_fderiv_eq_source`, `retainedPassiveA1TailTargetStagedFDerivAt`, `retainedPassiveA1TailTargetStagedFDerivAt_self`, `retainedPassiveA1TailTargetStagedFDerivAt_step`, `retainedPassiveA1TailTargetStagedFDerivAt_zero`, `retainedPassiveA1seedTailProductAt`, `fderiv_retainedPassive_A1seed_residualFactorProduct_targetStaged_apply`, `fderiv_retainedPassive_A1TailAfterFirst_targetStaged_apply`, `Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`, and `Ctop_tail_recursive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build passed; full `DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Dirac the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-recursive-a1-tail-ctop-plugin.md`; PASS; recurrence has base `D_M=0` and step `D_{m+1}*A1seed(p)+P_{m+1}*targetA1(q)` with `q=<m,m<M>` and `p=q.succ`; `Ctop` correction order is `Tail^-1*dTail*Tail^-1*coord.Ctop`; no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive positive-tail `F3` recursive `dEarly` plug-in and recovery | A2 terminal `F3` derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | terminal-target-staged positive-tail `F3` bridge; actual-derivative bridge `fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply`; recursive target-staged lower-left derivative at `m=0`; formal raw-order `F3` recovery | reproduced/design-recorded at `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-recursive-dearly-plugin.md` | `F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` and `F3_tail_pos_recursive_dEarly_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build passed; full `DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`, `git diff --check`, forbidden-marker search, and direct axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Franklin the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-f3-recursive-dearly-plugin.md`; PASS; tail parameter is `M+1`, recursive derivative call uses `(M := M)` and `m=0`; `qLast.succ = Fin.last (M+1)`; recovery factor is `(-(coord.solvedA1 (Fin.last (M+1))))^-1`; no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive lower-left actual derivative equals recursive target-staged expression | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | recursive target-staged lower-left expression API; zeroed-final tail derivative; zero-current and successor-current step-core recurrence wrappers; determinant-chart solved-`A1` derivative hypotheses inherited through those wrappers | reproduced/design-recorded at `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-lower-left-target-staged-actual-derivative-bridge.md` | `fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative build passed; full `DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`, `git diff --check`, forbidden-marker search, and axiom audit passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Erdos the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-lower-left-target-staged-actual-derivative-bridge.md`; PASS; staged index is `m<=M+1` while actual tail-sum bound is widened to `m<=M+2`; base is zeroed-final `m=M+1`; successor tangent is `v.1 s.castSucc`; positive-tail `F3` plug-in is tracked in the newer row above; no determinant normalizer, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive recursive target-staged lower-left derivative expression | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | lower-left one-step core `retainedPassiveLowerLeftTailStepCoreAt`; zero solved-`A1` current target tangent; successor solved-`A1` current target tangent; `Nat.decreasingInduction` with zeroed-final base | reproduced/design-recorded at `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-recursive-target-staged-lower-left-tail.md` | `retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt`, `retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_zero`, `retainedPassiveLowerLeftTailCurrentTargetSolvedA1TangentAt_succ`, `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt`, `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_self`, `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_step`, `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_zero`, and `retainedPassiveLowerLeftProductTailTargetStagedFDerivAt_succ` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative build passed; full `DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`, `git diff --check`, and axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]`; the actual derivative equality is now a separate row above | reviewed by xhigh `Turing the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-recursive-target-staged-lower-left-tail.md`; PASS; base is `m=M+1`; successor tangent is `v.1 s.castSucc`; `dNext` is recursive successor value; expression/unfold layer only, no `F3` plug-in, no determinant normalizer, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive lower-left one-step derivative core | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | existing retained-passive lower-left derivative recurrence after `dCprod`, `dG`, and `dPcast` staging; zero solved-`A1` branch; successor solved-`A1` branch; helper keeps `dAcur`, `dPsucc`, and `dNext` explicit | reproduced/design-recorded at `threads/03-block-product-reduction/reproduction-a2-retained-passive-recursive-target-staged-lower-left-tail.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-lower-left-step-core.md` | `retainedPassiveLowerLeftTailStepCoreAt`, `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_stepCore_apply`, `fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_stepCore_apply`, and `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_stepCore_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative build passed; full `DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`, `git diff --check`, and axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Averroes the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-lower-left-step-core.md`; PASS; successor wrapper uses `v.1 s.castSucc`, not `v.1 s.succ`/`v.1 q`; no full recursive staged derivative, no determinant normalizer, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive conditional determinant/Jacobian bridge from supplied target normalizer | A2 determinant/Jacobian assembly support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; determinant bridge itself is finite-dimensional linear algebra | supplied target-side `LinearEquiv T` on the retained-passive raw tuple vector space; pointwise identity `T ((fderiv topologyTupleEdgeRawOrder z) v) = retainedPassiveFormalRawOrderJacobianAt z v`; absolute determinant hypothesis `|det T| = 1`; formal product determinant theorem `retainedPassiveFormalRawOrderJacobianAbsDetAt_eq` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-conditional-determinant-jacobian-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-conditional-determinant-jacobian-bridge.md` | `topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_of_target_linearEquiv` and `topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_of_target_linearEquiv` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build passed with no focused-module warnings; full `DLNFibre` build passed with only pre-existing warning noise; `scripts/sorries`, `git diff --check`, and theorem axiom audits passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Noether the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-conditional-determinant-jacobian-bridge.md`; PASS; no construction of `T`, no claim that componentwise sheared packaging is already determinant-one, no source-prior transport, inverse-density pushforward, normal crossings, pole order, or RLCT |
| Retained-passive three-positive-tail `F3` next-next successor substitution and recovery | A2 terminal `F3` derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | tail parameterized as `((M+1)+1)+1`; two-positive-tail `F3` theorem instantiated with `M := M+1`; successor-index dEarly theorem instantiated at `s1 := (0 : Fin (M+1)).succ`; second successor tangent is `v.1 s1.castSucc`; `dPsucc`, `dPsucc1`, `dPsucc2`, `Psucc*`, and the next recursive derivative left explicit; recovery composes the same staged equality with `retainedPassiveFormalRawOrderJacobianAt_recovers_F3` and right-multiplies by `(-(coord.solvedA1 (Fin.last (((M+1)+1)+1))))^-1` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md` | `F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` and `F3_tail_pos_pos_pos_dEarly_zero_next_succ_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build, full `DLNFibre` build, `scripts/sorries`, `git diff --check`, and theorem axiom audit passed; axiom footprint is `[propext, Classical.choice, Quot.sound]`; factor order `Cprod2 * A3p2 * Pcast2^-1 * (...) * Pcast2^-1` preserved | reviewed by xhigh `Parfit the 2nd` and xhigh `Carson the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-f3-three-positive-tail-nextnext-succ-substitution.md`; PASS; no one- or two-positive-tail claim, no `v.1 q2`, no `dPsucc*` rewrite, no terminal cleanup, no full positive-tail `F3` target staging, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive second passive `A1` target-staging inside two-positive-tail `Ctop` | A2 first top-left branch derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | two-positive tail parameterized as `(M+1)+1`; first-passive `Ctop` target-staged theorem instantiated at `M := (M+1)+1`; generic passive seed-product suffix derivative helper instantiated at `q1 := (0 : Fin (M+1)).succ`; `Psucc` starts at `p0.succ` and `Psucc1` at `p1.succ`; second tangent is `Dzv.1 q1`, not the `F3` successor `castSucc` pattern; `(fderiv Psucc1 z) v` left explicit | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md` | `Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` and `Ctop_tail_pos_pos_firstA1_nextA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build passed; full `DLNFibre` build passed with only pre-existing style warnings; `scripts/sorries` and `git diff --check` passed; axiom footprint is `[propext, Classical.choice, Quot.sound]`; factor order `Tail⁻¹ * (((...) * data.A1seed p0) + ...) * Tail⁻¹ * coord.Ctop` preserved | reviewed by xhigh `Schrodinger the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-ctop-two-positive-tail-second-a1-target-staging.md`; PASS; no terminal cleanup for `M=0`, no full recursive passive suffix staging, no full `Ctop` or `F3` target staging, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive first passive `A1` target-staging inside positive-tail `Ctop` | A2 first top-left branch derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | generic passive seed-product suffix derivative product rule; target-staged passive `A1` recovery; positive-tail `Ctop` target-staged theorem; positive tail uses `q : Fin M := ⟨0,hM⟩`, `p := q.succ`, and the passive replacement uses `q.succ`, not the separate `Ctop` endpoint edge index `0 : Fin (M+1)` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-a1-tail-target-staged-first-passive.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-a1-tail-target-staged-first-passive.md` | `fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_target_staged_apply`, `fderiv_retainedPassive_A1TailAfterFirst_pos_target_staged_apply`, `Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`, and `Ctop_tail_pos_firstA1_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build passed; full `DLNFibre` build passed with only pre-existing style warnings; `scripts/sorries` and `git diff --check` passed; axiom footprint is `[propext, Classical.choice, Quot.sound]`; residual `(fderiv Psucc z) v` left explicit; factor order `Tail⁻¹ * (...) * Tail⁻¹ * coord.Ctop` preserved | reviewed by xhigh `Banach the 2nd` in `threads/03-block-product-reduction/review-a2-retained-passive-a1-tail-target-staged-first-passive.md`; PASS; no empty-suffix cleanup for `M=1`, no terminal raw lower-left zero claim, no full `Ctop` or `F3` target staging, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive two-positive-tail `F3` next-successor substitution and recovery | A2 terminal `F3` derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | tail parameterized as `(M+1)+1`; first-index `F3` dEarly consumer instantiated with `M := M+1`; successor-index dEarly theorem instantiated at `s0 := 0 : Fin (M+1)`; tangent is `v.1 s0.castSucc`; `dPsucc1`, `Psucc1`, and the next recursive derivative left explicit; recovery composes the same staged equality with `retainedPassiveFormalRawOrderJacobianAt_recovers_F3` and right-multiplies by `(-(coord.solvedA1 (Fin.last ((M+1)+1))))^-1` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md` | `F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` and `F3_tail_pos_pos_dEarly_zero_next_succ_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build, full `DLNFibre` build, `scripts/sorries`, `git diff --check`, and theorem axiom audit passed; axiom footprint is `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Dirac` and xhigh `Jason` in `threads/03-block-product-reduction/review-a2-retained-passive-f3-two-positive-tail-next-succ-substitution.md`; PASS; no one-positive-tail claim, no first-level `dPsucc` rewrite, no terminal cleanup, no full positive-tail `F3` target staging, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive positive-tail `F3` first `dEarly` substitution | A2 terminal `F3` derivative bridge support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | positive tail parameterized as `M+1`; terminal `dLast` target-staged theorem instantiated at `qLast := Fin.last M`; first-index zero-current `dEarly` theorem instantiated at `q0 := 0 : Fin (M+1)`; formal raw-order `F3` recovery; `dPsucc`, `dTail`, `dCnext`, and successor `Nextfun` derivative left explicit | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-positive-tail-dearly-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-positive-tail-dearly-substitution.md` | `F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt` and `F3_tail_pos_dEarly_zero_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`; focused Jacobian build, `scripts/sorries`, `git diff --check`, and theorem axiom audits passed; theorem preserves `- dEarly * coord.solvedA1(Fin.last (M+1))` and leaves recursive earlier-tail data explicit | reviewed by xhigh `Sartre` and xhigh `Popper` in `threads/03-block-product-reduction/review-a2-retained-passive-f3-positive-tail-dearly-substitution.md`; PASS; recovery right-multiplies the same staged expression by `(-(coord.solvedA1(Fin.last (M+1))))^-1`; no full positive-tail `F3` target staging, no recursion through `Nextfun`, no expansion of `dPsucc` or `dTail`, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive successor-index `dEarly` successor-current `dPcast` substitution | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | nonterminal `dEarly` product-rule wrapper instantiated at `M := M+1`, `q := s.succ : Fin (M+1)`; successor-current solved-`A1` residual-product derivative helper instantiated with `u := s.castSucc`; `Fin.succ_castSucc` identifies `u.succ = q.castSucc`; determinant-chart hypothesis inherited from successor-current helper; `dPsucc` and `Psucc` left explicit | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-succ-dpcast-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-succ-dpcast-substitution.md` | `fderiv_retainedPassiveLowerLeftProductTailSum_succ_product_dCprod_dG_dPcast_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative/Jacobian builds, `scripts/sorries`, `git diff --check`, and theorem axiom audit passed; theorem leaves `dPsucc`, `Psucc`, and first-summand `solvedA1(p)` explicit | reviewed by xhigh `Kierkegaard` in `threads/03-block-product-reduction/review-a2-retained-passive-dearly-succ-dpcast-substitution.md`; PASS; tangent is exactly `v.1 s.castSucc`; no zero-branch `dTail`, no terminal cleanup, no target staging, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive first-index `dEarly` zero-current `dPcast` substitution | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | nonterminal `dEarly` product-rule wrapper instantiated at `M := M+1`, `q := 0 : Fin (M+1)`; zero-current solved-`A1` residual-product derivative helper; determinant-chart hypothesis inherited from zero-current helper; `dPsucc`, `Psucc`, and `dTail` left explicit | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-zero-dpcast-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-zero-dpcast-substitution.md` | `fderiv_retainedPassiveLowerLeftProductTailSum_zero_product_dCprod_dG_dPcast_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative/Jacobian builds, `scripts/sorries`, `git diff --check`, and theorem axiom audit passed; theorem leaves `dPsucc`, `Psucc`, first-summand `solvedA1(p)`, and `dTail` explicit | reviewed by xhigh `Pasteur` in `threads/03-block-product-reduction/review-a2-retained-passive-dearly-zero-dpcast-substitution.md`; PASS; no `Fin M` nonemptiness assumption, no `Psucc = Tail`, no recursive `dTail`, no terminal cleanup, no target staging, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive successor-current solved-`A1` `dPcast` substitution | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | generic solved-`A1` residual-product product rule; successor solved-`A1` derivative branch; determinant-chart hypothesis inherited from product-rule helper; `dPsucc` left explicit | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dpcast-succ-solveda1-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dpcast-succ-solveda1-substitution.md` | `fderiv_retainedPassive_solvedA1_residualFactorProduct_succ_castSucc_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative/Jacobian builds, `scripts/sorries`, `git diff --check`, and theorem axiom audit passed; theorem leaves `dPsucc` and first-summand `solvedA1(q.succ)` explicit | reviewed by xhigh `Banach` in `threads/03-block-product-reduction/review-a2-retained-passive-dpcast-succ-solveda1-substitution.md`; PASS; tangent is exactly `v.1 q`; no downstream `dEarly` specialization, terminal cleanup, determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive zero-current solved-`A1` `dPcast` substitution | A2 derivative recurrence support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; recurrence infrastructure is local Lean development | generic solved-`A1` residual-product product rule; zero solved-`A1` derivative branch; determinant-chart hypothesis for inverse passive tail; `dPsucc` and `dTail` left explicit | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dpcast-zero-solveda1-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dpcast-zero-solveda1-substitution.md` | `fderiv_retainedPassive_solvedA1_residualFactorProduct_zero_castSucc_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused derivative/Jacobian builds, `scripts/sorries`, `git diff --check`, and theorem axiom audit passed; theorem leaves `dPsucc`, `dTail`, and the first-summand `solvedA1(0)` factor explicit | reviewed by xhigh `Hypatia` in `threads/03-block-product-reduction/review-a2-retained-passive-dpcast-zero-solveda1-substitution.md`; PASS; no `Psucc = Tail`, no recursive `dTail`, no downstream `dEarly` specialization, no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive solved-`A1` zero derivative | A2 derivative split support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; local retained-passive coordinate definitions | determinant-chart hypothesis for inverse passive tail; matrix inverse derivative; product rule for `Tail^-1 * Ctop`; coordinate projection derivative for `Ctop`; no recursive `dTail` expansion | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-solved-a1-zero-fderiv.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-a1-zero-fderiv.md` | `fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv` and `fderiv_retainedPassive_toCoordinateData_solvedA1_zero_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; duplicate downstream inverse-tail proof removed from `RetainedPassiveCoordinatesJacobian.lean`; focused derivative/Jacobian builds, `scripts/sorries`, `git diff --check`, full `DLNFibre` build, and axiom audits passed; theorem names have only `[propext, Classical.choice, Quot.sound]` | reviewed by xhigh `Feynman` in `threads/03-block-product-reduction/review-a2-retained-passive-solved-a1-zero-fderiv.md`; PASS; factor order `Tail^-1*dTail*Tail^-1*Ctop` preserved; no determinant equality, measure transport, normal crossings, pole order, or RLCT |
| Retained-passive solved-`A1` successor derivative | A2 derivative split support | PDF pp. 11-13 as retained-passive product-reduction coordinate algebra; local retained-passive coordinate definitions | `retainedPassiveSolvedA1_eq_of_ne_zero`; `A1seed(p.succ)=A1passive(p)`; coordinate projection derivative; no determinant-chart hypothesis | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-solved-a1-successor-fderiv.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-a1-successor-fderiv.md` | `fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; duplicate downstream proof removed from `RetainedPassiveCoordinatesJacobian.lean`; focused derivative/Jacobian builds, `scripts/sorries`, `git diff --check`, full `DLNFibre` build, and axiom audit passed; statement uses `TopologyTuple`, not `RetainedPassiveRawTopologyTuple` | reviewed by xhigh `Sagan` in `threads/03-block-product-reduction/review-a2-retained-passive-solved-a1-successor-fderiv.md`; PASS with required statement adjustment; no determinant-chart hypothesis, no zero-branch formula, no raw-order Jacobian, no measure transport, no normal crossings, pole order, or RLCT |
| Retained-passive terminal `dEarly` `dPcast` substitution | A2 derivative recurrence support | PDF pp. 11-13 as product-reduction coordinate algebra; recurrence infrastructure is local Lean development | terminal `dCprod`/`dG` boundary; solved-`A1` residual-product product-rule helper; determinant-chart hypothesis; no terminal `Psucc` cleanup | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-terminal-dpcast-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-terminal-dpcast-substitution.md` | `fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_dPcast_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused module build, `scripts/sorries`, `git diff --check`, full `DLNFibre` build, and axiom audit passed; theorem leaves terminal `Psucc` and `(fderiv solvedA1 p)` explicit | reviewed by xhigh `Volta` in `threads/03-block-product-reduction/review-a2-retained-passive-dearly-terminal-dpcast-substitution.md`; no source-staging of `solvedA1 0`, no terminal `Psucc` cleanup, no determinant equality, no measure transport, no normal crossings, pole order, or RLCT |
| Retained-passive `dEarly` `dPcast` substitution | A2 derivative recurrence support | PDF pp. 11-13 as product-reduction coordinate algebra; recurrence infrastructure is local Lean development | already `dCprod`/`dG`-staged retained-passive `dEarly` recurrence; solved-`A1` residual-product product-rule helper; determinant-chart hypothesis; no source-staging of `solvedA1 0` | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dpcast-substitution.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dpcast-substitution.md` | `fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_dPcast_castSucc_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused module build, `scripts/sorries`, `git diff --check`, full `DLNFibre` build, and axiom audit passed; theorem leaves `(fderiv solvedA1 p)` and successor `dPsucc` explicit | reviewed by xhigh `Euclid` in `threads/03-block-product-reduction/review-a2-retained-passive-dearly-dpcast-substitution.md`; no derivative formula for `solvedA1 0`, no complete `dPcast` source-staging, no determinant equality, no measure transport, no normal crossings, pole order, or RLCT |
| Retained-passive solved-`A1` `dPcast` product rule | A2 derivative recurrence support | PDF pp. 11-13 as product-reduction coordinate algebra; recurrence infrastructure is local Lean development | solved-`A1` residual-product differentiability on determinant chart; current solved-factor differentiability; residual-factor unfold; no downstream Jacobian import | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md` | `fderiv_retainedPassive_solvedA1_residualFactorProduct_castSucc_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused module build, `scripts/sorries`, `git diff --check`, full `DLNFibre` build, and axiom audit passed; theorem leaves `(fderiv solvedA1 p)` explicit | reviewed by xhigh `Fermat` in `threads/03-block-product-reduction/review-a2-retained-passive-dearly-dpcast-solveda1-product-rule.md`; no derivative formula for `solvedA1 0`, no complete `dPcast` source-staging, no determinant equality, no measure transport, no normal crossings, pole order, or RLCT |
| Retained-passive terminal `dEarly`/`dCprod` boundary | A2 terminal recurrence boundary | PDF pp. 11-13 as product-reduction coordinate algebra; recurrence infrastructure is local Lean development | source-staged `dCprod` recurrence; terminal zeroed-tail derivative; empty stored-`C` self suffix derivative; determinant-chart hypothesis for solved `A1` product factors; no analytic extraction | reproduced at `threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-terminal-dcprod-boundary.md`; statement card `threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-terminal-dcprod-boundary.md` | `fderiv_retainedPassive_C_residualFactorProduct_self_apply` and `fderiv_retainedPassiveLowerLeftProductTailSum_last_product_dCprod_dG_apply` proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean`; focused module build, `scripts/sorries`, `git diff --check`, full `DLNFibre` build, and axiom audit passed; theorem leaves `Cnext(z)`, terminal `Cprod(z)`, and `dPcast_z(v)` explicit | reviewed by xhigh `Copernicus` in `threads/03-block-product-reduction/review-a2-retained-passive-dearly-terminal-dcprod-boundary.md`; no empty-product value cleanup, no one-edge `Cprod` cleanup, no `dPcast` staging, no determinant equality, no measure transport, no normal crossings, pole order, or RLCT |
| Normal-crossing unit factors in chart displays | A0 certificate algebra | PDF pp. 5-6 | supplied chart certificate; supplied pointwise unit multipliers; no analytic extraction transfer | reproduced at `threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-unit-multiply-a0.md`; statement card `threads/02-analytic-interface/statement-card-a0-normal-crossing-chart-certificate-unit-multiply.md` | `AoyagiNormalCrossingChartCertificate.unitMultiply`, `exponentData_unitMultiply`, `exponentData_exponentMinimum_unitMultiply`, and `exponentData_exponentOrder_unitMultiply` proved in `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`; exponent data, finite minimum, and finite order are unchanged; divisor monomial shifts are outside intended use unless separately supplied as units | reviewed by xhigh `Epicurus` in `threads/02-analytic-interface/review-normal-crossing-chart-certificate-unit-multiply-a0.md` |
| RLCT definition and normal-crossing extraction | A0 | PDF pp. 5-6; p. 13 only as regular-variable-count motivation | external analytic theorem; finite certificate arithmetic | scout report `threads/02-analytic-interface/scout-report.md`; interface draft `threads/02-analytic-interface/interface-draft.md`; A2 repair `threads/02-analytic-interface/interface-repair-a2.md`; finite formula reproduction `threads/02-analytic-interface/reproduction-normal-crossing-exponent-interface-a0.md`; finite certificate reproduction `threads/02-analytic-interface/reproduction-normal-crossing-finite-certificates-a0.md`; ratio chart-count reproduction `threads/02-analytic-interface/reproduction-normal-crossing-ratio-chart-counts-a0.md`; Jacobian/prior loss-shift reproduction `threads/02-analytic-interface/reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`; chart-certificate lift reproduction `threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md` | finite exponent interface proved in `lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`: finite exponent data, active ratios/minimum/order, min/max certificates, ratio chart-count helpers, chart-certificate spine, `jacobianPriorLossShift` with active ratio shift by `m/2`, finite minimum shift by `m/2`, ratio-count shift, and preservation of `minCoordsInChart`, `minCountInChart`, and `exponentOrder`, plus `AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift` projecting definitionally to the finite exponent-data shift and preserving the projected finite order while shifting the projected finite minimum by `m/2`; analytic extraction remains Cited | xhigh source/API review recorded in `threads/02-analytic-interface/review-normal-crossing-exponent-interface-a0.md`; finite-certificate review passed in `threads/02-analytic-interface/review-normal-crossing-finite-certificates-a0.md`; ratio-count review passed in `threads/02-analytic-interface/review-normal-crossing-ratio-chart-counts-a0.md`; Jacobian/prior loss-shift reviews passed in `threads/02-analytic-interface/review-normal-crossing-jacobian-prior-loss-shift-a0.md` and `threads/02-analytic-interface/review-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`; A2 repair excludes Lemma 1/additivity/Theorem 4 as separate citations |
| Case 2 scalar-normalized `Q/P` product | A4 finite algebra/scalar accounting | PDF pp. 19-21 | displayed Case 2 chart; `D_J = u N`; transported weights `b'_i = u b_i`; supplied quotient witnesses; no chart/source production | reproduced at `threads/04-blow-up-certificate/reproduction-case2-corrected-weight-scalar-transport-a4.md`; statement card `threads/04-blow-up-certificate/statement-card-a4-case2-corrected-weight-scalar-transport.md` | `weightedPivotDiagonal_mul_smul` and `weightedPivotBlockRowOp_mul_oldDiagonal_mul_smul_pivotPreQBlock_mul_pivotQ` proved in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; the selected scalar is absorbed into transported diagonal weights and no extra final `u` is formalized under the p. 20 convention | reviewed by controller with xhigh source scout `Zeno` and Lean/API scout `Noether` in `threads/04-blow-up-certificate/review-case2-corrected-weight-scalar-transport-a4.md`; no coverage, source-produced `C'`, successor chart family, residual-index equivalence, normal crossings, pole order, or RLCT |
| Theorem 1, cited three-layer formula | context/special case | PDF pp. 6-7 | prior result [12]; likely derivable from Theorem 2 at `L=2` | pending/optional | no Lean target yet | pending |
| Theorem 2 multi-layer main formula | A6 | PDF pp. 8-9 | A0-A5 | formula arithmetic reproduced at `threads/06-dln-translation/reproduction-definition3-theorem2-translation-a6.md`; dimension/rank convention reproduced at `threads/06-dln-translation/reproduction-dimension-rank-convention-a6.md`; conditional finite-exponent bridge reproduced at `threads/06-dln-translation/reproduction-theorem2-finite-exponent-bridge-a6.md`; finite certificate bridge reproduced at `threads/06-dln-translation/reproduction-theorem2-finite-certificate-bridge-a6.md`; supplied final assembly boundary reproduced at `threads/06-dln-translation/reproduction-theorem2-final-assembly-a6.md`; Definition 3 branch-selection source audit at `threads/06-dln-translation/source-audit-definition3-branch-selection-a6.md`; final theorem still open | final theorem TBD; formula notation/equivalences proved in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`; Definition 3 count bridges proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; conditional A0/A6 bridge proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean` with `AoyagiTheorem2FiniteExponentFormulaHypothesis`, `of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le`, `lambda_eq_theorem2Lambda_fromCeilData_of_extractionHypothesis`, `lambda_eq_theorem2Lambda_average_of_extractionHypothesis`, `lambda_eq_theorem2Lambda_expanded_of_extractionHypothesis`, `poleOrder_eq_theorem2OrderFormula_of_extractionHypothesis`, `lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_extractionHypothesis`, and `lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount`; supplied final socket proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean` as `AoyagiTheorem2SuppliedFinalBoundary` plus selected-width provenance and lambda/order projection theorems; selected rank-width and source selected-width inequalities are auxiliary theorem inputs, not final-boundary fields; finite min/order certificate obligations remain supplied; arbitrary Definition 3 source-data quantification is unsafe without a source-backed branch choice | formula/dimension slices reviewed at `threads/06-dln-translation/review-final-formula-notation-a6.md` and `threads/06-dln-translation/review-dimension-rank-convention-a6.md`; conditional bridge reviewed at `threads/06-dln-translation/review-theorem2-finite-exponent-bridge-a6.md`; finite certificate bridge reviewed at `threads/06-dln-translation/review-theorem2-finite-certificate-bridge-a6.md`; final assembly reviewed at `threads/06-dln-translation/review-theorem2-final-assembly-a6.md`; branch-selection source audit by xhigh `Einstein the 3rd` found no printed tie-breaker; final theorem review pending |
| Theorem 2 source-rank regular-shift final socket | A6 finite/certificate bridge | PDF pp. 8-9 and p. 13 | Definition 3 source data; A2 source-rank-stratum rank-width bridge; finite regular-variable shift; shifted extraction hypothesis supplied | reproduced at `threads/06-dln-translation/reproduction-theorem2-source-rank-regular-shift-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-source-rank-regular-shift-bridge.md` | `AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_regularVariableCountShift` and `AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2SourceRankRegularShiftBridge.lean`; these return the existing supplied final sockets for the shifted exponent datum/certificate while keeping shifted extraction, reduced minimum-plus-regular-term, and reduced order obligations explicit; no regular-suspension construction, analytic ideal transport, active-ratio/chart-count proof, normal-crossing production, pole order, or RLCT | xhigh review passed in `threads/06-dln-translation/review-theorem2-source-rank-regular-shift-bridge-a6.md`; reviewer explicitly required the extraction hypothesis to stay shifted |
| Theorem 2 rank-width regular-shift final socket | A6 finite/certificate bridge | PDF pp. 8-9 and p. 13 | Definition 3 source data; source-range rank-width hypothesis; finite regular-variable shift; shifted extraction hypothesis supplied | reproduced at `threads/06-dln-translation/reproduction-theorem2-rank-width-regular-shift-bridge-a6.md`; finite rank-width shift reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-variable-rank-width-shift.md` | `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_rankWidth` and chart version proved in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`; `AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_regularVariableCountShift` and chart version proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2RankWidthRegularShiftBridge.lean`; the source-rank regular-shift wrappers now derive `hr` and delegate to this bridge | xhigh review passed in `threads/03-block-product-reduction/review-a2-regular-variable-rank-width-shift.md` and `threads/06-dln-translation/review-theorem2-rank-width-regular-shift-bridge-a6.md`; shifted extraction and reduced minimum/order obligations remain supplied |
| Case 2 regular-shift finite formula bridge | A6 finite exponent-array bridge | PDF pp. 8-9 and p. 13; Case 2 local ratio from PDF pp. 19-22 via supplied A4/A0 bridge | supplied Case 2/A0 coordinate bridge; active-ratio lower bound; endpoint rank bounds; shifted reduced-ratio-plus-regular-term lambda equality; reduced order or chart-count facts | reproduced at `threads/06-dln-translation/reproduction-case2-theorem2-regular-shift-finite-formula-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-case2-theorem2-regular-shift-finite-formula-bridge.md` | `Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_regularVariableCountShift_of_forall_le_of_centerCard_add_regularTerm_eq_fromCeilData` and chart-count variant proved in `lean/DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean`; conclusion is the finite formula hypothesis for `D.jacobianPriorLossShift (aoyagiTheorem2RegularVariableCount Lthm H r)` | xhigh review passed in `threads/06-dln-translation/review-case2-theorem2-regular-shift-finite-formula-bridge-a6.md`; no construction of regular-suspension charts, analytic transport, active-ratio lower bounds, shifted lambda equality, normal crossings, pole order, or RLCT |
| Supplied regular-suspension full-certificate boundary | A2/A6 interface | PDF p. 13 for block/count motivation; PDF pp. 5-6 for supplied extraction boundary | supplied reduced chart certificate; supplied full chart certificate; abstract source/ideal/coverage/Jacobian obligations; finite exponent equality; extraction for `Cfull` | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-suspension-interface.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-suspension-interface.md` | `AoyagiSuppliedRegularSuspensionBoundary` and `AoyagiSuppliedRegularSuspensionCertificate` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`; finite projections `full_exponentMinimum_eq_reduced_add_half_regularCount`, `full_exponentOrder_eq_reduced`, `full_exponentMinimum_eq_reduced_add_regularTerm`, finite-formula projection, and `theorem2SuppliedChartFinalBoundary_of_regularVariableCount` return `AoyagiTheorem2SuppliedChartFinalBoundary Cfull ...` exactly; no construction of `Cfull`, analytic transport, Aoyagi Lemma 1, regular-coordinate additivity, normal-crossing production, pole order, or RLCT | xhigh review passed in `threads/03-block-product-reduction/review-a2-regular-suspension-interface.md`; reviewer required independent reduced/full chart types and extraction only on `Cfull` |
| Supplied regular-suspension extraction projection | A2 supplied full-certificate projection | PDF p. 13 for regular-count motivation; PDF pp. 5-6 for supplied extraction boundary | supplied regular-suspension boundary; extraction hypothesis on `Cfull`; finite regular-count arithmetic | reproduced at `threads/03-block-product-reduction/reproduction-a2-supplied-regular-suspension-extraction-projection.md`; statement card `threads/03-block-product-reduction/statement-card-a2-supplied-regular-suspension-extraction-projection.md` | `AoyagiSuppliedRegularSuspensionCertificate.lambda_eq_reduced_add_half_regularCount`, `...poleOrder_eq_reduced_exponentOrder`, `...lambda_eq_reduced_add_regularTerm`, and `...lambda_and_poleOrder_eq_reduced_add_regularTerm` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`; extraction stays on `Cfull` and is projected through the supplied finite exponent equality | xhigh `Tesla the 4th` review passed in `threads/03-block-product-reduction/review-a2-regular-suspension-projections-and-loss-shape.md`; no construction of `Cfull`, no extraction from `Cred`, no Fubini/polar theorem, no Aoyagi Lemma 1 or Theorem 4, no normal-crossing production, pole-order theorem, or RLCT theorem beyond supplied full-certificate extraction |
| Canonical product-difference regular-chart source | A2 regular-suspension source predicate | PDF pp. 11-13, especially p. 13 product-difference blocks | A2 canonical local source certificate; supplied regular-suspension ideal/coverage/Jacobian/exponent obligations | reproduced at `threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-regular-chart-source.md`; statement card `threads/03-block-product-reduction/statement-card-a2-canonical-product-difference-regular-chart-source.md` | `AoyagiCanonicalProductDifferenceRegularChartSource` and `AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularChartSource` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`; the constructor fills only `regular_chart_source` from `PaperEndpointCanonicalProductDifferenceLocalSourceCertificate` and leaves ideal transport, coverage, Jacobian compatibility, exponent shift, `Cfull`, normal crossings, pole order, and RLCT supplied/open | xhigh review passed in `threads/03-block-product-reduction/review-a2-canonical-product-difference-regular-chart-source.md` |
| Regular-suspension scalar coordinate index | A2 finite regular-coordinate bookkeeping | PDF p. 13 | A2 canonical local certificate; fixed-base endpoint complement construction; base product rank; dimension convention | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-suspension-coordinate-index.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-suspension-coordinate-index.md` | `AoyagiRegularBlockCoordinateIndex`, `AoyagiRegularBlockCoordinateIndex.value`, `AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount`, `paperEndpointEndpointComplementIndex_card_eq_layerSubRank`, `paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount`, `PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt`, and `PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; finite coordinate/count, endpoint complement cardinalities, and componentwise continuity only; no ideal split or regular-suspension chart | controller and xhigh `Russell the 3rd` review passed in `threads/03-block-product-reduction/review-a2-regular-suspension-coordinate-index.md`; import boundary narrowed after review |
| Continuity-to-small-loss neighborhood | A2 finite real topology | PDF p. 13 only as motivation for the `F2`,`F3` smallness condition | centered `ContinuousAt` finite real coordinate families; coordinatewise centered-continuity data; finite disjoint-sum square-sum split | reproduced at `threads/03-block-product-reduction/reproduction-a2-continuity-to-small-loss-neighborhood.md`; statement card `threads/03-block-product-reduction/statement-card-a2-continuity-to-small-loss-neighborhood.md` | `aoyagiCoordinateSquareSum_continuousAt`, `aoyagiCoordinateSquareSum_eventually_le_one_of_continuousAt_zero`, `aoyagiCoordinateSquareSum_add_eventually_le_one_of_continuousAt_zero`, `aoyagiCoordinateSquareSum_eventually_le_one_of_forall_centered_continuousAt`, and `aoyagiCoordinateSquareSum_add_eventually_le_one_of_forall_centered_continuousAt` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; ambient `nhds` over `real` only, not a source-stratum or analytic-chart theorem | xhigh review passed in `threads/03-block-product-reduction/review-a2-continuity-to-small-loss-neighborhood.md`; focused module build passed after wrapper addition |
| Regular-coordinate F2/F3 smallness projection | A2 finite p. 13 tag projection | PDF p. 13 | tagged regular-coordinate index; coordinatewise centered-continuity data; generic two-family real smallness theorem | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-coordinate-f2-f3-smallness-projection.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-coordinate-f2-f3-smallness-projection.md` | `AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; ambient `nhds` over `real` only, not a fixed-base source-data, source-stratum, or analytic-chart theorem | xhigh `McClintock the 4th` review passed in `threads/03-block-product-reduction/review-a2-regular-coordinate-f2-f3-smallness-projection.md`; explicit nested-sum tag annotations retained |
| Fixed-base regular-coordinate F2/F3 smallness | A2 source-data topology wrapper | PDF p. 13 | fixed-base regular-coordinate source data; centered-continuity of actual regular-coordinate map; finite p. 13 tag projection | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-regular-coordinate-f2-f3-smallness.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_f2_f3_squareSum_eventually_le_one` and `..._nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; real fixed-base source-data map only; the `nhdsWithin` theorem is a filter weakening, not source-rank openness | xhigh `Kierkegaard the 4th` review passed in `threads/03-block-product-reduction/review-a2-fixed-base-regular-coordinate-f2-f3-smallness.md`; no analytic chart, source coverage, Fubini/polar shift, normal crossings, pole order, or RLCT |
| Fixed-base literal-cleaned square-sum comparison | A2 source-data finite loss comparison | PDF p. 13 | fixed-base regular-coordinate F2/F3 smallness; finite literal-vs-cleaned factor-2 comparison; fixed-base product-difference coordinate maps | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-literal-cleaned-square-sum-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-literal-cleaned-square-sum-comparison.md` | `paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap`, `PaperEndpointFixedBaseRegularCoordinateSourceData.literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two`, directional ambient wrappers, and source-rank `nhdsWithin` wrappers proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; finite real square-sum comparison only | xhigh `Linnaeus the 4th` review passed in `threads/03-block-product-reduction/review-a2-fixed-base-literal-cleaned-square-sum-comparison.md`; no analytic ideal transport, chart construction, source coverage, source-rank openness, normal crossings, pole order, or RLCT |
| p.13 source regular-suspension boundary and source-data loss wrapper | A2 source-side finite loss boundary | PDF pp. 10-14, especially p. 13 and p. 14 Theorem 4 handoff | Theorem 3 block algebra; source-data constructor from rank data; fixed-base literal/cleaned factor-2 comparison | reproduced at `threads/03-block-product-reduction/reproduction-a2-p13-source-regular-suspension-boundary.md`; statement card `threads/03-block-product-reduction/statement-card-a2-p13-source-regular-suspension-boundary.md` | `exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_cleaned_productDifferenceCoordinateMap_squareSum_eventually_factor_two_nhdsWithin_source_of_rank_eq` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; it chooses fixed-base regular-coordinate source data from real rank/source hypotheses and returns the existing source-rank `nhdsWithin` factor-`2` comparison; no regular-suspension chart, Jacobian/prior shift, normal crossings, Theorem 4 reduction, pole order, or RLCT | xhigh `Gibbs the 4th` review passed in `threads/03-block-product-reduction/review-a2-p13-source-regular-suspension-boundary.md`; source audit confirms `D-F3F2` lower-right block, p.13 RLCT shift as assertion, and p.14 `r(s)=r` as Theorem 4-dependent |
| Adapted product-difference triangular multiplier comparison | A2 finite p.13 adapted-coordinate comparison | PDF p. 13 | p.13 triangular block identity; finite Frobenius/Cauchy-Schwarz square-sum estimates; supplied multiplier square-sum bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-adapted-product-difference-triangular-multiplier-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-adapted-product-difference-triangular-multiplier-comparison.md` | `matrixCoordinateSquareSum_mul_le_mul`, `matrixCoordinateSquareSum_mul_mul_le_mul`, `const_mul_matrixCoordinateSquareSum_le_of_mul_eq_of_multiplierSquareSum_mul_le`, `AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_eq_fromBlocks_neg_neg_sub_mul`, and `AoyagiProductDifferenceCoordinateIndex.const_mul_literalCoordinateSquareSum_le_productDifferenceSquareSum_of_triangularBlockProduct` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; finite adapted product-difference square-sum lower-bound only | xhigh `Ramanujan the 5th` review passed in `threads/03-block-product-reduction/review-a2-adapted-product-difference-triangular-multiplier-comparison.md`; no original DLN loss comparison, covariance lower bound, basis norm equivalence, multiplier boundedness theorem, analytic chart construction, Jacobian/prior transport, regular-suspension theorem, normal crossings, pole order, or RLCT |
| Fixed-base adapted product-difference certificate bound | A2 pointwise p.13 certificate wrapper | PDF p. 13 | fixed-base product-reduction certificate block identity; deterministic suffix-state fields; finite triangular-multiplier comparison; supplied multiplier square-sum bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-adapted-product-difference-certificate-bound.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-adapted-product-difference-certificate-bound.md` | `paperEndpointFixedBaseAdaptedProductDifferenceSquareSum`, `paperEndpointFixedBaseTriangularMultiplierSquareSumProduct`, and `PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_le_adaptedProductDifferenceSquareSum` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; pointwise adapted fixed-base product-difference square-sum bound only | xhigh API/math review passed in `threads/03-block-product-reduction/review-a2-fixed-base-adapted-product-difference-certificate-bound.md`; no original DLN loss comparison, covariance lower bound, basis norm equivalence, local multiplier boundedness theorem, source-rank openness, analytic chart construction, Jacobian/prior transport, regular-suspension theorem, normal crossings, pole order, or RLCT |
| Source-filter adapted product-difference bound | A2 source-filter p.13 certificate wrapper | PDF p. 13 | pointwise adapted product-difference certificate bound; eventual product-reduction certificate; eventual multiplier square-sum bound; finite literal/cleaned half-bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-source-filter-adapted-product-difference-bound.md`; statement card `threads/03-block-product-reduction/statement-card-a2-source-filter-adapted-product-difference-bound.md` | `PaperEndpointFixedBaseProductReductionCertificate.const_mul_literalProductDifferenceCoordinateMap_squareSum_eventually_le_adaptedProductDifferenceSquareSum_nhdsWithin_source` and `PaperEndpointFixedBaseRegularCoordinateSourceData.half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productReductionCertificate_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; source-filter adapted square-sum bound only | xhigh API/math review passed in `threads/03-block-product-reduction/review-a2-source-filter-adapted-product-difference-bound.md`; no original DLN loss comparison, covariance lower bound, basis norm equivalence, local multiplier boundedness theorem, source-rank openness, analytic chart construction, Jacobian/prior transport, regular-suspension theorem, normal crossings, pole order, or RLCT |
| Fixed-base triangular multiplier local boundedness | A2 self-base p.13 multiplier bound | PDF p. 13 | fixed-base suffix-state field continuity; self-base determinant-chart hypotheses; finite real continuity/local boundedness; source-filter adapted product-difference bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-triangular-multiplier-local-boundedness.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-triangular-multiplier-local-boundedness.md` | `continuousAt_eventually_le_self_add_one`, `continuousAt_exists_pos_eventually_le`, `aoyagiCoordinateSquareSum_exists_pos_eventually_le_of_continuousAt`, `paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le`, `paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_nhdsWithin_source`, and `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_half_regular_add_residual_squareSum_eventually_le_adaptedProductDifferenceSquareSum_selfBase_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; positive self-base adapted square-sum lower-bound only | xhigh `Goodall the 5th` API review and xhigh `Aquinas the 5th` pen-and-paper check recorded in `threads/03-block-product-reduction/review-a2-fixed-base-triangular-multiplier-local-boundedness.md`; no original DLN loss comparison, source-rank openness, analytic chart construction, Jacobian/prior transport, regular-suspension theorem, normal crossings, pole order, or RLCT |
| Fixed-base adapted endpoint Frobenius comparison | A2 finite endpoint loss coordinate identity | PDF p. 13 | fixed-base adapted endpoint basis construction; base endpoint total block identity; finite real trace-square identity; existing adapted square-sum product-reduction bounds | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-adapted-endpoint-frobenius-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-adapted-endpoint-frobenius-comparison.md` | `matrix_trace_transpose_mul_self_eq_aoyagiCoordinateSquareSum`, `paperEndpointFixedBaseTotalMatrixOfReverseEdges_selfBase_eq_fromBlocks_one_zero_zero`, `paperEndpointFixedBaseAdaptedProductDifferenceSquareSum_eq_baseRelative_totalMatrix_squareSum`, `paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss`, `paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum`, and Frobenius-form p.13 product-reduction wrappers proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; fixed-basis endpoint Frobenius loss only | xhigh `Sagan the 5th` review passed in `threads/03-block-product-reduction/review-a2-fixed-base-adapted-endpoint-frobenius-comparison.md`; no original `lossDLN` comparison, original-coordinate basis-norm comparison, statistical/KL/covariance loss, product chart, source-rank openness, density/Jacobian transport, regular-suspension theorem, normal crossings, pole order, or RLCT |
| Finite basis-change square-sum comparison | A2 finite endpoint-coordinate algebra | finite linear algebra, used after PDF p. 13 endpoint coordinate identity | finite Cauchy-Schwarz matrix square-sum estimate; `LinearMap.toMatrix_comp`; fixed source/target bases | reproduced at `threads/03-block-product-reduction/reproduction-a2-finite-basis-change-square-sum-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-finite-basis-change-square-sum-comparison.md` | `exists_pos_const_matrixCoordinateSquareSum_le_of_mul_eq`, `exists_pos_const_forall_matrixCoordinateSquareSum_le_mul`, `exists_pos_const_linearMap_toMatrix_squareSum_le_of_basis_change`, and `exists_pos_const_forall_linearMap_toMatrix_squareSum_le_of_basis_change` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; finite global basis-change comparison only | xhigh Curie review passed in `threads/03-block-product-reduction/review-a2-finite-basis-change-square-sum-comparison.md`; no `lossDLN`, tuple/product bridge, statistical/KL/covariance comparison, product chart, source-rank openness, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Chain-map tuple product bridge | A2 product-coordinate bridge | finite linear algebra, needed before original `lossDLN` comparison | core `Tuple`/`mult`/`submult`; Aoyagi `chainMap`; `LinearMap.toMatrix_comp`; fixed bases at each layer | reproduced at `threads/03-block-product-reduction/reproduction-a2-chainmap-tuple-product-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-chainmap-tuple-product-bridge.md` | `chainMapMatrixTuple`, `submult_chainMapMatrixTuple`, `multPrefix_chainMapMatrixTuple`, `mult_chainMapMatrixTuple`, `mult_toMatrix_chainMap`, and `mult_toMatrix_chainMap_reverseVertex` proved in `lean/DLNFibre/DLN/Aoyagi/ChainMapTupleBridge.lean`; finite tuple/product identity only | xhigh Mill and Franklin scouts passed in `threads/03-block-product-reduction/review-a2-chainmap-tuple-product-bridge.md`; no `lossDLN` unfolding, target-matrix choice, adapted-to-original basis comparison, statistical/KL/covariance comparison, product chart, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Chain-map loss bridge | A2 original endpoint loss rewrite | finite linear algebra, after chain-map tuple product bridge | `lossDLN`; `chainMapMatrixTuple`; `mult_chainMapMatrixTuple`; fixed endpoint bases | reproduced at `threads/03-block-product-reduction/reproduction-a2-chainmap-loss-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-chainmap-loss-bridge.md` | `chainMapMatrixFrobeniusLossAgainst`, `chainMapMatrixFrobeniusLoss`, `lossDLN_chainMapMatrixTuple_eq_trace`, `lossDLN_chainMapMatrixTuple_eq_chainMapFrobenius`, and `lossDLN_reverseVertex_chainMapMatrixTuple_eq_baseFrobenius` proved in `lean/DLNFibre/DLN/Aoyagi/ChainMapLossBridge.lean`; exact `lossDLN` Frobenius rewrite only | xhigh Laplace statement review passed in `threads/03-block-product-reduction/review-a2-chainmap-loss-bridge.md`; no adapted-to-original basis comparison, no positive lower-bound comparison, no statistical/KL/covariance comparison, product chart, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Endpoint loss comparison | A2 finite original-loss comparison | finite endpoint linear algebra after PDF p. 13 fixed adapted endpoint loss | fixed adapted endpoint Frobenius identity; finite basis-change square-sum comparison; chain-map loss bridge | reproduced at `threads/03-block-product-reduction/reproduction-a2-endpoint-loss-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-endpoint-loss-comparison.md` | `chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum`, `exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss`, and `exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple` proved in `lean/DLNFibre/DLN/Aoyagi/EndpointLossComparison.lean`; positive comparison only for chain-map tuples with target `[T(B)]` in original endpoint bases | xhigh Pascal review passed in `threads/03-block-product-reduction/review-a2-endpoint-loss-comparison.md`; no arbitrary-tuple, statistical/KL/covariance, chart, density/Jacobian, normal-crossing, pole-order, or RLCT claim |
| Original loss self-base lower bound | A2 source-filter original-loss lower bound | PDF p. 13 via self-base product-reduction lower bound plus finite endpoint comparison | self-base adapted p.13 lower bound; endpoint loss comparison; continuous self-base edge family | reproduced at `threads/03-block-product-reduction/reproduction-a2-original-loss-self-base-lower-bound.md`; statement card `threads/03-block-product-reduction/statement-card-a2-original-loss-self-base-lower-bound.md` | `exists_pos_const_half_regular_add_residual_squareSum_eventually_le_lossDLN_chainMapMatrixTuple_selfBase_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/EndpointLossComparison.lean`; one-parameter source-filter lower bound for original `lossDLN` on `chainMapMatrixTuple b (Cedge x)` | xhigh Plato review passed in `threads/03-block-product-reduction/review-a2-original-loss-self-base-lower-bound.md`; no product chart, independent regular fiber variable, signed-box source-measure transport, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Original loss source-measure handoff | A2 restricted-source original-loss a.e. wrapper | PDF p. 13 via self-base original-loss lower bound | original-loss self-base source-filter theorem; local-measure `nhdsWithin` to restricted a.e. handoff; source-stratum measurability | reproduced at `threads/03-block-product-reduction/reproduction-a2-original-loss-source-measure-handoff.md`; statement card `threads/03-block-product-reduction/statement-card-a2-original-loss-source-measure-handoff.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase` and `...prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase` proved in `lean/DLNFibre/DLN/Aoyagi/OriginalLossSourceMeasure.lean`; restricted-measure a.e. comparison only, with the product theorem depending only on the first coordinate | xhigh Leibniz review passed in `threads/03-block-product-reduction/review-a2-original-loss-source-measure-handoff.md`; no product chart, independent regular fiber variable, signed-box pushforward, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Original loss source-measure continuous-edge wrapper | A2 measurable-source convenience wrapper | PDF p. 13 via source-rank measurability and self-base original-loss handoff | global continuity of `Cedge`; source-rank-stratum measurability theorem; original-loss source-measure handoff | reproduced at `threads/03-block-product-reduction/reproduction-a2-original-loss-source-measure-continuous-edge-wrapper.md`; statement card `threads/03-block-product-reduction/statement-card-a2-original-loss-source-measure-continuous-edge-wrapper.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge` and `...prod_fst_half_regular_add_residual_squareSum_le_lossDLN_chainMapMatrixTuple_selfBase_of_continuousEdge` proved in `lean/DLNFibre/DLN/Aoyagi/OriginalLossSourceMeasure.lean`; discharges source-stratum measurability and `ContinuousAt` from global `Continuous Cedge` | xhigh Chandrasekhar review passed in `threads/03-block-product-reduction/review-a2-original-loss-source-measure-continuous-edge-wrapper.md`; no source-rank openness, product chart, independent regular fiber variable, signed-box pushforward, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Adapted product-difference local-measure handoff | A2 self-base p.13 source-measure wrapper | PDF p. 13 via fixed-base adapted lower bound | self-base adapted fixed-base lower bound; local-measure `nhdsWithin` to restricted a.e. handoff; source-stratum measurability | reproduced at `threads/03-block-product-reduction/reproduction-a2-adapted-product-difference-local-measure-handoff.md`; statement card `threads/03-block-product-reduction/statement-card-a2-adapted-product-difference-local-measure-handoff.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase` and `...prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; restricted-measure a.e. comparison only, preserving the positive constant from the source-filter theorem | xhigh `Epicurus the 5th` review passed in `threads/03-block-product-reduction/review-a2-adapted-product-difference-local-measure-handoff.md`; no original DLN/statistical loss comparison, no product-chart construction, no Jacobian/prior transport, no residual integrability, no normal crossings, pole order, or RLCT |
| Adapted product-difference local finite-integral handoff | A2 conditional p.13 finite-integral wrapper | PDF p. 13 via supplied product-coordinate adapted loss | p.13 local finite-integral theorem; supplied product edge-family; supplied adapted product-difference lower bound; supplied chart-loss identification; residual and density hypotheses | reproduced at `threads/03-block-product-reduction/reproduction-a2-adapted-product-difference-local-finite-integral-handoff.md`; statement card `threads/03-block-product-reduction/statement-card-a2-adapted-product-difference-local-finite-integral-handoff.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_chartLoss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_identified` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; conditional ball-local finite-integral handoff only | xhigh `Galileo the 5th` review passed after fixing statement-card ball-indicator wording in `threads/03-block-product-reduction/review-a2-adapted-product-difference-local-finite-integral-handoff.md`; no product-chart construction, source coverage, Jacobian/prior transport, residual proof, original `lossDLN` comparison, normal crossings, pole order, or RLCT |
| Adapted product-difference loss-comparison finite-integral handoff | A2 conditional p.13 original-loss boundary | PDF p. 13 via supplied product-coordinate adapted loss comparison | p.13 local finite-integral theorem; supplied product edge-family; supplied adapted product-difference lower bound; supplied positive comparison from adapted square-sum to `loss`; residual and density hypotheses | reproduced at `threads/03-block-product-reduction/reproduction-a2-adapted-product-difference-loss-comparison-finite-integral.md`; statement card `threads/03-block-product-reduction/statement-card-a2-adapted-product-difference-loss-comparison-finite-integral.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; multiplies constants to use the existing p.13 finite-integral theorem with comparison constant `c0 * c` | xhigh `Beauvoir the 5th` review passed in `threads/03-block-product-reduction/review-a2-adapted-product-difference-loss-comparison-finite-integral.md`; the comparison with `loss` is supplied, not proved; no original DLN/statistical loss identification, product-chart construction, source coverage, Jacobian/prior transport, residual proof, normal crossings, pole order, or RLCT |
| Adapted loss-comparison continuous-density finite-integral helper | A2 conditional p.13 density-bound removal | PDF p. 13 via supplied product density | adapted-loss comparison finite-integral handoff; positive continuous product density; residual source hypotheses | reproduced at `threads/03-block-product-reduction/reproduction-a2-adapted-loss-comparison-continuous-density-finite-integral.md`; statement card `threads/03-block-product-reduction/statement-card-a2-adapted-loss-comparison-continuous-density-finite-integral.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; shrinks `R <= Rmax` and delegates to the fixed-radius adapted-loss bridge | xhigh `Poincare the 5th` accepted only as helper in `threads/03-block-product-reduction/review-a2-adapted-loss-comparison-continuous-density-finite-integral.md`; no density/Jacobian transport, product chart, residual proof, original-loss comparison, normal crossings, pole order, or RLCT |
| Continuous-edge signed-box adapted-loss finite-integral front end | A2 composed p.13 local finite-integral front end | PDF p. 13 via supplied signed-box residual chart and supplied adapted-loss comparison | global `Continuous Cedge`; signed-box residual source theorem; positive continuous product density; product-coordinate adapted lower bound; supplied `c0 * adapted <= loss` | reproduced at `threads/03-block-product-reduction/reproduction-a2-continuous-edge-signed-box-adapted-loss-finite-integral.md`; statement card `threads/03-block-product-reduction/statement-card-a2-continuous-edge-signed-box-adapted-loss-finite-integral.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; derives source measurability and edge-matrix measurability from global continuity, residual source hypotheses from signed-box data, density bounds from continuity, and loss lower bound from adapted comparison | xhigh `Poincare the 5th` review passed in `threads/03-block-product-reduction/review-a2-continuous-edge-signed-box-adapted-loss-finite-integral.md`; all chart/pushforward/residual/density/adapted-loss hypotheses remain supplied; no product chart, original-loss comparison, normal crossings, pole order, or RLCT |
| Edge-matrix signed-box adapted/original loss finite-integral front end | A2 measurable-edge p.13 local finite-integral front end | PDF p. 13 via supplied signed-box residual chart and supplied product-coordinate adapted lower bound | fixed-base edge-matrix measurability; finite matrix exact-rank measurability; weighted signed-box residual source theorem; positive continuous product density; product-coordinate adapted lower bound; endpoint loss comparison for original `lossDLN` consumer | reproduced at `threads/03-block-product-reduction/reproduction-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md`; statement card `threads/03-block-product-reduction/statement-card-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md` | `measurableSet_matrix_rank_eq_of_measurable_finite` proved in `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`; `measurableSet_paperEndpointFixedBaseEdgeRankStratum_of_measurable_edgeMatrix` and `measurableSet_paperEndpointFixedBaseSourceRankStratum_of_measurable_edgeMatrix` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`; edge-matrix adapted-loss theorem proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; original square-Frobenius consumer `...lossDLN_chainMapMatrixTuple...edgeMatrix_adaptedProductDifferenceSquareSum_lower...` proved in `lean/DLNFibre/DLN/Aoyagi/OriginalLossLocalMeasure.lean` | xhigh `Copernicus the 5th` review passed in `threads/03-block-product-reduction/review-a2-edge-matrix-signed-box-adapted-loss-finite-integral.md`; signed-box chart/pushforward, residual monomial lower bound, source-density bounds, positive continuous product density, and product-coordinate adapted lower bound remain supplied; no product chart, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Product-coordinate adapted lower-bound socket | A2 conditional independent regular-fiber lower-bound bridge | PDF p. 13 | positive regular radius; product-coordinate square-sum shape; cleaned-to-literal p.13 comparison; product-reduction certificates; positive uniform triangular multiplier bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-product-coordinate-adapted-lower-bound-socket.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-coordinate-adapted-lower-bound-socket.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; derives the `hadapted_lower` shape from supplied independent `u` product-coordinate shape, direct `S <= 2*L`, certificate, `0 < Kmul`, and multiplier bound with that `Kmul` | xhigh Faraday review passed after adding `0 < Rmax` and correcting notes to say `F2/F3` smallness is not exposed here; review at `threads/03-block-product-reduction/review-a2-product-coordinate-adapted-lower-bound-socket.md`; no product chart, source coverage, signed-box transport, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Product-family assumption-reduction sockets | A2 conditional product-family coordinate bridges | PDF p. 13 | p.13 regular-coordinate tags; finite cleaned/literal comparison under `F2/F3` smallness; cleaned square-sum split; supplied product component coordinate identities | reproduced at `threads/03-block-product-reduction/reproduction-a2-product-family-assumption-reduction-sockets.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-family-assumption-reduction-sockets.md` | `paperEndpointFixedBaseRegularBlockF2F3SquareSum`, `PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_squareSum_le_two_mul_literalProductDifferenceCoordinateMap_squareSum_of_regularBlockF2F3SquareSum_le_one`, `..._nhdsWithin_source_prod_of_regularBlockF2F3SquareSum_le_one`, `productCoordinateShape_nhdsWithin_source_of_regular_residual_coordinateMap_eq`, `exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_productCoordinateShape_regularBlockF2F3Small_nhdsWithin_source`, and `exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularBlockF2F3Small_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; reduces direct socket assumptions to concrete product-family `F2/F3` smallness and component identities | xhigh Gauss and Gibbs reviews passed in `threads/03-block-product-reduction/review-a2-product-family-assumption-reduction-sockets.md`; no construction of `CedgeProd`, analytic chart, source coverage, signed-box pushforward, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Product-family radius-derived `F2/F3` smallness | A2 conditional product-family coordinate bridge | PDF p. 13 plus Euclidean finite square-sum | literal regular-coordinate identity `regularBlock(CedgeProd(x,u)) = u`; regular ball membership; `Rmax <= 1`; `0 < Rmax` carried by the final wrapper as an interface/nonvacuity condition; residual identity/certificates/positive multiplier bound for final wrapper | appended to `threads/03-block-product-reduction/reproduction-a2-product-family-assumption-reduction-sockets.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-family-assumption-reduction-sockets.md` | `aoyagiCoordinateSquareSum_le_one_of_mem_ball_le_one`, `AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_add_le_coordinateSquareSum`, `PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseRegularBlockF2F3SquareSum_le_regularBlockCoordinateMap_squareSum`, `...F2F3SquareSum_le_one_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one`, `...F2F3SquareSum_eventually_le_one_nhdsWithin_source_of_regularBlockCoordinateMap_eq_of_mem_ball_le_one`, and `...exists_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_of_regular_residual_coordinateMap_eq_regularRadius_le_one_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; removes explicit `F2/F3` smallness when regular coordinates are literally `u` and `Rmax <= 1`, while the final wrapper still takes `0 < Kmul` and its multiplier bound | xhigh Hubble/Wegener scout checks and Peirce review passed in `threads/03-block-product-reduction/review-a2-product-family-assumption-reduction-sockets.md`; no product-family construction, hidden linear-coordinate norm comparison, analytic chart, source coverage, signed-box transport, density/Jacobian transport, normal-crossing, pole-order, or RLCT claim |
| Fixed-base product-family coordinate readout | A2 finite product-family coordinate bridge | PDF p. 13 | product-family transformed-edge block shapes; fixed endpoint bases; matrix-level suffix-field theorem; finite coordinate readout | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-product-family-coordinate-readout.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-product-family-coordinate-readout.md` | `paperEndpointFixedBaseRegularBlockCoordinateMap_eq_of_suffixState_fields`, `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_of_suffixState_D`, `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_suffixState_fields`, `paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdges_succSucc`, and `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdges_succSucc` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; the fixed-base product-difference coordinate map reads as `value(Ctop - I, F2, F3, residualProduct EMat last 0)` for at-least-two-edge chains | controller review recorded in `threads/03-block-product-reduction/review-a2-fixed-base-product-family-coordinate-readout.md`; no concrete `CedgeProd`, no proof of transformed-edge realization, no source coverage, signed-box pushforward, density/Jacobian transport, analytic chart, normal crossings, pole order, or RLCT |
| Fixed-base single-edge product-family coordinate readout | A2 finite product-family coordinate bridge | PDF p. 13 | single-edge product-family transformed block; fixed endpoint bases; matrix-level one-edge suffix theorem; finite coordinate readout | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-single-edge-product-family-coordinate-readout.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-single-edge-product-family-coordinate-readout.md` | `paperEndpointFixedBaseSuffixState_fields_of_productFamily_transformedEdge_one`, `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productFamily_transformedEdge_one`, and `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrix_one` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; the single-edge fixed-base product-difference coordinate map reads as `value(Ctop - I, F2, F3, C0)` | controller review recorded in `threads/03-block-product-reduction/review-a2-fixed-base-single-edge-product-family-coordinate-readout.md`; no product-coordinate matrix family, no proof of transformed-edge production, no parameter-continuity, product chart, source coverage, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Fixed-base prescribed edge-matrix realisation | A2 finite product-family constructor support | PDF p. 13 | fixed endpoint bases; Mathlib matrix-to-linear-map inverse; finite-dimensional continuity of linear maps; product-family coordinate readout | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-prescribed-edge-matrix-realisation.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-prescribed-edge-matrix-realisation.md` | `paperEndpointFixedBaseReverseEdgeFamilyOfMatrices`, `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_reverseEdgeFamilyOfMatrices`, `paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices`, `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices`, and `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_prescribedProductFamilyEdgeMatrices_succSucc` proved in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean` and `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; prescribed matrices `G` can be realised by continuous fixed-base edges and read through p.13 coordinates when `G` satisfies transformed-edge shapes | controller review recorded in `threads/03-block-product-reduction/review-a2-fixed-base-prescribed-edge-matrix-realisation.md`; pointwise only; no construction of `G(x,u)`, no proof of transformed-edge shapes, no parameter-continuity, product chart, source coverage, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Fixed-base raw product-coordinate edge matrices | A2 finite product-coordinate matrix bridge | PDF p. 13 | raw p.13 right/middle/left and single-edge edge-matrix patterns; suffix-state `B=0` tail invariant; fixed endpoint bases; finite coordinate readout | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-product-coordinate-edge-matrices.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-product-coordinate-edge-matrices.md` | `ChartLocalSuffixState.productCoordinateRightEndpointMatrix`, `productCoordinateMiddleMatrix`, `productCoordinateLeftEndpointMatrix`, `productCoordinateSingleEdgeMatrix`, `suffixState_tail_fields_of_productCoordinateEdges`, `suffixState_productCoordinate_fields_one`, `suffixState_productCoordinate_fields_succSucc`, `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdgeMatrix_one`, and `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_of_productCoordinateEdges_succSucc` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean` and `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; raw p.13 edge shapes feed the readouts `value(Ctop - I,F2,F3,C0)` and `value(Ctop - I,F2,F3,residualProduct EMat last 0)` | xhigh Laplace/Ptolemy checks recorded in `threads/03-block-product-reduction/review-a2-fixed-base-product-coordinate-edge-matrices.md`; no dependent product-family `G(x,u)`, no parameter-continuity, no source coverage, no signed-box pushforward, no density/Jacobian transport, no normal crossings, pole order, or RLCT |
| Regular coordinate-vector block reconstruction | A2 finite product-coordinate constructor support | PDF p. 13 | tagged regular-coordinate index; scalar coordinate family or Euclidean regular-coordinate vector | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-coordinate-vector-block-reconstruction.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-coordinate-vector-block-reconstruction.md` | `AoyagiRegularBlockCoordinateIndex.ctopMinusIdentityMatrix`, `ctopMatrix`, `f2Matrix`, `f3Matrix`, `ctopMatrix_sub_one`, `value_coordinateMatrices`, `exists_value_eq`, `value_euclideanCoordinateMatrices`, and `value_euclideanCtopMatrixCoordinateMatrices` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; any desired regular coordinate vector can be repackaged as blocks `Ctop-I`, `F2`, and `F3`, and also as `Ctop=I+X`, whose `value` readout is exactly that vector | xhigh Laplace/Ptolemy checks recorded in `threads/03-block-product-reduction/review-a2-regular-coordinate-vector-block-reconstruction.md`; no residual choice, edge-matrix assembly, raw edge-pattern proof, parameter-continuity, product chart, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Single-edge product-coordinate family constructor | A2 finite product-coordinate constructor support | PDF p. 13 | regular coordinate-vector block reconstruction; residual matrix coordinate reconstruction; raw single-edge p.13 matrix readout; fixed-base prescribed edge realisation; suffix residual-product bridge; pointwise source-dependent residual matrix wrapper and continuity under supplied `Continuous Dbase` | reproduced at `threads/03-block-product-reduction/reproduction-a2-single-edge-product-coordinate-family-constructor.md`, `threads/03-block-product-reduction/reproduction-a2-single-edge-residual-product-realisation.md`, and `threads/03-block-product-reduction/reproduction-a2-single-edge-source-dependent-residual-matrix-family.md`; statement cards `threads/03-block-product-reduction/statement-card-a2-single-edge-product-coordinate-family-constructor.md`, `threads/03-block-product-reduction/statement-card-a2-single-edge-residual-product-realisation.md`, and `threads/03-block-product-reduction/statement-card-a2-single-edge-source-dependent-residual-matrix-family.md` | `AoyagiResidualBlockCoordinateIndex.matrix`, `AoyagiResidualBlockCoordinateIndex.value_matrix`, `AoyagiResidualBlockCoordinateIndex.exists_value_eq`, `AoyagiProductDifferenceCoordinateIndex.value_euclideanCtopMatrixCoordinateMatrices_residual`, `ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq`, `continuous_productCoordinateSingleEdgeMatrix`, `paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean`, `paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq`, `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_singleEdgeProductCoordinateEuclidean`, `paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean`, `paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeProductCoordinateEuclidean_residualMatrix`, and `continuousAt_paperEndpointFixedBaseSingleEdgeProductCoordinateEdgeFamilyOfResidualMatrixEuclidean` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`, `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`, and `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; for a Euclidean regular vector `u` and residual matrix `D`, the raw one-edge p.13 matrix `[Ctop,-Ctop F2; -F3 Ctop, D + F3 Ctop F2]` has cleaned product-difference readout `u` on regular coordinates and `value D` on residual coordinates, and its transformed suffix residual product is `D`; the source-dependent wrapper replaces `D` pointwise by `Dbase x` and is continuous at `(x₀,u₀)` if `Dbase` is continuous; all coordinate readouts require `IsUnit Ctop.det` | controller review recorded in `threads/03-block-product-reduction/review-a2-single-edge-product-coordinate-family-constructor.md`; xhigh/controller reviews recorded in `threads/03-block-product-reduction/review-a2-single-edge-residual-product-realisation.md` and `threads/03-block-product-reduction/review-a2-single-edge-source-dependent-residual-matrix-family.md`; no construction of `Dbase`, no source chart/source coverage, no multi-edge arbitrary-terminal-residual theorem, no product chart, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Single-edge selected-entry product-coordinate readout | A2 finite selected-entry readout support | PDF p. 13 | one-edge source-dependent residual matrix wrapper; selected-entry center chart map; explicit residual-coordinate equivalence; determinant-chart hypothesis | reproduced at `threads/03-block-product-reduction/reproduction-a2-single-edge-selected-entry-product-coordinate-readout.md`; statement card `threads/03-block-product-reduction/statement-card-a2-single-edge-selected-entry-product-coordinate-readout.md` | `paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean`, `paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean`, and `continuousAt_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEdgeFamilyEuclidean` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`; the residual matrix is `AoyagiResidualBlockCoordinateIndex.matrix (fun c => SelectedEntrySignedBox.CenterCoord.chartMap pivot y (residualCoordEquiv c))`, so the one-edge readout gives regular coordinates `u` and residual coordinates equal to the selected-entry chart coordinates after the supplied equivalence | xhigh Carver/Helmholtz scouts and controller review recorded in `threads/03-block-product-reduction/review-a2-single-edge-selected-entry-product-coordinate-readout.md`; one-edge finite coordinate algebra only; explicit `residualCoordEquiv` and `IsUnit Ctop.det`; no inverse chart, source coverage, source-measure transport, multi-edge arbitrary-terminal-residual theorem, normal crossings, pole order, or RLCT |
| Single-edge selected-entry square-sum readout | A2 finite selected-entry scalar residual socket | PDF p. 13 | one-edge selected-entry product-coordinate readout; supplied residual-coordinate equivalence; determinant-chart hypothesis; finite square-sum reindexing | reproduced at `threads/03-block-product-reduction/reproduction-a2-single-edge-selected-entry-square-sum-readout.md`; statement card `threads/03-block-product-reduction/statement-card-a2-single-edge-selected-entry-square-sum-readout.md` | `aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_singleEdgeSelectedEntryProductCoordinateEuclidean` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`; it composes the one-edge residual-coordinate readout with `aoyagiCoordinateSquareSum_comp_equiv` and `SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap` | controller review recorded in `threads/03-block-product-reduction/review-a2-single-edge-selected-entry-square-sum-readout.md`; one-edge source-neutral finite algebra only; explicit `residualCoordEquiv` and `IsUnit Ctop.det`; no source coverage, source-measure transport, local lower bound, multi-edge selected-entry product, normal crossings, pole order, or RLCT |
| Single-edge selected-entry determinant-ball readout | A2 finite determinant-chart/readout support | PDF p. 13 | `Ctop` determinant-neighborhood theorem; one-edge selected-entry coordinate and square-sum readouts; supplied residual-coordinate equivalence | reproduced at `threads/03-block-product-reduction/reproduction-a2-single-edge-selected-entry-determinant-ball-readout.md`; statement card `threads/03-block-product-reduction/statement-card-a2-single-edge-selected-entry-determinant-ball-readout.md` | `exists_pos_radius_le_forall_paperEndpointFixedBaseSingleEdgeSelectedEntryProductCoordinateEuclidean_readout` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`; for any `0<Rmax`, it chooses `0<R<=Rmax` so that all `u` in `Metric.ball 0 R` satisfy regular readout, residual-coordinate readout, and scalar selected-entry residual square-sum readout | controller review recorded in `threads/03-block-product-reduction/review-a2-single-edge-selected-entry-determinant-ball-readout.md`; one-edge local determinant-neighborhood algebra only; explicit `residualCoordEquiv`; no source coverage, source-measure transport, local lower bound, multi-edge selected-entry product, normal crossings, pole order, or RLCT |
| Multi-edge residual-product preservation | A2 finite product-coordinate constructor support | PDF p. 13 | raw multi-edge p.13 edge matrix patterns; base transformed Schur residual blocks; residual-product congruence | reproduced at `threads/03-block-product-reduction/reproduction-a2-multi-edge-residual-product-preservation.md`; statement card `threads/03-block-product-reduction/statement-card-a2-multi-edge-residual-product-preservation.md` | `schurResidualBlock_fromBlocks_upperRight_zero`, `schurResidualBlock_fromBlocks_lowerLeft_zero`, `residualProduct_eq_of_residualBlock_eq`, `suffixState_tail_fields_of_productCoordinateEdges_from`, `residualBlock_productCoordinateEdges_succSucc`, and `residualProduct_productCoordinateEdges_succSucc_eq_base` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; for chains with at least two edges, choosing product-coordinate residual factors as the base transformed Schur residual blocks preserves the ordered residual product | controller review recorded in `threads/03-block-product-reduction/review-a2-multi-edge-residual-product-preservation.md`; no one-edge endpoint-collapse theorem, no dependent `G(x,u)` family, no parameter-continuity, product chart, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Residual-factor product two-edge unfold | A2 finite residual-factor product API | PDF p. 13; Case 2 pp. 19-22 as local two-factor motivation | explicit residual-factor product over `Fin 2`; canonical middle endpoint casts | reproduced at `threads/03-block-product-reduction/reproduction-a2-residual-factor-product-two-edge-unfold.md`; statement card `threads/03-block-product-reduction/statement-card-a2-residual-factor-product-two-edge-unfold.md` | `ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; `residualFactorProduct C (Fin.last 2) 0` unfolds to the right factor times the left factor after casting both to middle endpoint `(1 : Fin 3)` | xhigh source/API review recorded in `threads/03-block-product-reduction/review-a2-residual-factor-product-two-edge-unfold.md`; no concrete displayed Case 2 `Cfac`, no residual-index equivalence, no selected-entry matrix RHS identity, no source/image equality, no source-measure transport, no normal crossings, pole order, or RLCT |
| Case 2 residual-factor product reindex | A2 finite residual-factor/Case 2 bridge | PDF p. 13; Case 2 pp. 19-22 as local two-factor motivation | supplied two-edge residual-factor family; explicit endpoint equivalences; supplied factor identities for `D_{J+1}` and `C'_+` | reproduced at `threads/03-block-product-reduction/reproduction-a2-case2-residual-factor-product-reindex.md`; statement card `threads/03-block-product-reduction/statement-card-a2-case2-residual-factor-product-reindex.md` | `case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_submatrix` proved in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`; after `residualFactorProduct_fin_two_eq_mul`, `Matrix.submatrix_mul_equiv` reindexes the two factors to the existing `case2DisplayedPostPivotFreeTwoEdgeFactorProduct` | controller review recorded in `threads/03-block-product-reduction/review-a2-case2-residual-factor-product-reindex.md`; no construction of `Cfac`, no fixed-base endpoint equivalence, no selected-entry coordinate-matrix RHS identity, no source/image equality, no source-measure transport, no normal crossings, pole order, or RLCT |
| Case 2 residual-factor product selected-center matrix | A2 finite residual-factor/Case 2 bridge | PDF p. 13; Case 2 pp. 19-22 post-pivot lower product | supplied two-edge residual-factor family; explicit endpoint equivalences; supplied factor identities; supplied displayed selected-center RHS identity on post-pivot `(S,J+1)` domains | reproduced at `threads/03-block-product-reduction/reproduction-a2-case2-residual-factor-product-selected-center-matrix.md`; statement card `threads/03-block-product-reduction/statement-card-a2-case2-residual-factor-product-selected-center-matrix.md` | `Matrix.eq_of_submatrix_equiv_eq` and `residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_submatrix` proved in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`; the existing displayed-product submatrix bridge plus a supplied selected-center RHS equality imply the exact unreindexed `residualFactorProduct` matrix identity | xhigh bridge scout `Hypatia` and controller review recorded in `threads/03-block-product-reduction/review-a2-case2-residual-factor-product-selected-center-matrix.md`; displayed RHS remains supplied; no construction of `Cfac`, endpoint equivalences, source `Cprime`, source/image equality, source-measure transport, normal crossings, pole order, or RLCT |
| Case 2 residual-coordinate index pivot entries | A2 finite residual-index bookkeeping | PDF p. 13; Case 2 pp. 19-22 rectangular center | p.13 residual scalar-coordinate index; Case 2 row/column finite ranges; product selected-entry center | reproduced at `threads/03-block-product-reduction/reproduction-a2-case2-residual-coordinate-index-pivot-entries.md`; statement card `threads/03-block-product-reduction/statement-card-a2-case2-residual-coordinate-index-pivot-entries.md` | `case2ResidualBlockCoordinateIndexEquivPivotEntries` proved in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualIndex.lean`; the residual coordinate product index for `Case2ResidualRowIndex n S J` and `Case2ResidualColIndex n S J` is equivalent to `(case2ResidualBlockPivotEntries n S J : Type)` | xhigh source/API review recorded in `threads/03-block-product-reduction/review-a2-case2-residual-coordinate-index-pivot-entries.md`; no selected-entry chart construction, no fixed-base endpoint complement equivalence, no compatible `Cfac`, no selected-entry matrix RHS, no source/image equality, no source-measure transport, no normal crossings, pole order, or RLCT |
| Case 2 residual-coordinate endpoint-equivalence composition | A2 finite residual-index bookkeeping | PDF p. 13; Case 2 pp. 19-22 rectangular center | supplied endpoint row equivalence; supplied endpoint column equivalence; Case 2 product selected-entry center | reproduced at `threads/03-block-product-reduction/reproduction-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`; statement card `threads/03-block-product-reduction/statement-card-a2-case2-residual-coordinate-endpoint-equivalence-composition.md` | `case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs` and `case2ResidualBlockCoordinateIndexEquivPivotEntriesOfCase2EndpointEquivs` proved in `lean/DLNFibre/DLN/Aoyagi/Case2ResidualIndex.lean`; separate row/column endpoint equivalences compose with `case2ResidualBlockCoordinateIndexEquivPivotEntries` to produce the full residual-coordinate equivalence to `(case2ResidualBlockPivotEntries n S J : Type)`, in both useful orientations | controller review recorded in `threads/03-block-product-reduction/review-a2-case2-residual-coordinate-endpoint-equivalence-composition.md`; row/column endpoint equivalences remain supplied; no selected-entry chart construction, no compatible `Cfac`, no selected-entry matrix RHS, no source/image equality, no source-measure transport, no normal crossings, pole order, or RLCT |
| Multi-edge product-coordinate family constructor | A2 finite product-coordinate constructor support | PDF p. 13 | regular coordinate-vector block reconstruction; raw multi-edge p.13 edge matrix readout; multi-edge residual-product preservation; fixed-base prescribed edge realisation | reproduced at `threads/03-block-product-reduction/reproduction-a2-multi-edge-product-coordinate-family-constructor.md`; statement card `threads/03-block-product-reduction/statement-card-a2-multi-edge-product-coordinate-family-constructor.md` | `paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean` and `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_multiEdgeProductCoordinateEuclidean` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; for chains with at least two edges, a Euclidean regular vector `u` and fixed base edge matrices `Ebase` determine raw p.13 matrices whose cleaned fixed-base readout is `u` on regular coordinates and `value(residualProduct Ebase last 0)` on residual coordinates under `IsUnit Ctop.det` | controller review recorded in `threads/03-block-product-reduction/review-a2-multi-edge-product-coordinate-family-constructor.md`; no source-dependent `G(x,u)` wrapper, no parameter-continuity, product chart, source coverage, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Fixed-base residual-factor family constructor | A2 finite product-coordinate constructor support | PDF p. 13 | raw multi-edge p.13 right/middle/left matrix patterns; supplied compatible residual factors; explicit residual-factor product API | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-residual-factor-family-constructor.md` | `paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean`, `..._residualBlock_eq`, and `..._residualProduct_eq_residualFactorProduct` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; a supplied finite factor family `Cfac` is realized as the transformed Schur residual blocks of the fixed-base raw p.13 matrix family, and the suffix residual product is `residualFactorProduct Cfac last 0` | controller review recorded in `threads/03-block-product-reduction/review-a2-fixed-base-residual-factor-family-constructor.md`; no construction of `Cfac`, no selected-entry factor-product identity, no residual-index equivalence, no source/image equality, no source-measure transport, no normal crossings, pole order, or RLCT |
| Selected-entry residual-factor constructor readout | A2 finite selected-entry readout support | PDF p. 13 with pp. 19-22 as conditional compatible-factor motivation | fixed-base residual-factor constructor; supplied `uBase`; supplied `Cfac`; supplied selected-entry factor-product identity; supplied residual-index equivalence | reproduced at `threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-factor-constructor-readout.md`; statement card `threads/03-block-product-reduction/statement-card-a2-selected-entry-residual-factor-constructor-readout.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualFactorProduct_eq_matrix` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean`; it realizes the fixed-base matrices from `paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfResidualFactorsEuclidean`, rewrites their suffix residual product to `residualFactorProduct (Cfac (chartMap pivot y)) last 0`, and applies the prescribed-matrix readout bridge | xhigh source/API review recorded in `threads/03-block-product-reduction/review-a2-selected-entry-residual-factor-constructor-readout.md`; no construction of `Cfac`, no factor-product selected-entry proof, no residual-index equivalence construction, no source/image equality, no source-measure transport, no normal crossings, pole order, or RLCT |
| Multi-edge source-dependent product-coordinate family | A2 finite product-coordinate constructor support | PDF p. 13 | fixed-base matrix realisation; fixed-`Ebase` multi-edge constructor; residual coordinate map equals suffix residual product | reproduced at `threads/03-block-product-reduction/reproduction-a2-multi-edge-source-dependent-product-coordinate-family.md`; statement card `threads/03-block-product-reduction/statement-card-a2-multi-edge-source-dependent-product-coordinate-family.md` | `paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct`, `paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point`, `paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point`, `paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean`, and `paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; at each `(x,u)`, the product family built from `CedgeBase x` has regular coordinates `u` and residual coordinates equal to the base residual coordinate map, under `IsUnit Ctop.det` | controller review recorded in `threads/03-block-product-reduction/review-a2-multi-edge-source-dependent-product-coordinate-family.md`; no one-edge wrapper, determinant-neighborhood theorem, parameter-continuity, product chart, source coverage, density/Jacobian transport, normal crossings, pole order, or RLCT |
| `Ctop` determinant neighborhood for product coordinates | A2 finite determinant-chart support | PDF p. 13 | regular coordinate-vector block reconstruction; determinant continuity; openness of real units | reproduced at `threads/03-block-product-reduction/reproduction-a2-ctop-determinant-neighborhood.md`; statement card `threads/03-block-product-reduction/statement-card-a2-ctop-determinant-neighborhood.md` | `AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean`, `continuous_det_ctopMatrix_euclidean`, `ctopMatrix_zero`, `ctopMatrix_euclidean_zero`, `det_ctopMatrix_zero`, `det_ctopMatrix_euclidean_zero`, `isUnit_det_ctopMatrix_euclidean_zero`, `eventually_isUnit_det_ctopMatrix_euclidean_nhds_zero`, `exists_pos_ball_forall_isUnit_det_ctopMatrix_euclidean`, and `exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; for sufficiently small Euclidean regular-coordinate vectors, the explicit product-coordinate hypothesis `IsUnit(det(Ctop(u)))` holds | controller and xhigh audits recorded in `threads/03-block-product-reduction/review-a2-ctop-determinant-neighborhood.md`; no product-family continuity, source coverage, rank-stratum openness, product chart, signed-box pushforward, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Residual-block continuity support | A2 finite topology/product-coordinate support | PDF pp. 11-13, especially p. 13 | suffix-state field continuity; Schur complement continuity on determinant charts; fixed-base matrix-coordinate continuity | reproduced at `threads/03-block-product-reduction/reproduction-a2-residual-block-continuity-support.md`; statement card `threads/03-block-product-reduction/statement-card-a2-residual-block-continuity-support.md` | `continuous_productCoordinateRightEndpointMatrix`, `continuous_productCoordinateMiddleMatrix`, `continuous_productCoordinateLeftEndpointMatrix`, `continuousAt_chartLocalSuffixState_residualBlock`, and `continuousAt_chartLocalSuffixState_residualProduct` proved in `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`; `paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt` and `paperEndpointFixedBaseContinuousEdges_residualBlock_continuousAt` proved in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`; `continuous_f2Matrix_euclidean` and `continuous_f3Matrix_euclidean` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean` | controller and xhigh audits recorded in `threads/03-block-product-reduction/review-a2-residual-block-continuity-support.md`; recursive determinant-chart hypotheses remain explicit; no full product-family continuity, product chart, source coverage, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Original loss local-measure handoff | A2 concrete original `lossDLN` local finite-integral front end | PDF p. 13 via supplied p.13 product-coordinate data plus finite endpoint basis comparison | endpoint loss comparison; adapted-loss continuous-density helper; continuous-edge signed-box adapted-loss front end; signed-box residual and density hypotheses; product-coordinate adapted lower bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-original-loss-local-measure.md`; statement card `threads/03-block-product-reduction/statement-card-a2-original-loss-local-measure.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density` and `..._of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density` proved in `lean/DLNFibre/DLN/Aoyagi/OriginalLossLocalMeasure.lean`; removes the supplied `c0 * adapted <= loss` hypothesis for original square-Frobenius `lossDLN` on chain-map tuples; edge-matrix variant now also available via the edge-matrix front-end row | xhigh Feynman review passed in `threads/03-block-product-reduction/review-a2-original-loss-local-measure.md`; chart/pushforward, residual lower bound, product-density, and adapted product-coordinate lower bound remain supplied; no arbitrary-tuple, statistical/KL/covariance, density/Jacobian, normal-crossing, pole-order, or RLCT claim |
| Signed-box residual source finite-integral bridge | A2 p.13 finite-integral source-hypothesis bridge | PDF p. 13 via supplied signed-box residual chart | weighted signed-box source pushforward; residual monomial lower bound; source-density a.e.-measurability/nonnegativity and monomial upper bound; fixed-basis edge-matrix measurability; source-stratum measurability; `0 < t`; p.13 local loss/density bounds | reproduced at `threads/03-block-product-reduction/reproduction-a2-signed-box-residual-source-finite-integral-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-signed-box-residual-source-finite-integral-bridge.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; composes the measurable-edge weighted signed-box residual-source constructor with the existing p.13 local finite-integral theorem | xhigh `Russell the 5th` review passed after doc-boundary fixes in `threads/03-block-product-reduction/review-a2-signed-box-residual-source-finite-integral-bridge.md`; no chart construction, pushforward proof, density/Jacobian transport, original-loss comparison, normal crossings, pole order, or RLCT |
| Signed-box residual continuous-density finite-integral bridge | A2 p.13 radius-shrinking source/density bridge | PDF p. 13 via supplied signed-box residual chart and supplied transported density | weighted signed-box source pushforward; residual monomial lower bound; source-density a.e.-measurability/nonnegativity and monomial upper bound; fixed-basis edge-matrix measurability; source-stratum measurability; `0 < t`; product-density continuity/positivity at `(x₀,0)`; p.13 local loss lower bound | reproduced at `threads/03-block-product-reduction/reproduction-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-signed-box-residual-continuous-density-finite-integral-bridge.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; composes the measurable-edge weighted signed-box residual-source constructor with the positive-continuous-density p.13 local finite-integral theorem | xhigh `Aristotle the 5th` review passed after statement-card radius-bound fix in `threads/03-block-product-reduction/review-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`; no chart construction, pushforward proof, density/Jacobian transport, original-loss comparison, normal crossings, pole order, or RLCT |
| Continuous-edge signed-box continuous-density finite-integral bridge | A2 p.13 continuity-to-measurability bridge | PDF p. 13 via supplied continuous edge family and signed-box residual chart | global `Continuous Cedge`; source-rank-stratum measurability theorem; endpoint fixed-basis matrix continuity; signed-box source pushforward; residual/source-density/product-density/loss hypotheses | reproduced at `threads/03-block-product-reduction/reproduction-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; derives `hsource_meas` and `hEdgeMatrix` from global continuity, then delegates to the signed-box continuous-density bridge | xhigh `Sartre the 5th` review passed after reproduction-note `0 < t` fix in `threads/03-block-product-reduction/review-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`; no source-rank openness, no derivation from only `ContinuousAt Cedge x₀`, no raw `Measurable Cedge` API, no chart construction, no density/Jacobian transport, no original-loss comparison, no normal crossings, pole order, or RLCT |
| Local-source signed-box and monomial-unit finite-integral boundary | A2 local p.13 signed-box source boundary | PDF p. 13 for finite block/product residual algebra; signed-box chart/pushforward remains supplied | measurable local source set; local source chart and weighted signed-box pushforward; residual and density monomial-unit identities or bounds; local source-filter loss and transported-density bounds; fixed-base edge-matrix measurability | reproduced at `threads/03-block-product-reduction/reproduction-a2-local-source-signed-box-monomial-unit-boundary.md`; statement card `threads/03-block-product-reduction/statement-card-a2-local-source-signed-box-monomial-unit-boundary.md` | `exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds`, `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource`, `signedBox_monomialLower_sourceDensityBounds_of_monomialUnits`, and `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; replaces the global source-rank front end by an explicit local source and derives the residual lower/source-density hypotheses from bounded monomial units | xhigh source and Lean-boundary audits recorded in `threads/03-block-product-reduction/review-a2-local-source-signed-box-monomial-unit-boundary.md`; no local chart construction, source coverage, pushforward proof, density/Jacobian formula, normal crossings, pole order, or RLCT |
| Local-source monomial-unit finite-integral wrapper | A2 supplied local residual chart consumer | PDF p. 13 for finite block/product residual algebra; signed-box chart/pushforward remains supplied | measurable local source set; local source chart and weighted signed-box pushforward; residual/source-density monomial-unit identities; unit bounds; local source-filter loss and transported-density bounds; fixed-base edge-matrix measurability | reproduced at `threads/03-block-product-reduction/reproduction-a2-local-source-monomial-unit-finite-integral-wrapper.md`; statement card `threads/03-block-product-reduction/statement-card-a2-local-source-monomial-unit-finite-integral-wrapper.md` | `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; composes the monomial-unit inequality package with the local-source signed-box finite-integral theorem so future chart packages can supply unit identities directly | xhigh source audit and Lean/API audit recorded in `threads/03-block-product-reduction/review-a2-local-source-monomial-unit-finite-integral-wrapper.md`; no local chart construction, source coverage, pushforward proof, density/Jacobian formula, concrete monomial-unit production, normal-crossing extraction, pole order, or RLCT |
| Source-stratum local-subset local-source finite-integral consumer | A2 conditional source-stratum finite-integral handoff | PDF p. 13 motivates the p.13 finite-integral socket; theorem itself is measure bookkeeping | measurable local source set; open local inclusion `Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource`; residual positivity/integrability and loss/density bounds on `localSource`; `[SFinite μ]` for product-restriction comparison | reproduced at `threads/03-block-product-reduction/reproduction-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`; statement card `threads/03-block-product-reduction/statement-card-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md` | `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; calls the local-source p.13 theorem, shrinks the returned open set by `Ulocal`, and compares restricted product measures | xhigh scout boundary review recorded in `threads/03-block-product-reduction/review-a2-source-stratum-local-subset-local-source-finite-integral-consumer.md`; no proof of the local inclusion, no source coverage, source/image equality, raw-Haar pushforward, source-measure transport, density/Jacobian identity, normal crossings, pole order, or RLCT |
| Selected-entry signed-box monomial-unit data | A2 finite selected-entry chart-side data | PDF pp. 19-22 for Case 2 selected-entry blow-up; uses existing A4 reproduction notes; no chart/source production claim | finite center and pivot; selected-entry square-sum factorization; formal pivot-first determinant; signed-box monomial-unit consumer | reproduced at `threads/03-block-product-reduction/reproduction-a2-selected-entry-signed-box-monomial-unit-data.md`; statement card `threads/03-block-product-reduction/statement-card-a2-selected-entry-signed-box-monomial-unit-data.md` | `SelectedEntrySignedBox.residual_eq_unit_mul_abs_monomial`, `SelectedEntrySignedBox.sourceDensity_eq_abs_pivotFirstJacobian_det`, `SelectedEntrySignedBox.sourceDensity_eq_unit_mul_abs_monomial`, `SelectedEntrySignedBox.monomialUnitHypotheses`, `SelectedEntrySignedBox.monomialLower_sourceDensityBounds`, `SelectedEntrySignedBox.CenterCoord.monomialUnitHypotheses`, and `SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxMeasure.lean`; supplies concrete selected-entry unit data with coordinate index `Option {i // i in center.erase pivot}` and a center-subtype API, both with constants `c = C = 1` | xhigh `Dewey the 6th` and `Locke the 6th` audits recorded in `threads/03-block-product-reduction/review-a2-selected-entry-signed-box-monomial-unit-data.md`; no analytic chart domains, source coverage, pushforward, analytic Jacobian/source-density transport, full loss comparison, normal crossings, pole order, or RLCT |
| Selected-entry local-source finite-integral handoff | A2 concrete selected-entry residual chart consumer | PDF p. 13 local-source finite-integral socket plus PDF pp. 19-22 selected-entry square-sum/Jacobian calculation | selected-entry center-coordinate monomial-unit data; supplied local source chart; supplied weighted pushforward; supplied residual-coordinate identification; fixed-base edge-matrix measurability; local source-filter loss and density bounds | reproduced at `threads/03-block-product-reduction/reproduction-a2-selected-entry-local-source-finite-integral-handoff.md`; statement card `threads/03-block-product-reduction/statement-card-a2-selected-entry-local-source-finite-integral-handoff.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean`; discharges the generic residual/density monomial-unit hypotheses and coordinatewise critical-exponent condition for the center-indexed selected-entry signed box, leaving chart/pushforward/source production explicit | controller review recorded in `threads/03-block-product-reduction/review-a2-selected-entry-local-source-finite-integral-handoff.md`; source chart construction, source image/coverage, weighted pushforward proof, analytic Jacobian/source-density transport, original-loss comparison, normal crossings, pole order, and RLCT remain open |
| Local-source adapted-loss finite-integral socket | A2 local p.13 adapted-loss consumer | PDF p. 13 as regular/product-coordinate motivation; theorem itself is finite comparison plumbing | measurable local source set; residual positivity/integrability on source; local adapted lower bound; local adapted-to-loss comparison; local density bounds | reproduced at `threads/03-block-product-reduction/reproduction-a2-local-source-adapted-loss-finite-integral-socket.md`; statement card `threads/03-block-product-reduction/statement-card-a2-local-source-adapted-loss-finite-integral-socket.md` | `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean`; local-source analogue of the existing adapted-loss socket, multiplying comparison constants and delegating to the local-source p.13 theorem | review recorded in `threads/03-block-product-reduction/review-a2-local-source-adapted-loss-finite-integral-socket.md`; no adapted lower-bound proof, original-loss comparison, chart construction, source coverage, density/Jacobian transport, normal crossings, pole order, or RLCT |
| Selected-entry finite-cover integral assembly | A2 finite selected-entry atlas gluing | PDF p. 13 for local finite-integral socket; selected-entry sector cover is finite coordinate geometry from Aoyagi-style selected-entry substitutions, not source coverage | per-pivot selected-entry chart-image finite-integral theorem; finite sector cover `signedBoxSet S subset union_p chartMap p '' signedBoxSet R`; finite product-measure lower-integral cover lemma; original-loss comparison for the `lossDLN` wrapper | reproduced at `threads/03-block-product-reduction/reproduction-a2-selected-entry-finite-cover-integral-assembly.md`; statement card `threads/03-block-product-reduction/statement-card-a2-selected-entry-finite-cover-integral-assembly.md` | `lintegral_prod_restrict_lt_top_of_subset_iUnion_finite` and `PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntrySignedBoxLocalMeasure.lean`; original-loss wrapper `...exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_selectedEntryCenter_signedBox_finiteCover_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryOriginalLossLocalMeasure.lean` | xhigh review recorded in `threads/03-block-product-reduction/review-a2-selected-entry-finite-cover-integral-assembly.md`; no source-rank-stratum equality, source/image equality, original source-measure transport, analytic source chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Source-stratum literal regular/residual square-sum comparison | A2 finite p.13 loss-shape comparison | PDF p. 13 | source-stratum literal/cleaned factor-2 comparison; cleaned regular/residual square-sum split | reproduced at `threads/03-block-product-reduction/reproduction-a2-source-stratum-literal-regular-residual-square-sum.md`; statement card `threads/03-block-product-reduction/statement-card-a2-source-stratum-literal-regular-residual-square-sum.md` | `PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_factor_two_nhdsWithin_source` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; finite real square-sum comparison on the source-rank `nhdsWithin` filter only | xhigh `Tesla the 4th` review passed in `threads/03-block-product-reduction/review-a2-regular-suspension-projections-and-loss-shape.md`; no analytic regular-coordinate status, no Fubini/polar theorem, no chart construction, no normal-crossing production, pole order, or RLCT |
| Regular square-suspension integrability target | A2 analytic target; finite-side supplied-bound wrappers partly Lean | PDF p. 13 as motivation for regular variables | product-coordinate lower loss comparison; bounded nonnegative density for the finite side; residual negative-power input; Fubini/fiber scaling | target statement at `threads/03-block-product-reduction/reproduction-a2-regular-square-suspension-integrability-target.md`; bounded-density wrapper reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-square-bounded-density-wrapper.md` | finite threshold-shift sockets and bounded-density wrappers proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean` and `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean`; full p.13 theorem still has supplied chart/loss/density hypotheses | xhigh `Tesla the 4th` source scout recommended this as the next genuine analytic theorem; xhigh `Mendel the 4th` reviewed the bounded-density wrapper; no Aoyagi p.13 chart/density construction yet |
| One-sided finite-factor singular-integral preservation | A2 analytic brick | PDF p. 13 as motivation for adding regular variables; theorem itself is elementary measure theory | ENNReal monotonicity for `u ↦ u^s`, inverse order reversal, Tonelli product formula, finite extra measure | reproduced at `threads/03-block-product-reduction/reproduction-a2-one-sided-regular-suspension-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-one-sided-regular-suspension-integrability.md` | `lintegral_rpow_neg_add_right_le_prod_fst`, `lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top`, and restricted version proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; adding a nonnegative ENNReal term over a finite factor preserves finiteness of the pulled-back singular integral | xhigh `Copernicus the 4th` review passed in `threads/03-block-product-reduction/review-a2-one-sided-regular-suspension-integrability.md`; no threshold definition, no `+k/2` shift, no polar estimate, no density theorem, no p.13 analytic chart/Jacobian construction, no normal crossings, pole order, or RLCT |
| Punctured radial finite-side integrability | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary finite-dimensional radial analysis | additive Haar radial integrability API; one-dimensional `r^q` integrability on `(0,R)`; comparison `(r^2+a)^(-s) <= r^(-2s)` for `r>0`, `a>=0`, `s>=0`; real-integrability to `ENNReal.ofReal` handoff | reproduced at `threads/03-block-product-reduction/reproduction-a2-radial-finite-side-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-radial-finite-side-integrability.md` | `integrable_norm_rpow_neg_indicator_Ioo`, `integrable_norm_sq_add_rpow_neg_indicator_Ioo`, and `lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Ioo_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves only finite-side integrability on `1_(0,R)(||x||)` under `t<finrank` and `2*s<finrank` | xhigh `Volta the 4th` review passed in `threads/03-block-product-reduction/review-a2-radial-finite-side-integrability.md`; no ball/null-origin transfer, endpoint theorem, lower/divergence theorem, uniform asymptotic in `a`, density theorem, product-coordinate `+k/2` threshold, p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Null-origin radial integrability transfer | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary a.e. measure theory | no-atoms/null singleton; a.e. congruence from `(0,R)` radial support to `(-infinity,R)` radial support; pointwise open-ball/radial support rewrite | reproduced at `threads/03-block-product-reduction/reproduction-a2-null-origin-radial-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-null-origin-radial-integrability.md` | `ae_eq_norm_indicator_Ioo_Iio`, `integrable_norm_sq_add_rpow_neg_indicator_Iio`, `lintegral_ofReal_norm_sq_add_rpow_neg_indicator_Iio_lt_top`, `norm_sq_add_rpow_neg_indicator_ball_eq_indicator_Iio`, `integrable_norm_sq_add_rpow_neg_indicator_ball`, and `lintegral_ofReal_norm_sq_add_rpow_neg_indicator_ball_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; transfers finite-side integrability to nonpunctured radial and open-ball supports only up to a.e./pointwise support rewrites | xhigh review recorded in `threads/03-block-product-reduction/review-a2-null-origin-radial-integrability.md`; no pointwise origin regularity, closed-ball theorem, boundary-sphere nullity, endpoint theorem, lower/divergence theorem, uniform asymptotic in `a`, density theorem, product-coordinate `+k/2` threshold, p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Product below-critical regular-ball integrability | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary product-measure domination | finite base measure; a.e. nonnegative base term; no-atoms on regular Haar factor; domination by `a=0` regular-ball integrand; Tonelli/product integral for the majorant | reproduced at `threads/03-block-product-reduction/reproduction-a2-product-below-critical-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-below-critical-integrability.md` | `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves finite lower integral over `alpha x ball(0,R)` only under `2*s<finrank`, using an a.e. nonnegative base term and finite base measure | xhigh `Hypatia the 4th` review recorded in `threads/03-block-product-reduction/review-a2-product-below-critical-integrability.md`; no `+dim/2` threshold shift, no theorem for `s>=dim/2`, no endpoint, lower/divergence theorem, uniform asymptotic, density/prior theorem, p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Product bounded-away regular-ball integrability | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary product-measure domination away from the residual zero set | finite base measure; a.e. positive lower bound `epsilon <= a`; monotonicity of `t^(-s)` for `s>=0`; finite Haar measure of metric balls; Tonelli/product integral for the constant-ball majorant | reproduced at `threads/03-block-product-reduction/reproduction-a2-product-bounded-away-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-bounded-away-integrability.md`; threshold-shift route probe `threads/03-block-product-reduction/scout-a2-regular-square-threshold-shift-lean-route.md` | `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves finite lower integral over `alpha x ball(0,R)` for all `s>=0` when the base term is a.e. bounded below by a positive constant | xhigh `Hilbert the 4th` review passed in `threads/03-block-product-reduction/review-a2-product-bounded-away-integrability.md`; no singular-base theorem where `a` approaches zero, no `+dim/2` threshold shift, no endpoint, lower/divergence theorem, uniform asymptotic, density/prior theorem, p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Japanese-bracket supercritical integrability | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary finite-dimensional Haar integrability via Mathlib Japanese bracket | Mathlib `integrable_rpow_neg_one_add_norm_sq`; arithmetic `finrank/2<s -> finrank<2*s`; nonnegative lower-integral handoff; comparison with `min(a,1)*(1+||x||^2)` for fixed `a>0` | reproduced at `threads/03-block-product-reduction/reproduction-a2-japanese-bracket-supercritical-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-japanese-bracket-supercritical-integrability.md`; threshold-shift route probe `threads/03-block-product-reduction/scout-a2-regular-square-threshold-shift-lean-route.md` | `integrable_one_add_norm_sq_rpow_neg`, `lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top`, and `lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves global finiteness in the supercritical range and fixed-positive-parameter global finiteness | xhigh `Pauli the 4th` review passed in `threads/03-block-product-reduction/review-a2-japanese-bracket-supercritical-integrability.md`; no sharp `a^(finrank/2-s)` bound, no base-product theorem, no `+dim/2` threshold shift, no endpoint, lower/divergence theorem, uniform asymptotic, density/prior theorem, p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Sharp positive-parameter fiber scaling | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary Haar scaling and Japanese-bracket integrability | Haar scaling under scalar multiplication; substitution `u=sqrt(a) v`; positive real-power algebra; whole-space-to-ball monotonicity; Japanese-bracket finiteness for the final supercritical corollary | reproduced at `threads/03-block-product-reduction/reproduction-a2-sharp-positive-parameter-fiber-scaling.md`; statement card `threads/03-block-product-reduction/statement-card-a2-sharp-positive-parameter-fiber-scaling.md` | `lintegral_comp_inv_smul_eq_mul_addHaar`, `ofReal_add_norm_sq_pos_rpow_neg_eq_mul_one_add_norm_sq_inv_sqrt_smul`, `lintegral_ofReal_add_norm_sq_pos_rpow_neg_eq_scale`, `lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_le_scale`, and `lintegral_ofReal_add_norm_sq_pos_rpow_neg_indicator_ball_lt_top_of_supercritical` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves exact whole-space scaling and ball-restricted sharp bound for fixed `a>0` | xhigh `Socrates the 4th` review passed after low docstring/name fixes in `threads/03-block-product-reduction/review-a2-sharp-positive-parameter-fiber-scaling.md`; no variable-base product theorem, no proof of residual-base integrability of `a(x)^(dim/2-s)`, no full regular-variable threshold shift, no endpoint/lower theorem, no bounded-density/prior theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Variable-base product fiber integrability | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is elementary product-measure/fiber-bound integration | sharp fixed-positive-parameter fiber bound; Japanese-bracket finiteness; `lintegral_prod_le`; a.e. strict positivity of base parameter; finite base-power lower integral | reproduced at `threads/03-block-product-reduction/reproduction-a2-variable-base-product-fiber-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-variable-base-product-fiber-integrability.md` | `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_scale` and `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_of_base_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves product bound and finiteness from a.e. `0<a(x)`, `dim/2<s`, and finite `∫ ofReal(a(x)^(dim/2-s))`; no finite base measure or measurability hypothesis on `a` required | xhigh `Planck the 4th` review passed after low wording/name fixes in `threads/03-block-product-reduction/review-a2-variable-base-product-fiber-integrability.md`; no proof of the residual-base integrability hypothesis, no theorem for positive-measure zero set of `a`, no endpoint/lower theorem, no bounded-density/prior theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Residual-power threshold-shift bridge | A2 analytic brick | PDF p. 13 as motivation for regular square variables; theorem itself is the finite-side exponent substitution in the variable-base product theorem | variable-base product fiber integrability; substitution `s=t+dim/2`; arithmetic `dim/2-s=-t`; strict residual-power exponent `0<t` | reproduced at `threads/03-block-product-reduction/reproduction-a2-residual-power-threshold-shift-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-residual-power-threshold-shift-bridge.md` | `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale` and `lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; proves finite product integrability at exponent `t+dim/2` from a.e. `0<a(x)`, `0<t`, and finite `∫ ofReal(a(x)^(-t))`; no finite base measure or measurability hypothesis on `a` required | xhigh `Ampere the 4th` review passed after a low docstring fix in `threads/03-block-product-reduction/review-a2-residual-power-threshold-shift-bridge.md`; no proof that Aoyagi's reduced residual coordinates satisfy the residual negative-power hypothesis, no theorem for positive-measure zero set of `a`, no endpoint/lower theorem or threshold equality, no bounded-density/prior theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Residual square-sum integrability socket | A2 analytic/interface brick | PDF p. 13 residual square-loss motivation; theorem itself only specialises the finite-side product theorem to coordinate square-sums | residual-power threshold-shift bridge; `aoyagiCoordinateSquareSum`; residual block coordinate values | reproduced at `threads/03-block-product-reduction/reproduction-a2-residual-square-sum-integrability-socket.md`; statement card `threads/03-block-product-reduction/statement-card-a2-residual-square-sum-integrability-socket.md` | `lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_le_residual_power_scale`, `lintegral_ofReal_coordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top`, and `lintegral_ofReal_residualBlockSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_residual_power_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean`; specialises the square-model product estimate to finite coordinate square-sums and residual block square-sums while keeping positivity and base integrability explicit | xhigh `Nash the 4th` review passed after low wording fixes in `threads/03-block-product-reduction/review-a2-residual-square-sum-integrability-socket.md`; no proof that Aoyagi's reduced residual coordinates satisfy positivity or residual negative-power integrability, no theorem for positive-measure zero set, no endpoint/lower theorem or threshold equality, no bounded-density/prior theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Euclidean coordinate square-sum base integrability | A2 analytic base-case brick | PDF p. 13 residual square-loss motivation; theorem itself is elementary Euclidean/radial integrability for free coordinates | `EuclideanSpace.real_norm_sq_eq`; `finrank_euclideanSpace`; existing radial finite-side theorem; origin has measure zero for nonatomic measures; residual-power product socket | reproduced at `threads/03-block-product-reduction/reproduction-a2-euclidean-coordinate-square-sum-base-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-euclidean-coordinate-square-sum-base-integrability.md` | `aoyagiEuclideanCoordinateSquareSum_pos_of_ne_zero`, `ae_aoyagiEuclideanCoordinateSquareSum_pos`, `ae_aoyagiEuclideanCoordinateSquareSum_pos_restrict`, `lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_indicator_ball_lt_top`, `lintegral_ofReal_euclideanCoordinateSquareSum_rpow_neg_restrict_ball_lt_top`, and `lintegral_ofReal_euclideanCoordinateSquareSum_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean`; proves local base and product finiteness for the free Euclidean coordinate model under `R>0`, `0<=t`, and `2*t<card eta` | xhigh `Huygens the 4th` review passed with no findings in `threads/03-block-product-reduction/review-a2-euclidean-coordinate-square-sum-base-integrability.md`; no proof for Aoyagi's product residual `D=prod_s C^(s)`, no local equivalence between p.13 residual product coordinates and free coordinates, no zero-dimensional residual branch, no endpoint/lower theorem or threshold equality, no bounded-density/prior theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Negative-power lower-bound comparison | A2 analytic comparison brick | PDF p. 13 residual square-loss motivation; theorem itself is elementary real-power comparison | a.e. strict positivity of model loss; a.e. lower bound `c*a <= b` with `c>0`; monotonicity of negative real powers; constant extraction from lower integral | reproduced at `threads/03-block-product-reduction/reproduction-a2-negative-power-lower-bound-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-negative-power-lower-bound-comparison.md` | `lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean`; transfers finite `∫ ofReal(a^(-t))` to finite `∫ ofReal(b^(-t))` under a.e. `0<a`, a.e. `c*a<=b`, `c>0`, and `0<=t` | xhigh `Locke the 4th` review passed with only a verification-root note in `threads/03-block-product-reduction/review-a2-negative-power-lower-bound-comparison.md`; no lower-bound construction for Aoyagi's product residual, no monomial integrability theorem, no finite chart cover theorem, no bounded-density/prior theorem, no endpoint/lower theorem or threshold equality, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Positive-box monomial integrability | A2 analytic monomial base brick | PDF pp. 5-6 normal-crossing monomial exponent template; theorem itself is elementary product-measure integrability | one-dimensional `x^p` integrability on `(0,R)` for `-1<p`; finite product integrability; lower-integral handoff from Bochner integrability | reproduced at `threads/03-block-product-reduction/reproduction-a2-positive-box-monomial-integrability.md`; statement card `threads/03-block-product-reduction/statement-card-a2-positive-box-monomial-integrability.md` | `lintegral_ofReal_rpow_restrict_Ioo_lt_top`, `lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top`, `lintegral_ofReal_fintype_rpow_positiveBox_lt_top`, and `lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`; proves finite positive-box product integrability under `R_i>0` and strict inequalities `2*t*k_i<h_i+1`; imported by `lean/DLNFibre.lean` | xhigh `Lorentz the 4th` review passed with one low future-target caveat addressed in `threads/03-block-product-reduction/review-a2-positive-box-monomial-integrability.md`; no residual-loss lower-bound theorem, no density/prior upper-bound theorem, no signed-box absolute-value theorem, no endpoint/lower theorem or threshold equality, no finite chart cover theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Positive-box monomial domination | A2 analytic monomial comparison brick | PDF pp. 5-6 normal-crossing monomial exponent template; theorem itself is elementary lower-integral domination | positive-box monomial integrability; a.e. upper bound by a nonnegative constant multiple of the monomial product; lower-integral monotonicity and constant extraction | reproduced at `threads/03-block-product-reduction/reproduction-a2-positive-box-monomial-domination.md`; statement card `threads/03-block-product-reduction/statement-card-a2-positive-box-monomial-domination.md` | `lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top` and `lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`; transfers finite lower-integral control from the positive-box monomial model to any `f` satisfying the explicit a.e. upper bound | xhigh `Einstein the 4th` review passed in `threads/03-block-product-reduction/review-a2-positive-box-monomial-domination.md`; no residual-loss lower-bound theorem, no density/prior upper-bound theorem, no derivation from separate loss/density estimates, no signed-box absolute-value theorem, no endpoint/lower theorem or threshold equality, no finite chart cover theorem, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| Positive-box residual/density comparison | A2 analytic monomial comparison brick | PDF pp. 5-6 normal-crossing monomial exponent template; theorem itself is elementary positive-box comparison | positive-box coordinate positivity a.e.; loss lower bound by `c*prod x_i^(2*k_i)` with `c>0`; nonnegative density upper bound by `C*prod x_i^(h_i)` with `C>=0`; monomial domination theorem | reproduced at `threads/03-block-product-reduction/reproduction-a2-positive-box-residual-density-comparison.md`; statement card `threads/03-block-product-reduction/statement-card-a2-positive-box-residual-density-comparison.md` | `ae_forall_pos_measure_pi_restrict_Ioo`, `loss_rpow_neg_mul_density_le_const_mul_monomialFactor_of_pos`, and `lintegral_ofReal_loss_rpow_neg_mul_density_positiveBox_lt_top` proved in `lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean`; proves finite lower-integral control for `loss^(-t)*density` under explicit supplied positive-box loss/density bounds and strict inequalities `2*t*k_i<h_i+1` | xhigh `Gauss the 4th` review passed in `threads/03-block-product-reduction/review-a2-positive-box-residual-density-comparison.md`; low module-docstring caveat addressed; no signed-box/absolute-value theorem, no proof that Aoyagi's actual residual charts satisfy the supplied bounds, no analytic density/Jacobian transport theorem, no finite chart cover theorem, no endpoint/lower theorem or threshold equality, no p.13 analytic chart/Jacobian construction, normal crossings, pole order, or RLCT |
| One-step determinant-chart coordinate equivalence | A2 finite determinant-chart topology | PDF pp. 11-13, especially p. 13 one-step product-reduction variables | one-step raw/chart coordinate formulas; determinant-domain preservation; algebraic inverse identities; matrix-inversion continuity on determinant-unit loci | reproduced at `threads/03-block-product-reduction/reproduction-a2-one-step-determinant-chart-coordinate-equivalence.md`; statement card `threads/03-block-product-reduction/statement-card-a2-one-step-determinant-chart-coordinate-equivalence.md` | product-topology instances, determinant-chart subtype continuity lemmas, and `productReductionStepCoordinate_detChart_homeomorph` proved in `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`; finite topological coordinate equivalence only | xhigh `Herschel the 4th` review passed in `threads/03-block-product-reduction/review-a2-one-step-determinant-chart-coordinate-equivalence.md`; no analytic regularity, analytic Jacobian determinant calculation, source-rank openness, source coverage, ideal-germ transport, regular-suspension certificate, normal crossings, pole order, or RLCT |
| One-step A1 formal inverse | A2 finite coordinate algebra | PDF pp. 10-13, especially p. 13 one-step product-reduction variables | one-step raw/chart coordinate formulas; determinant-unit cancellation for retained `A1`; no inverse of passive `D` | reproduced at `threads/03-block-product-reduction/reproduction-a2-product-step-a1-formal-inverse.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-step-a1-formal-inverse.md` | `productReductionStepCoordinate_left_inverse_of_isUnit_A1` and `productReductionStepCoordinate_right_inverse_of_isUnit_A1` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; old determinant-chart inverse theorems remain wrappers | xhigh `Avicenna the 2nd` review passed in `threads/03-block-product-reduction/review-a2-product-step-a1-formal-inverse.md`; finite formal inverse only, no weakening of derivative/measure chart hypotheses, source coverage, source-measure transport, normal crossings, pole order, or RLCT |
| Regular/residual matrix-entry ideal split | A2 algebraic regular/residual separation | PDF p. 13 | existing four-block entry ideal; regular block-entry ideal definition; canonical product-difference source-rank package | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-residual-ideal-split.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-residual-ideal-split.md` | `regularBlockEntryIdeal`, `fourMatrixEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal`, `matrixEntryIdeal_triangularBlockProductDifference_eq_regular_sup_residual`, `ChartLocalSuffixState.productDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal`, and `PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularBlockEntryIdeal_sup_matrixEntryIdeal` proved in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean` and `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`; scalar ideal regrouping only; `D` remains residual | controller check plus xhigh scouts `Kant the 3rd` and `Planck the 3rd` passed in `threads/03-block-product-reduction/review-a2-regular-residual-ideal-split.md`; no analytic germ transport or RLCT consequence |
| Regular-coordinate scalar ideal bridge | A2 scalar-coordinate/ideal bridge | PDF p. 13 | regular-coordinate index; regular block-entry ideal; regular/residual ideal split | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-coordinate-ideal-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-coordinate-ideal-bridge.md` | `AoyagiRegularBlockCoordinateIndex.entryIdeal`, `AoyagiRegularBlockCoordinateIndex.entryIdeal_eq_regularBlockEntryIdeal`, and `PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_regularCoordinateIdeal_sup_matrixEntryIdeal` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; algebraic scalar ideal bookkeeping only; no residual `D` coordinate in the scalar regular-coordinate ideal | controller and xhigh `Bohr the 3rd` review passed in `threads/03-block-product-reduction/review-a2-regular-coordinate-ideal-bridge.md`; Bohr noted the scalar ideal equality is valid without finiteness assumptions |
| Local source regular-coordinate ideal split | A2 local source algebraic package | PDF p. 13 | fixed-base local source certificate; scalar regular-coordinate ideal bridge; regular/residual ideal split | reproduced at `threads/03-block-product-reduction/reproduction-a2-local-source-regular-coordinate-ideal-split.md`; statement card `threads/03-block-product-reduction/statement-card-a2-local-source-regular-coordinate-ideal-split.md` | `PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_regularCoordinateIdeal_source_neighborhood` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; local source-stratum guarded algebraic ideal split only | controller and xhigh `Feynman the 3rd` review passed in `threads/03-block-product-reduction/review-a2-local-source-regular-coordinate-ideal-split.md`; p. 13 sign convention checked |
| Regular-coordinate ideal source predicate | A2 regular-suspension source predicate | PDF p. 13 | fixed-base local source certificate; local regular-coordinate ideal split; supplied regular-suspension boundary | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-coordinate-ideal-source-predicate.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-coordinate-ideal-source-predicate.md` | `PaperEndpointFixedBaseRegularCoordinateIdealSourceNeighborhood`, `PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateIdealSourceNeighborhood`, `AoyagiCanonicalProductDifferenceRegularCoordinateIdealSource`, `aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate`, and `AoyagiSuppliedRegularSuspensionBoundary.of_canonicalProductDifferenceRegularCoordinateIdealSource` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean` and `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean`; the supplied-boundary constructor fills only `regular_chart_source` and leaves ideal transport, coverage, Jacobian compatibility, and exponent shift supplied | controller and xhigh `Carson the 3rd` review passed in `threads/03-block-product-reduction/review-a2-regular-coordinate-ideal-source-predicate.md`; no analytic germ transport, `Cfull` construction, normal crossings, pole order, or RLCT |
| Regular-coordinate ideal source existence | A2 source-hypothesis constructor | PDF p. 13 | raw canonical local source-certificate constructor; regular-coordinate ideal source predicate; supplied base rank bounds | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-coordinate-ideal-source-existence.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-coordinate-ideal-source-existence.md` | `exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionAlgebraicSource.lean`; it composes `exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate` with `aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_localSourceCertificate`; the rank-bound hypothesis `r <= rEdge p` remains supplied | controller and xhigh `Zeno the 3rd` review passed in `threads/03-block-product-reduction/review-a2-regular-coordinate-ideal-source-existence.md`; no analytic germ transport, `Cfull` construction, ideal transport, coverage, Jacobian compatibility, exponent shift, normal crossings, pole order, or RLCT |
| Base product rank bounded by edge ranks | A2 base source-rank inequality | PDF pp. 11-13 rank setup | reversed chain factorization; linear-map rank-of-composite inequality; finite-dimensional rank-to-finrank conversion | reproduced at `threads/03-block-product-reduction/reproduction-a2-base-product-rank-le-edge-rank.md`; statement card `threads/03-block-product-reduction/statement-card-a2-base-product-rank-le-edge-rank.md` | `paperTotalMap_finrank_range_le_reverseEdge_finrank_range`, `paperEndpointFixedBaseSourceRankStratum_selfBase_mem_of_rank_eq`, `paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl_of_rank_eq`, `exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate_of_rank_eq`, and `exists_aoyagiCanonicalProductDifferenceRegularCoordinateIdealSource_of_rank_eq` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`, `ProductReductionEntryIdealBoundary.lean`, and `RegularSuspensionAlgebraicSource.lean`; this removes the separate base `r <= rEdge p` input from the new wrappers only | controller and xhigh `Copernicus the 3rd` review passed in `threads/03-block-product-reduction/review-a2-base-product-rank-le-edge-rank.md`; no exact-rank/source-rank openness, analytic transport, `Cfull`, normal crossings, pole order, or RLCT |
| Regular/residual coordinate source-data package | A2 source-side regular/residual block package | PDF p. 13 | no-`hle` local source-certificate constructor; regular-coordinate ideal source neighborhood; scalar centered-continuity and count lemmas; dimension convention; residual scalar-coordinate ideal equality | regular-coordinate package reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-coordinate-source-data.md`; residual update reproduced at `threads/03-block-product-reduction/reproduction-a2-residual-coordinate-source-data.md`; statement cards `threads/03-block-product-reduction/statement-card-a2-regular-coordinate-source-data.md` and `threads/03-block-product-reduction/statement-card-a2-residual-coordinate-source-data.md` | `PaperEndpointFixedBaseRegularBlockScalarCoordinatesCenteredContinuousAt`, `PaperEndpointFixedBaseResidualBlockScalarCoordinatesCenteredContinuousAt`, `AoyagiResidualBlockCoordinateIndex`, `AoyagiResidualBlockCoordinateIndex.entryIdeal_eq_matrixEntryIdeal`, `PaperEndpointFixedBaseRegularCoordinateSourceData`, `PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.regularCoordinateSourceData`, and `exists_paperEndpointFixedBaseRegularCoordinateSourceData_of_rank_eq` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; the package exposes the local source certificate, source-stratum guarded regular/residual ideal split, centered scalar regular coordinates, centered scalar residual coordinates, `aoyagiTheorem2RegularVariableCount N H r`, and residual endpoint entry count `(H 1-r)*(H(N+1)-r)` | regular-coordinate package reviewed by xhigh `McClintock the 3rd` in `threads/03-block-product-reduction/review-a2-regular-coordinate-source-data.md`; residual-coordinate update reviewed by xhigh `Curie the 3rd` in `threads/03-block-product-reduction/review-a2-residual-coordinate-source-data.md` after row/column endpoint wording repair; no exact-rank/source-rank openness, analytic germ transport, regular-suspension chart, coverage, Jacobian compatibility, exponent shift, normal crossings, pole order, or RLCT |
| Product-difference coordinate source-data package | A2 source-side cleaned p. 13 scalar ideal family | PDF p. 13 | regular/residual coordinate source-data package; four-block entry ideal; fixed-base canonical product-difference source ranks; dimension convention and endpoint rank-width bounds | reproduced at `threads/03-block-product-reduction/reproduction-a2-product-difference-coordinate-source-data.md`; statement card `threads/03-block-product-reduction/statement-card-a2-product-difference-coordinate-source-data.md` | `AoyagiProductDifferenceCoordinateIndex`, `AoyagiProductDifferenceCoordinateIndex.entryIdeal_eq_fourMatrixEntryIdeal`, `AoyagiProductDifferenceCoordinateIndex.value_centered_continuousAt`, `AoyagiProductDifferenceCoordinateIndex.card_eq_endpointProductEntryCount`, `paperEndpointProductDifferenceCoordinateIndex_card_eq_endpointProductEntryCount`, `PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks.canonicalProductDifferenceEntryIdeal_eq_productDifferenceCoordinateIdeal`, `PaperEndpointFixedBaseProductDifferenceCoordinateIdealSourceNeighborhood`, `PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_productDifferenceCoordinateIdeal_source_neighborhood`, `PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceScalarCoordinates_centered_continuousAt`, and `PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.productDifferenceCoordinateIndex_card_eq_endpointProductEntryCount` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; `PaperEndpointFixedBaseRegularCoordinateSourceData` now exposes the combined product-difference ideal neighborhood, centered continuity, and endpoint product-entry count `H 1 * H(N+1)` | xhigh `Descartes the 3rd` review passed in `threads/03-block-product-reduction/review-a2-product-difference-coordinate-source-data.md` after source-wording repair; finite source-coordinate and scalar-ideal bookkeeping only; no exact-rank/source-rank openness, analytic chart, regular-suspension chart construction, analytic germ transport, coverage, transition regularity, Jacobian compatibility, normal crossings, pole order, or RLCT |
| Regular-suspension coordinate map source data | A2 source-side Pi-valued coordinate family package | PDF p. 13 | regular/residual and product-difference scalar centered-continuity packages; product topology on Pi types | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-suspension-coordinate-map-source-data.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-suspension-coordinate-map-source-data.md` | `paperEndpointFixedBaseRegularBlockCoordinateMap`, `paperEndpointFixedBaseResidualBlockCoordinateMap`, `paperEndpointFixedBaseProductDifferenceCoordinateMap`, `PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt`, `PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt`, and `PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; each source-data theorem proves the Pi-valued map is zero at the base point and continuous there | xhigh `Halley the 4th` review passed in `threads/03-block-product-reduction/review-a2-regular-suspension-coordinate-map-source-data.md`; product-topology packaging only; no analytic chart, local inverse, source-rank openness, analytic ideal transport, coverage, Jacobian compatibility, normal crossings, pole order, or RLCT |
| Cleaned coordinate square-sum | A2 finite cleaned-loss bookkeeping | PDF p. 13 | product-difference coordinate source-data package; regular/residual coordinate maps; finite sum over disjoint sum indices | reproduced at `threads/03-block-product-reduction/reproduction-a2-cleaned-coordinate-square-sum.md`; statement card `threads/03-block-product-reduction/statement-card-a2-cleaned-coordinate-square-sum.md` | `aoyagiCoordinateSquareSum`, `aoyagiCoordinateSquareSum_sumElim`, `AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_eq_regular_add_residual`, `paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim`, and `paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; this splits the cleaned coordinate square-sum into regular plus residual parts | xhigh `Darwin the 4th` review passed in `threads/03-block-product-reduction/review-a2-cleaned-coordinate-square-sum.md`; finite square-sum bookkeeping only; no equality with the literal signed/corrected p. 13 Frobenius loss, analytic generator transport, local loss comparability, chart construction, Jacobian compatibility, normal crossings, pole order, or RLCT |
| Literal product-difference square-sum | A2 finite literal-loss bookkeeping | PDF p. 13 | product-difference coordinate index; finite square-sum; literal p. 13 signed/corrected block | reproduced at `threads/03-block-product-reduction/reproduction-a2-literal-product-difference-square-sum.md`; statement card `threads/03-block-product-reduction/statement-card-a2-literal-product-difference-square-sum.md` | `AoyagiProductDifferenceCoordinateIndex.literalValue`, `literalValue_regular`, `literalValue_residual`, and `literalCoordinateSquareSum_eq_regular_add_correctedResidual` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; this expands the square-sum of `fromBlocks X (-F2) (-F3) (D - F3*F2)` as regular square-sum plus corrected residual square-sum | xhigh `Franklin the 4th` review passed in `threads/03-block-product-reduction/review-a2-literal-product-difference-square-sum.md`; finite square-sum bookkeeping only; no comparison with the cleaned loss, analytic transport, local loss comparability, chart construction, Jacobian compatibility, normal crossings, pole order, or RLCT |
| Finite literal-vs-cleaned loss comparison | A2 finite local-loss comparison boundary | PDF p. 13 | literal product-difference square-sum; cleaned coordinate square-sum; finite ordered-ring inequalities; row-column Cauchy-Schwarz | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`; statement card `threads/03-block-product-reduction/statement-card-a2-regular-suspension-loss-comparison-and-fubini-boundary.md` | `aoyagiCoordinateSquareSum_nonneg`, `aoyagiCoordinateSquareSum_sub_le_two_mul_add_two_mul`, `aoyagiCoordinateSquareSum_add_le_two_mul_add_two_mul`, `AoyagiRegularBlockCoordinateIndex.coordinateSquareSum_eq_ctop_add_f2_add_f3`, `AoyagiProductDifferenceCoordinateIndex.productCorrectionSquareSum_le_f3SquareSum_mul_f2SquareSum`, `AoyagiProductDifferenceCoordinateIndex.four_mul_productCorrectionSquareSum_le_regular_of_f2_f3_squareSum_add_le_one`, `AoyagiProductDifferenceCoordinateIndex.literalCoordinateSquareSum_le_two_mul_coordinateSquareSum_of_f2_f3_squareSum_add_le_one`, and `AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_le_two_mul_literalCoordinateSquareSum_of_f2_f3_squareSum_add_le_one` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; under `squareSum(F2)+squareSum(F3) <= 1`, the literal and cleaned finite square-sums are mutually bounded by factor `2` | xhigh `Schrodinger the 4th` review passed after wording repairs in `threads/03-block-product-reduction/review-a2-regular-suspension-loss-comparison-and-fubini-boundary.md`; finite ordered-ring comparison only; no p. 13 source-stratum smallness wrapper, analytic coordinate chart, Fubini/polar regular-variable shift, chart coverage, Jacobian compatibility, normal crossings, pole order, or RLCT |
| Literal signed product-difference coordinate ideal bridge | A2 finite p. 13 scalar ideal bridge | PDF p. 13 | signed-block entry-ideal cleanup; product-difference coordinate source-data package | reproduced at `threads/03-block-product-reduction/reproduction-a2-literal-product-difference-coordinate-ideal-bridge.md`; statement card `threads/03-block-product-reduction/statement-card-a2-literal-product-difference-coordinate-ideal-bridge.md` | `AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal` proved in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`; it identifies `matrixEntryIdeal (fromBlocks X (-F2) (-F3) (D - F3*F2))` with `AoyagiProductDifferenceCoordinateIndex.entryIdeal X F2 F3 D`; finite scalar ideal algebra only | xhigh `Hubble the 4th` review passed in `threads/03-block-product-reduction/review-a2-literal-product-difference-coordinate-ideal-bridge.md`; no analytic germ transport, chart coverage, regular-suspension construction, normal crossings, pole order, or RLCT |
| Theorem 2 supplied regular-suspension source-data final bridge | A6 chart-final handoff | PDF pp. 8-9 and p. 13 | Definition 3 source data; source-range rank-width or source-rank stratum; supplied regular-suspension full certificate; reduced min/order obligations; extraction for `Cfull` | reproduced at `threads/06-dln-translation/reproduction-theorem2-regular-suspension-final-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-regular-suspension-final-bridge.md` | `AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_suppliedRegularSuspension` and source-rank delegating wrapper proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2RegularSuspensionFinalBridge.lean`; these return `AoyagiTheorem2SuppliedChartFinalBoundary Cfull ...` exactly and do not add bare exponent-data variants | xhigh review passed in `threads/06-dln-translation/review-theorem2-regular-suspension-final-bridge-a6.md`; reviewer required chart-level only, explicit regular count equality, endpoint bounds from `hr`, and source-rank only as delegating wrapper |
| Selected-entry analytic atlas Case 2 source final socket | A4/A6 chart-final handoff | PDF pp. 19-22 for displayed Case 2 finite source calculation; PDF pp. 5-6 for supplied extraction boundary | supplied selected-entry analytic-atlas boundary; displayed Case 2 source certificate; A0 exponent-coordinate bridge; selected-width provenance; extraction; active-ratio and chart-count hypotheses | reproduced at `threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-case2-source-final-socket-a4.md`; statement card `threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-case2-source-final-socket.md` | `SelectedEntryCase2DisplayedA0SourceProductionData`, `SelectedEntryCase2DisplayedA0SourceProduction`, and `SelectedEntryAnalyticAtlasBoundary.theorem2SuppliedChartFinalBoundary_of_case2DisplayedA0SourceProduction` proved in `lean/DLNFibre/DLN/Aoyagi/SelectedEntryAnalyticAtlasCase2FinalBridge.lean`; this unwraps non-vacuous source-production payload and delegates to the existing Case 2/A0 chart-final bridge | xhigh review passed in `threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-case2-source-final-socket-a4.md`; no coverage, transition regularity, analytic Jacobian control, successor/suffix production, pole order, or RLCT is inferred |
| Chart-local suffix-state field continuity | A2 topology/product-reduction support | PDF pp. 11-13 | deterministic suffix-state recursion; recursive determinant-chart hypotheses; matrix inverse continuity on determinant-unit loci | reproduced at `threads/03-block-product-reduction/reproduction-a2-chart-local-suffix-state-field-continuity.md`; statement card `threads/03-block-product-reduction/statement-card-a2-chart-local-suffix-state-field-continuity.md` | `continuousAt_chartLocalSuffixState_step_fields` and `continuousAt_chartLocalSuffixState_suffixState_fields` proved in `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`; the suffix theorem returns `IsUnit Ctop.det` plus fieldwise continuity of `L`, `B`, `Ctop`, and `D` for every `i <= j` | xhigh review passed in `threads/03-block-product-reduction/review-a2-chart-local-suffix-state-field-continuity.md`; no analytic regularity, exact-rank openness, source-neighborhood construction, regular suspension, ideal transport, normal crossings, pole order, or RLCT |
| Fixed-base suffix-state field continuity handoff | A2 topology/product-reduction support | PDF pp. 11-13 | chart-local suffix-state field continuity; fixed endpoint bases from `B`; continuous reversed-edge family; recursive determinant-chart hypotheses | reproduced at `threads/03-block-product-reduction/reproduction-a2-fixed-base-suffix-state-field-continuity.md`; statement card `threads/03-block-product-reduction/statement-card-a2-fixed-base-suffix-state-field-continuity.md` | `paperEndpointFixedBaseContinuousEdges_recursiveSuffixState_fields_continuousAt` proved in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`; it builds the fixed-base coordinate matrix family from `Cedge`, proves it continuous via `continuous_linearMap_toMatrix`, and returns `IsUnit Ctop.det` plus fieldwise continuity of `L`, `B`, `Ctop`, and `D` for every suffix ending at `Fin.last N` | xhigh review passed in `threads/03-block-product-reduction/review-a2-fixed-base-suffix-state-field-continuity.md`; no analytic regularity, exact-rank/source-rank openness, chart coverage, regular suspension, ideal transport, normal crossings, pole order, or RLCT |
| Canonical product-difference coefficient fields | A2 product-reduction support | PDF p. 13 | suffix-state block-diagonal invariant; lower-unitriangularity of `S.L`; algebraic product-difference entry-ideal cleanup | reproduced at `threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-coefficient-fields.md`; statement card `threads/03-block-product-reduction/statement-card-a2-canonical-product-difference-coefficient-fields.md` | `ChartLocalSuffixState.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal` and `PaperEndpointFixedBaseProductReductionCertificate.productDifferenceEntryIdeal_eq_fourMatrixEntryIdeal_canonicalFields` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`; the four generators are the deterministic fields `S.Ctop - 1`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`, not existential `F2/F3/Ctop/D` witnesses | xhigh review passed in `threads/03-block-product-reduction/review-a2-canonical-product-difference-coefficient-fields.md`; no source-rank wrapper, exact-rank/source-rank openness, analytic regularity, analytic germ-ideal transport, chart coverage, normal crossings, pole order, or RLCT |
| Canonical product-difference coefficient-field continuity and centering | A2 product-reduction/topology support | PDF p. 13 | deterministic canonical coefficient fields; fixed-base suffix-state field continuity; self-base total matrix `fromBlocks 1 0 0 0`; lower-unitriangularity of `S.L` | reproduced at `threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-field-continuity.md`; statement card `threads/03-block-product-reduction/statement-card-a2-canonical-product-difference-field-continuity.md` | `paperEndpointFixedBaseContinuousEdges_productDifferenceCoefficientFields_continuousAt`, `paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_continuousAt`, and `paperEndpointFixedBaseContinuousEdges_selfBase_productDifferenceCoefficientFields_centered_continuousAt` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`; they prove continuity of `S.Ctop - 1`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`, and at self-base prove all four fields vanish | xhigh review passed in `threads/03-block-product-reduction/review-a2-canonical-product-difference-field-continuity.md`; no analytic regularity, exact-rank/source-rank openness, chart coverage, analytic ideal/germ transport, regular-suspension certificate, normal crossings, pole order, or RLCT |
| Canonical product-difference local certificate | A2 product-reduction/topology support | PDF p. 13 | canonical coefficient-field continuity and centering; product-reduction local certificate; source-rank stratum; residual-rank formulas | reproduced at `threads/03-block-product-reduction/reproduction-a2-canonical-product-difference-local-certificate.md`; statement card `threads/03-block-product-reduction/statement-card-a2-canonical-product-difference-local-certificate.md` | `PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks`, `PaperEndpointFixedBaseProductReductionCertificate.toCanonicalProductDifferenceSourceRanks`, `paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source`, `PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate`, and `exists_paperEndpointCanonicalProductDifferenceLocalCertificate` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`; the local package stores centered continuous canonical fields and a `nhdsWithin` source-stratum conclusion whose pointwise ideal equality uses deterministic fields | xhigh review passed in `threads/03-block-product-reduction/review-a2-canonical-product-difference-local-certificate.md`; relative/vacuous when the stratum is empty by design; no exact-rank/source-rank openness, analytic regularity, chart coverage, analytic ideal/germ transport, regular-suspension construction, normal crossings, pole order, or RLCT |
| Lemma 2 block elimination | A1 | PDF pp. 10-11 | matrix rank/open block hypotheses | draft + partial check: `threads/03-block-product-reduction/reproduction-draft.md`, `threads/03-block-product-reduction/reproduction-check.md`; algebraic chart identities and rank formula checked | block identities and indexed variants plus `rank_fromBlocks_zero_zero` and `rank_fromBlocks_eq_card_add_rank_schurComplement_of_isUnit_det`; proved in `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean` | reviewed; statement cards `threads/03-block-product-reduction/statement-card-a1-block-identities.md`, `threads/03-block-product-reduction/statement-card-a1-rank-formula.md` |
| Theorem 3 product reduction | A2 | PDF pp. 11-13 | A1, product/block notation, through-layer open-chart/basis lemma, entry-ideal algebra, regular-suspension certificate | draft + failed full check plus repair reports: `threads/03-block-product-reduction/reproduction-draft.md`, `threads/03-block-product-reduction/reproduction-check.md`, `threads/03-block-product-reduction/reproduction-repair-a2.md`, `threads/03-block-product-reduction/through-layer-basis-reproduction.md`; full theorem not formalisation-ready; chart-local induction step reproduced; through-layer basis repair checked; finite chart-data construction rechecked; paper-order bridge notes `threads/03-block-product-reduction/paper-order-bridge-notes.md`; regular-suspension plan `threads/03-block-product-reduction/regular-suspension-plan.md`; pointwise p. 13 block product-difference algebra reproduced at `threads/03-block-product-reduction/reproduction-a2-block-product-difference-algebra.md`; product-difference entry-ideal boundary reproduced at `threads/03-block-product-reduction/reproduction-a2-product-difference-entry-ideal-boundary.md` | partial sub-artifacts proved: `productReduction_chartLocalInductionStep_fromBlocks`, `productReduction_chartLocalInductionStep_fromBlocks_indexed`, `upperUnitriangular_mul_fromBlocks_one_zero`, `upperUnitriangular_mul_fromBlocks_one_zero_indexed`, `exists_fromBlocks_one_zero_of_upperUnitriangular_mul`, `exists_fromBlocks_one_zero_of_upperUnitriangular_mul_indexed`, `topLeftCorner`, `upperRightBlock`, `lowerRightBlock`, `identityCornerForm`, `identityCornerDetChart`, `identityCornerForm_upperUnitriangular_mul`, `productReduction_blockDiagonal_mul_fromBlocks_one_zero_rightElim_indexed`, `productReduction_blockDiagonal_mul_eq_fromBlocks_one_zero_rightElim_indexed`, `productReduction_blockDiagonal_mul_identityCornerForm_rightElim`, `productReduction_blockDiagonal_mul_identityCornerForm_rightElim_submatrix`, `productReduction_blockDiagonal_mul_unitriangular_identityCornerForm_rightElim`, `upperUnitriangular_neg_mul_upperUnitriangular`, `upperUnitriangular_neg_mul_upperUnitriangular_neg_neg`, `productReduction_identityCorner_suffixStep_rightElim`, `productReduction_identityCorner_suffixChain_rightElim`, and `triangularBlockProductDifference_fromBlocks_indexed` in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`; matrix-entry ideal transport/sign/block cleanup lemmas in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`; product-difference entry-ideal boundary wrappers in `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`; through-layer subspace theorem `exists_chain_throughSubspaces`, restricted-edge equivalence `throughSubspaceEdgeEquiv`, paper-order composite `paperChainMap`, paper-order split theorem `paperChainMap_zero_last_eq_prefix_comp_suffix`, reversed vertex/edge definitions `reverseVertex` and `reverseEdge`, and reversal theorem `chainMap_reverse_eq_paper` in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerBasis.lean`; per-edge transported quotient-basis theorem `exists_toMatrix_throughSubspaceEdge_eq_fromBlocks_one_zero`, direct-sum theorem `exists_toMatrix_throughSubspaceEdge_basisOfIsCompl_eq_fromBlocks_one_zero`, prefix-basis theorem `exists_toMatrix_throughSubspaceEdge_prefix_basisOfIsCompl_eq_fromBlocks_one_zero`, chart-data theorem `exists_unitriangular_toMatrix_throughSubspaceEdge_chartData_eq_fromBlocks_one_zero`, shared adapted-basis theorem `exists_toMatrix_throughSubspaceEdge_adaptedBasis_eq_fromBlocks_one_zero`, adapted matrix composition/reduction definitions/theorems `throughSubspaceAdaptedChainMapMatrix`, `throughSubspaceAdaptedChainMapMatrix_proof_irrel`, `throughSubspaceAdaptedChainMapMatrix_self`, `throughSubspaceAdaptedEdgeMatrix`, `throughSubspaceAdaptedChainMapMatrix_succ`, `throughSubspaceAdaptedChainMapMatrix_succ_right`, `throughSubspaceAdaptedEdgeProductMatrix`, `throughSubspaceAdaptedEdgeProductMatrix_self`, `throughSubspaceAdaptedEdgeProductMatrix_succ`, `throughSubspaceAdaptedChainMapMatrix_eq_edgeProductMatrix`, `throughSubspaceAdaptedChainMapMatrix_zero_eq_edgeProductMatrix`, `toMatrix_chainMap_zero_last_eq_adaptedEdgeProductMatrix`, `identityCornerForm_throughSubspaceAdaptedEdgeMatrix`, and `productReduction_throughSubspaceAdaptedChainMapMatrix_suffixChain_rightElim`, endpoint total-product theorems `toMatrix_chainMap_zero_last_ker_basisOfIsCompl_eq_fromBlocks_one_zero_zero` and `toMatrix_chainMap_zero_last_chartData_eq_fromBlocks_one_zero_zero_of_maps_complement_to_zero`, finite chart-data definitions `throughSubspaceComplement`, `throughSubspaceComplementIndex`, `throughSubspaceChartDataOfFiniteDimensional`, `throughSubspaceAdaptedBasis`, `throughSubspaceEndpointComplement`, `throughSubspaceEndpointComplementIndex`, and `throughSubspaceEndpointChartDataOfFiniteDimensional`, endpoint-compatible package theorems `toMatrix_chainMap_zero_last_endpointChartData_eq_fromBlocks_one_zero_zero` and `endpointChartData_edge_and_totalProduct_blocks`, nonempty/existence theorems `nonempty_throughSubspaceChartDataOfFiniteDimensional`, `nonempty_throughSubspaceEndpointChartDataOfFiniteDimensional`, `exists_isCompl_ker_throughSubspaceChartDataOfFiniteDimensional`, and `exists_isCompl_ker_throughSubspaceEndpointChartDataOfFiniteDimensional`, concrete finite-basis edge theorem `exists_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`, concrete finite-basis unitriangular theorem `exists_unitriangular_toMatrix_throughSubspaceEdge_finiteDimensional_eq_fromBlocks_one_zero`, paper-order disjointness bridge `disjoint_ker_reverse_total_of_disjoint_ker_paperChainMap`, paper-order complement bridge `isCompl_ker_reverse_total_of_isCompl_ker_paperChainMap`, paper-order finite edge theorem `exists_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`, paper-order finite unitriangular theorem `exists_unitriangular_toMatrix_reverseEdge_finiteDimensional_eq_fromBlocks_one_zero`, paper-order determinant-chart predicates for `paperAdaptedReverseEdgeMatrix` and its unitriangular transform, paper-order one-edge right-elimination theorem `productReduction_paperAdaptedReverseEdgeMatrix_rightElim`, paper-order endpoint theorem `toMatrix_paperChainMap_ker_finiteDimensional_eq_fromBlocks_one_zero_zero`, paper-order endpoint-compatible data theorem `exists_isCompl_ker_paperEndpointChartDataOfFiniteDimensional`, paper-order shared-basis package `paperEndpointChartData_edge_and_totalProduct_blocks`, and concrete finite-basis endpoint theorem `toMatrix_chainMap_zero_last_ker_finiteDimensional_eq_fromBlocks_one_zero_zero` in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`; paper-order endpoint reduction wrapper, topological open-neighborhood bridge, full theorem, and RLCT/certificate consequences blocked | xhigh reviews pass for chart-local theorem, entry-ideal lemmas, through-subspace theorem, quotient-basis through-matrix theorem, endpoint total-product theorem, prefix-compatible edge theorem, supplied chart-data bundle, reversed-chain bridge, one-edge right-elimination orientation/scope, endpoint-compatible chart-data shape, and adapted matrix composition/all-layer product orientation; xhigh recommendation incorporated for right-elimination assembly interface; xhigh suffix-chain review passed with source-fidelity warning; through-layer reproduction checked; block product-difference algebra independently checked by xhigh `Lorentz` and accepted by xhigh `Fermat` in `threads/03-block-product-reduction/review-a2-block-product-difference-algebra.md`; product-difference entry-ideal boundary reviewed by xhigh `Dewey` in `threads/03-block-product-reduction/review-a2-product-difference-entry-ideal-boundary.md`; statement cards `threads/03-block-product-reduction/statement-card-a2-chart-local-induction-step.md`, `threads/03-block-product-reduction/statement-card-a2-entry-ideal.md`, `threads/03-block-product-reduction/statement-card-a2-unitriangular-chart.md`, `threads/03-block-product-reduction/statement-card-a2-through-subspaces.md`, `threads/03-block-product-reduction/statement-card-a2-paper-chain.md`, `threads/03-block-product-reduction/statement-card-a2-paper-matrix-block.md`, `threads/03-block-product-reduction/statement-card-a2-one-edge-right-elim.md`, `threads/03-block-product-reduction/statement-card-a2-suffix-chain-right-elim.md`, `threads/03-block-product-reduction/statement-card-a2-endpoint-compatible-chart-data.md`, `threads/03-block-product-reduction/statement-card-a2-adapted-matrix-composition.md`, `threads/03-block-product-reduction/statement-card-a2-through-matrix-block.md`, `threads/03-block-product-reduction/statement-card-a2-chart-data-existence.md`, `threads/03-block-product-reduction/statement-card-a2-total-product-block.md`, `threads/03-block-product-reduction/statement-card-a2-block-product-difference-algebra.md`, `threads/03-block-product-reduction/statement-card-a2-product-difference-entry-ideal-boundary.md`; full Theorem 3 review pending |
| Theorem 3 transformed-edge rank condition | A2 | PDF pp. 11-13 | fixed-base endpoint bases; determinant-unit block-unitriangular rank preservation | reproduced at `threads/03-block-product-reduction/reproduction-a2-transformed-edge-rank-stratum-bridge.md` | `paperEndpointFixedBase_transformedEdgeRanks_iff_edgeRankStratum` proved in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`; identifies the recursive transformed-edge rank predicate with `paperEndpointFixedBaseEdgeRankStratum`; no exact-rank openness, chart production, analytic transport, normal crossings, pole order, or RLCT | statement card `threads/03-block-product-reduction/statement-card-a2-transformed-edge-rank-stratum-bridge.md`; xhigh review passed in `threads/03-block-product-reduction/review-a2-transformed-edge-rank-stratum-bridge.md` |
| Post-Theorem-3 regular-variable count | A2 finite bridge | PDF p. 13 | A0 finite `jacobianPriorLossShift`; A6 formula notation; endpoint rank-width bounds, now discharged from source-rank-stratum membership when `L=N` and `H(k+1)=finrank(W k)` | reproduced at `threads/03-block-product-reduction/reproduction-a2-regular-variable-count.md`; source-rank endpoint-bound reproduction at `threads/03-block-product-reduction/reproduction-a2-regular-variable-source-rank-shift.md`; statement cards `threads/03-block-product-reduction/statement-card-a2-regular-variable-count.md` and `threads/03-block-product-reduction/statement-card-a2-regular-variable-source-rank-shift.md` | `aoyagiTheorem2RegularVariableCount` and `aoyagiTheorem2RegularTerm_eq_half_regularVariableCount` proved in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`; finite shift bridge proved in `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean` via `AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount`, `AoyagiNormalCrossingExponentData.exponentOrder_jacobianPriorLossShift_regularVariableCount`, chart-certificate projections, and `AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift`/`of_chart_regularVariableCountShift`; source-rank variants now prove `paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds`, exponent-data/chart finite-minimum shift from source rank, and finite-formula constructors `of_regularVariableCountShift_sourceRankStratum`/`of_chart_regularVariableCountShift_sourceRankStratum`; no regular-suspension chart construction or analytic additivity | xhigh reviews passed in `threads/03-block-product-reduction/review-a2-regular-variable-count.md` and `threads/03-block-product-reduction/review-a2-regular-variable-source-rank-shift.md`; nonclaims recorded next to the statements |
| Theorem 4 deepest singular point | A3 | PDF p. 14 | A2, analytic/global comparison | source scout report: `threads/02-analytic-interface/scout-report.md`; A2 repair notes at `threads/02-analytic-interface/interface-repair-a2.md`; xhigh `Dirac the 3rd` avoidance audit checked the current final sockets | no Lean target for current local/conditional supplied sockets; avoided by theorem statement shape, with source data and normal-crossing certificates supplied rather than globally produced | xhigh `Dirac the 3rd` passed; reopen only for a future global arbitrary-base-point theorem or a global-attainment source-production claim |
| Blow-up inductive statement | A4 | PDF pp. 14-15 | reduced product coordinates | draft + failed check plus repair: `threads/04-blow-up-certificate/reproduction-draft.md`, `threads/04-blow-up-certificate/reproduction-check.md`, `threads/04-blow-up-certificate/reproduction-repair-a4.md`; source uses actual widths `M^{(s)}` and prefix minima `M(S)` simultaneously; page image also shows the inductive comparability range undercounts labels relative to the Jacobian ranges | actual-width vs prefix-width label API and introduced-label state bookkeeping proved in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; invariant theorem TBD/blocked | failed check; xhigh source and pen-and-paper rechecks completed; statement cards `threads/04-blow-up-certificate/statement-card-a4-actual-width-labels.md`, `threads/04-blow-up-certificate/statement-card-a4-introduced-labels.md` |
| Blow-up Case 1 | A4 | PDF pp. 15-18 | reduced product coordinates, inductive statement | repair report corrects the row-strip center and exponent increments to use actual active column width `M^{(S+1)}-J`; selected-variable chart and displayed pivot chart are understood only locally; full pivot-chart family or permutation reduction still missing; `P` quotient divisibility reduced to recurrence arithmetic; normalized displayed `Q/P` matrix identities checked; tail-lowering exponent increment checked under explicit flat-tail hypothesis; one-label lower-tail certificate transformer requires old least value `J+J1` and `J<=J+J1`; Case 1 center generator set records chosen old generator plus actual-width row strip but does not encode old-label hypotheses; row-strip containment requires explicit bound `J+J1<=mu_S`; first-jump package now records the strict nonterminal boundary `J+J1<mu_S`, selected introduced label, level gap, and componentwise minimality but not `b` recurrence semantics; same-domain lower-tail update assumes `leastValue=level`, flat-tail, selected post-data, and unchanged non-selected labels; selected-label update-data helpers are total assignment overrides only; level/tail bridge assumes `leastValue=level` for introduced labels and flat-tail only above pivot; selected-old erased-base and concrete level-move recurrence checkpoints are now reproduced | monomial recurrence divisibility, normalized `Q` column-operation identities, normalized `P` row-operation identity, combined local normalized pivot-step identities, Case 1 tail-lowering terminal-exponent increment, lower-tail finite minimum facts, one-label lower-tail certificate transformer, finite Case 1 center generator bookkeeping, row-strip residual-block containment, Case 1 first-jump selected-label hypothesis package, conditional same-domain Case 1 lower-tail certificate update, selected-label update-data helper theorem, conditional level/tail invariant bridge, Case 1 chart-family boundary names, displayed top-left source-order adapter, selected-old erased-base recurrence model, and selected-old concrete level-move state proved in `BlowupArithmetic.lean`; transition lemma TBD/blocked | repair note updated; statement cards `threads/04-blow-up-certificate/statement-card-a4-monomial-recurrence-divisibility.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-p-row-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-q-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-pivot-step.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-tail-exponent-increment.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-center-generators.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-row-strip-containment.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-first-jump-hypotheses.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-same-domain-lower-tail-update.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-label-update-data.md`, `threads/04-blow-up-certificate/statement-card-a4-level-tail-invariant-bridge.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-chart-family-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-displayed-top-left-source-order-adapter.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-erased-base-source-model.md`, `threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-concrete-level-move.md` |
| Blow-up Case 2 | A4 | PDF pp. 19-22 | reduced product coordinates, inductive statement | page image confirms the printed vector `t_{S,J+1}^{(i)}=M^{(i+1)}` for `i<S` and printed increment `(M(S)-J)(M^{(S+1)}-J)`; substituting that printed vector into the terminal formula gives `(M^{(S)}-J)(M^{(S+1)}-J)` unless `M(S)=M^{(S)}`; the prefix-minimum vector repairs the arithmetic but is a corrected certificate, not printed source data; pivot charts, full polynomial-coordinate chart construction, `b'_i`/standalone-`u` bookkeeping, termination, and boundary cases remain unresolved; normalized displayed `Q/P` matrix identities are independent of this mismatch | arithmetic split, monomial recurrence divisibility, normalized `Q/P` identities, combined local normalized pivot-step identity, corrected Case 2 vector minimum certificate, one-label corrected Case 2 new-label certificate, finite exponent-domain bookkeeping, Case 2 residual-block entry set, selected-entry substitution scaffold, displayed pivot-first following-factor package, displayed source-substitution factorisation, transported following-factor name, row-index monomial-recurrence `Q/P` wrapper, row-index source-substitution `Q/P` wrapper, source-block tail-lift wrappers, all-pivot source-selected chart adapter, conditional recurrence-gap row-weight bridge, conditional finite label-product gap bridge, conditional introduced-label finite-domain gap bridge, conditional recurrence-state interface, arbitrary selected-pivot recurrence handoff, source-selected pair wrappers, supplied source-selected pivot boundary, displayed concrete-update boundary, selected-entry principalization/unit facts, Case 2 chart-family boundary names, displayed top-left source-order adapter, displayed finite frontier branch witness, source-chart frontier implication package, free-`Cprime` continuing lower-row product package, free-`Cprime` local product package, weighted free-`Cprime` lower-row projection, source-side weighted lower-row handoff, and paper-`Cprime` source-following weighted handoff proved in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`; all-pivot source-selected chart adapter also uses `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`; no source-faithful or corrected transition theorem accepted | xhigh rechecks confirm printed-vector mismatch/source gap, recurrence-divisibility reduction, normalized matrix algebra, one-label certificate scope, exponent-domain bookkeeping scope, residual-block entry bounds, selected-entry substitution scope, displayed source-substitution factor scope, row-index recurrence wrapper scope, row-index source-substitution scope, source-block tail-lift scope, all-pivot supplied-pivot source-selected adapter scope, recurrence-gap row-weight bridge scope, finite label-product gap scope, introduced-label finite-domain bridge scope, recurrence-state interface scope, arbitrary selected recurrence handoff scope, source-selected pair wrapper scope, selected-entry principalization/unit scope, Case 2 chart-family boundary scope, displayed top-left source-order adapter scope, supplied source-selected pivot boundary scope, displayed concrete-update boundary scope, displayed finite frontier branch scope, source-chart frontier implication package scope, free-`Cprime` lower-row identity scope, free-`Cprime` weighted/local product package scope, weighted lower-row projection scope, source-side weighted lower-row handoff scope, and paper-`Cprime` source-following weighted handoff scope; statement cards `threads/04-blow-up-certificate/statement-card-a4-terminal-exponent-split.md`, `threads/04-blow-up-certificate/statement-card-a4-monomial-recurrence-divisibility.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-p-row-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-q-operation.md`, `threads/04-blow-up-certificate/statement-card-a4-normalized-pivot-step.md`, `threads/04-blow-up-certificate/statement-card-a4-corrected-case2-vector-minimum.md`, `threads/04-blow-up-certificate/statement-card-a4-corrected-case2-new-label-certificate.md`, `threads/04-blow-up-certificate/statement-card-a4-finite-exponent-domain-bookkeeping.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-residual-block-entries.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-entry-substitution.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-pivot-first-following-factor.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-substitution-factor.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-transported-following-factor-monomial.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-rowindex-source-substitution-qp.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-block-tail-lift.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-all-pivot-source-selected-chart-adapter.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-gap-row-weights.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-label-product-gap.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-introduced-label-gap.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-recurrence-state-interface.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-selected-recurrence-handoff.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-pair-wrapper.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-supplied-source-selected-pivot-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-concrete-update-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-selected-entry-principalization-unit-facts.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-chart-family-boundary.md`, `threads/04-blow-up-certificate/statement-card-a4-displayed-top-left-source-order-adapter.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-displayed-frontier-branch.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-frontier-packages.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-free-cprime-continuing-branch.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-free-cprime-local-product-package.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-weighted-free-cprime-lower-row-projection.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-source-side-weighted-lower-row-handoff.md`, `threads/04-blow-up-certificate/statement-card-a4-case2-paper-cprime-source-following-weighted-handoff.md`; review artifacts `threads/04-blow-up-certificate/review-case2-supplied-source-selected-pivot-boundary-a4.md`, `threads/04-blow-up-certificate/review-case2-displayed-concrete-update-boundary-a4.md`, `threads/04-blow-up-certificate/review-case2-displayed-frontier-branch-a4.md`, `threads/04-blow-up-certificate/review-case2-source-chart-frontier-packages-a4.md`, `threads/04-blow-up-certificate/review-case2-free-cprime-continuing-branch-a4.md`, `threads/04-blow-up-certificate/review-case2-free-cprime-local-product-package-a4.md`, `threads/04-blow-up-certificate/review-case2-weighted-free-cprime-lower-row-projection-a4.md`, `threads/04-blow-up-certificate/review-case2-source-side-weighted-lower-row-handoff-a4.md`, `threads/04-blow-up-certificate/review-case2-paper-cprime-source-following-weighted-handoff-a4.md`, `threads/04-blow-up-certificate/review-case2-all-pivot-and-rowindex-source-bridges-a4.md` |
| Terminal normal-crossing exponents | A4 | PDF p. 22 | Case 1/2 induction | page image confirms the terminal diagonal length is `M(L+1)` prefix minimum while the exponent formula uses actual widths `M^{(j)}`; terminal formula cannot be accepted as reproduced until Case 2 is split into printed mismatch and corrected certificate | terminal expression and prefix-step arithmetic proved in `BlowupArithmetic.lean`; full certificate theorem TBD/blocked | xhigh rechecks confirm split; statement card `threads/04-blow-up-certificate/statement-card-a4-terminal-exponent-split.md` |
| Quadratic exponent expression | A5 | PDF pp. 22-24 | terminal exponents | draft reproduction + failed check: promising algebra but candidate minimum must keep `\tilde t=0` restriction and feasibility hypotheses | arithmetic theorem TBD; blocked | failed check |
| Lemma 3 minimisation | A5 | PDF p. 24 | exponent vector definitions | full draft reproduction still blocked by terminal-variable restriction and feasibility; isolated endpoint arithmetic reproduced at `threads/05-arithmetic-tail/reproduction-lemma3-endpoint-arithmetic-a5.md`; isolated equality cases reproduced at `threads/05-arithmetic-tail/reproduction-lemma3-equality-cases-a5.md`; isolated equality count reproduced at `threads/05-arithmetic-tail/reproduction-lemma3-equality-count-a5.md` | isolated integer numerator identity, endpoint-corrected constrained minimum, exact equality cases, and equality-set cardinality proved in `lean/DLNFibre/DLN/Aoyagi/ArithmeticTail.lean` as `aoyagiLemma3A_eq_min_add`, `aoyagiLemma3A_isLeast_image_Icc`, `aoyagiLemma3A_eq_min_iff`, `aoyagiLemma3A_eq_min_iff_source_Icc`, and `aoyagiLemma3AMinimizerSet_card`; full Lemma 3/candidate theorem still blocked | isolated endpoint sub-slice xhigh checked by `Lorentz the 5th`, review `threads/05-arithmetic-tail/review-lemma3-endpoint-arithmetic-a5.md`; equality sub-slice checked by xhigh `Epicurus the 5th` and Lean-scouted by xhigh `Dalton the 5th`, review `threads/05-arithmetic-tail/review-lemma3-equality-cases-a5.md`; equality count checked by xhigh `Lagrange the 5th` and Lean-scouted by xhigh `Leibniz the 5th`, review `threads/05-arithmetic-tail/review-lemma3-equality-count-a5.md`; full A5 review still blocked |
| Lemma 4 pole/order comparison | A5 | PDF p. 25 | Lemma 3 | draft reproduction + failed check: depends on endpoint-corrected Lemma 3, the explicit `H_0`/`F_1` convention, source vector inequalities, and the two-value increment hypothesis; isolated two-value count reproduced at `threads/05-arithmetic-tail/reproduction-lemma4-two-value-count-a5.md`; source sum bridge reproduced at `threads/05-arithmetic-tail/reproduction-lemma4-sum-bridge-a5.md`; free-count bridge reproduced at `threads/05-arithmetic-tail/reproduction-lemma4-free-count-bridge-a5.md`; endpoint squeeze reproduced at `threads/05-arithmetic-tail/reproduction-lemma4-endpoint-squeeze-a5.md` | elementary two-value count proved in `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean` as `aoyagiLemma4_twoValueCount_int`; source telescope and count wrapper proved as `aoyagiLemma4F`, `aoyagiLemma4F_sum_eq_selectedSum`, `aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a`, and `aoyagiLemma4_twoValueCount_of_terminalH`; free-count split and isolated Lemma 3 numerator bridge proved as `highCount_castSucc_add_last_eq_total`, `highCount_castSucc_int_eq_or_eq_pred_of_total`, `aoyagiLemma4_freeHighCount_lemma3A_eq_min_of_totalCount`, and `aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min`; endpoint-sandwich wrappers proved as `aoyagiLemma4TerminalEndpoint`, `aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum`, `aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds`, `aoyagiLemma4_twoValueCount_of_terminalEndpointBounds`, and `aoyagiLemma4_terminalEndpointBounds_freeHighCount_lemma3A_eq_min`; full Lemma 4 theorem still blocked by the two-value hypothesis, vector-inequality-to-endpoint bridge, vector admissibility, terminal exponent rewrite, and correspondence to `lambda` | two-value count checked by xhigh `Hume the 5th` and Lean-scouted by xhigh `Chandrasekhar the 5th`, review `threads/05-arithmetic-tail/review-lemma4-two-value-count-a5.md`; source sum bridge checked by xhigh `Dewey the 5th`, review `threads/05-arithmetic-tail/review-lemma4-sum-bridge-a5.md`; free-count bridge checked by xhigh `Arendt the 5th` and Lean-scouted by xhigh `Banach the 5th`, review `threads/05-arithmetic-tail/review-lemma4-free-count-bridge-a5.md`; endpoint squeeze checked by xhigh `Parfit the 5th`, Lean-scouted by xhigh `Galileo the 5th`, and landed-patch audited by xhigh `Ramanujan the 5th`, review `threads/05-arithmetic-tail/review-lemma4-endpoint-squeeze-a5.md`; full Lemma 4 review still blocked |
| Lemma 5 final order count | A5 | PDF pp. 25-27 | Lemmas 3-4 | draft reproduction + failed check: chart-family admissibility, coverage, exclusions, and exact equal-minimum count not reproduced; isolated interval-excess arithmetic reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-interval-excess-a5.md`; same-coordinate value-set count reproduced at `threads/05-arithmetic-tail/reproduction-htilde-value-set-count-a5.md`; Eq5 own-coordinate source-label bridge reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-source-label-a5.md`; Eq5 strict alpha-family value image reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-value-image-a5.md`; Eq5 alpha-domain source-label adapter reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-source-label-a5.md`; Eq5 alpha-indexed branch value-image bridge reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`; Eq5 post-`p` lower exact guard reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-exact-guard-a5.md`; Eq5 early/tail interval guards reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-early-tail-interval-guards-a5.md`; Eq5 nonfirst block admissibility reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-admissibility-a5.md`; Eq5 nonfirst block explicit bounds reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-bounds-a5.md`; counted-datum back-to-label bijection reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-back-to-label-bijon-a5.md`; terminal exactness/bijection equivalence reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-bijon-equivalence-a5.md` | elementary interval-excess sum proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean` as `aoyagiLemma5IntervalSize_excess_sum_Icc`; same-coordinate value-set wrapper/count proved in `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean` as `aoyagiHtildeIntervalValueSetNat_card_of_lt`, `aoyagiHtildeIntervalValueSetNat_card`, and `aoyagiHtildeIntervalValueSetNat_excess_sum_Icc`; Eq5 own-coordinate label bounds proved as `aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality` and actual-width wrapper `aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility`; Eq5 strict alpha-family value image proved as `aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet`; Eq5 alpha-domain source-label adapter proved as `aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound`; Eq5 named alpha domain and branch-image bridge proved as `aoyagiLemma5Eq5AlphaDomain` and `aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet`; Eq5 post-`p` lower exact guard proved as `aoyagiLemma5Eq5PostPLowerGuard`, `aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_iff_offset_le_intervalExcess`, and companion wrappers/counterexamples; Eq5 early/tail interval guards proved as `aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_iff_index_le_intervalExcess`, `aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_iff_predAlpha_le_intervalExcess`, `aoyagiLemma5Eq5_tail_mem_intervalValueSetNat`, and guard wrappers; Eq5 nonfirst block admissibility proved as `aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard`; Eq5 explicit bounds proved as `aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_postPLowerGuard` and `aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_terminalRoom`; supplied counted-datum back-to-label bijection proved as `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumBackToBranchLabel`; supplied terminal exactness/bijection equivalence proved as `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_bijOn`; full order-count theorem still blocked | interval-excess arithmetic checked by xhigh `Confucius the 5th` and Lean-scouted by xhigh `Maxwell the 5th`, review `threads/05-arithmetic-tail/review-lemma5-interval-excess-a5.md`; value-set count checked by xhigh `Plato the 5th`; Eq5 source-label bridge checked by xhigh `Sagan`, `Averroes`, and `Peirce`, review `threads/05-arithmetic-tail/review-lemma5-eq5-source-label-a5.md`; Eq5 alpha-family value image checked by xhigh `Meitner` and `Kuhn`, review `threads/05-arithmetic-tail/review-lemma5-eq5-alpha-family-value-image-a5.md`; Eq5 alpha-family source-label adapter checked by xhigh `Avicenna`, review `threads/05-arithmetic-tail/review-lemma5-eq5-alpha-family-source-label-a5.md`; Eq5 alpha-indexed branch value-image bridge checked by xhigh `Anscombe`, review `threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`; Eq5 post-`p` lower exact guard pen-and-paper checked by xhigh `Bohr` and reviewed by xhigh `Darwin`, review `threads/05-arithmetic-tail/review-lemma5-eq5-postp-lower-exact-guard-a5.md`; Eq5 early/tail interval guards pen-and-paper checked by xhigh `Lagrange` and reviewed by xhigh `Hypatia`, review `threads/05-arithmetic-tail/review-lemma5-eq5-early-tail-interval-guards-a5.md`; Eq5 nonfirst block admissibility checked by xhigh `Faraday` and reviewed by xhigh `Confucius`, review `threads/05-arithmetic-tail/review-lemma5-eq5-nonfirst-block-admissibility-a5.md`; Eq5 explicit bounds reviewed in `threads/05-arithmetic-tail/review-lemma5-eq5-nonfirst-block-bounds-a5.md`; counted-datum back-to-label bijection source-checked by xhigh `Nietzsche`, pen-and-paper checked by xhigh `Russell`, Lean-scouted by xhigh `Hegel`, and reviewed by xhigh `Archimedes`, review `threads/05-arithmetic-tail/review-lemma5-back-to-label-bijon-a5.md`; terminal exactness/bijection equivalence reviewed by xhigh `Epicurus`, review `threads/05-arithmetic-tail/review-lemma5-terminal-exactness-bijon-equivalence-a5.md`; full Lemma 5 review still blocked |
| Lemma 5 Eq5 structured injection adapters | A5 | PDF pp. 25-27 | Eq5 own-block payloads, selected-block endpoint bookkeeping | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-structured-injection-adapters-a5.md` | generic counted-datum injectivity adapter `aoyagiLemma5Eq5_ownBlock_countDatum_injOn_of_pAlpha_injOn` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5CountDatumBridge.lean`; terminal-family counted-datum injectivity adapter, terminal-endpoint base/nonbase separation, and terminal-endpoint-base branch-label injectivity wrapper proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; this adapter slice itself added no exact count/no-extra theorem | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-structured-injection-adapters-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-structured-injection-adapters.md` |
| Lemma 5 Eq5 terminal pAlpha endpoint cardinal squeeze | A5 | PDF pp. 25-27 | Eq5 terminal counted-datum classifier, structured injection adapters, finite cardinal squeeze | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md` | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze` and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_endpointBase_cardSqueeze` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; conditional exactness/cardinality only under supplied terminal payloads, terminal `(p, alpha)` injectivity, branch alpha data, nonbase inequality, and terminal-endpoint base label | xhigh hardener review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-palpha-endpoint-cardinal-squeeze.md` |
| Lemma 5 Eq5 value-label branch injection | A5 | PDF pp. 25-27 | supplied nonbase value-label data, selected-block membership, terminal counted-datum classifier, finite cardinal squeeze | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-value-label-branch-injection-a5.md` | `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel`, `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_nonbase_valueLabel_terminalEndpointBase`, `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_valueLabel_cardSqueeze` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; replaces supplied branch-alpha formula/injectivity inputs with supplied value-label synchronisation, while retaining terminal Eq5 payloads, terminal `(p, alpha)` injectivity, nonbase block membership, terminal-label nonbase inequalities, and endpoint base label as hypotheses | xhigh review passed after statement-card wording repair in `threads/05-arithmetic-tail/review-lemma5-eq5-value-label-branch-injection-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-value-label-branch-injection.md` |
| Lemma 5 Eq5 branch-coordinate/value cardinal squeeze | A5 | PDF pp. 25-27 | supplied branch-coordinate map, branch source/value labels, value-label branch injection, terminal counted-datum classifier | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md` | `AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_branchCoord_leftEndpoint`, `AoyagiLemma5SuppliedTerminalCandidateFamily.valueLabel_of_branchK_value`, `AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_branchCoord_leftEndpoint_branchK_value_terminalEndpointBase`, `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_pAlpha_branchCoordVal_cardSqueeze` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; derives selected-block and value-label inputs from supplied branch-coordinate, `branchS`, and `branchK` data, while retaining terminal Eq5 payloads, terminal `(p, alpha)` injectivity, terminal-label nonbase inequalities, and endpoint base label as hypotheses | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-branchcoord-value-cardinal-squeeze-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-branchcoord-value-cardinal-squeeze.md` |
| Lemma 5 Eq5 endpoint raw coverage | A5 | PDF pp. 25-27 | Eq5 strict alpha-domain value image, supplied endpoint values, supplied-family constructor | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-branches-a5.md` | `aoyagiLemma5Eq5EndpointRawBranches`, `aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat`, and `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; proves raw coordinate value-image coverage from Eq5 alpha-domain coverage and endpoint values, while keeping base-value membership, raw injectivity, and disjointness supplied | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-raw-branches-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-raw-branches.md` |
| Lemma 5 Eq5 endpoint branch coordinates | A5 | PDF pp. 25-27 | Eq5 endpoint raw coverage, supplied component coordinate map | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-a5.md` | `aoyagiLemma5Eq5EndpointRawBranches_branchCoord_eq` and `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branchCoord_eq` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; proves coordinate correctness through the conditional raw branch set and base-value filter, not source production or distinctness | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-branchcoord-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-branchcoord.md` |
| Lemma 5 Eq5 endpoint branch-coordinate disjointness | A5 | PDF pp. 25-27 | Eq5 endpoint raw coverage, supplied component coordinate map | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md` | `aoyagiLemma5Eq5EndpointRawBranches_pairwiseDisjoint_of_branchCoord_eq` and `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_branchCoord` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; derives cross-coordinate raw disjointness at distinct interior coordinates from supplied coordinate facts, while keeping value injectivity and coverage/value data supplied | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-branchcoord-disjoint-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-branchcoord-disjoint.md` |
| Lemma 5 Eq5 endpoint raw value injectivity | A5 | PDF pp. 25-27 | Eq5 endpoint raw coverage, strict alpha injectivity, endpoint value formulas | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-value-injective-a5.md` | `aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective` and `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; derives one-coordinate raw value injectivity at interior coordinates from strict alpha injectivity and endpoint/strict values, then removes raw value-injectivity plus raw-disjointness inputs in a stricter constructor wrapper | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-value-injective-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-value-injective.md` |
| Lemma 5 Eq5 endpoint raw cardinality | A5 | PDF pp. 25-27 | Eq5 endpoint raw value-image coverage, raw value injectivity, Htilde interval cardinality | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-raw-cardinality-a5.md` | `aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective` and `aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; counts one interior raw endpoint branch set through its injective value image, not filtered nonbase branches or terminal-minimum labels | xhigh review passed after a docs fix in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-raw-cardinality-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-raw-cardinality.md` |
| Lemma 5 Eq5 endpoint counted-datum classifier | A5 | PDF pp. 25-27 | strictest Eq5 endpoint supplied family, generic supplied-family classifier API | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-countdatum-classifier-a5.md` | `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_branchCoord_eq` and `AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; packages the constructed supplied full branch set into the generic counted-datum classifier, not source terminal-minimum labels | xhigh review initially failed on docs, repaired after Hypatia/Dirac notes in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-countdatum-classifier-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-countdatum-classifier.md` |
| Lemma 5 Eq5 endpoint filtered cardinality | A5 | PDF pp. 25-27 | Eq5 endpoint supplied family constructor, generic supplied-family cardinality | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-filtered-cardinality-a5.md` | `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_branch_card_eq_intervalSize_sub_one`, `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_fullBranches_card`, and `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord_fullBranches_card` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; specializes generic supplied-family counts to the filtered Eq5 endpoint constructor, not terminal-minimum labels or source-backed no-extra coverage | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-filtered-cardinality-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-filtered-cardinality.md` |
| Lemma 5 Eq5 strict endpoint filtered cardinality | A5 | PDF pp. 25-27 | strictest Eq5 endpoint supplied family constructor, endpoint filtered cardinality | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-strict-filtered-cardinality-a5.md` | `AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_strict_branch_card_eq_intervalSize_sub_one` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5SuppliedCoverage.lean`; counts one filtered supplied coordinate branch set for the strictest endpoint constructor, not source records or terminal-minimum labels | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-strict-filtered-cardinality.md` |
| Lemma 5 Eq5 endpoint-to-terminal branch coordinates | A5 | PDF pp. 25-27 | strictest endpoint supplied family equality, terminal branch-coordinate adapter | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-to-terminal-branchcoord-a5.md` | `AoyagiLemma5SuppliedTerminalCandidateFamily.branchCoord_of_toNonbase_eq_eq5EndpointCoverage` and `AoyagiLemma5SuppliedTerminalCandidateFamily.branchBlock_of_toNonbase_eq_eq5EndpointCoverage_leftEndpoint` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; transports branch coordinates through an explicit equality with the strictest endpoint constructor and derives selected-block membership from a supplied `branchS` left-endpoint formula, not source construction or terminal exactness | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-strict-filtered-and-terminal-branchcoord-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-to-terminal-branchcoord.md` |
| Lemma 5 Eq5 endpoint-family cardinal squeeze | A5 | PDF pp. 25-27 | endpoint-family branch-coordinate transport, terminal cardinal squeeze | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md` | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_cardSqueeze` and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_cardSqueeze` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; replaces only the abstract terminal branch-coordinate input by an explicit endpoint-family equality, not source construction or source-backed/direct back-to-label no-extra coverage | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-family-cardinal-squeeze-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-family-cardinal-squeeze.md` |
| Lemma 5 Eq5 endpoint-family block-width cardinal squeeze | A5 | PDF pp. 25-27 | endpoint-family cardinal squeeze, selected-block actual-width bound | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md` | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze` and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`; replaces the per-label width input by blockwise actual-width data, not source construction or source-backed/direct back-to-label no-extra coverage | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-family-blockwidth-cardinal-squeeze.md` |
| Lemma 5 Eq5 terminal order formula bridge | A5/A6 handoff | PDF pp. 25-27 and Theorem 2 notation pp. 8-9 | endpoint-family block-width cardinal squeeze, Definition 3 order formula | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-order-formula-bridge-a5.md`; this is a downstream supplied-payload handoff under the A5 freeze decision | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalOrderBridge.lean`; specializes `a=data.aParam` and `M=data.ceilWidth`, using `data.aParam_le` and `data.selectedSum_eq`, not a source proof of Eq5 payloads, endpoint-family equality, injectivity, no-extra coverage, pole order, normal crossings, or RLCT | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-eq5-terminal-order-formula-bridge-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-order-formula-bridge.md` |
| Lemma 5 minimum numerator residue normalization | A5/A6 finite lambda alignment | PDF pp. 24-27 and Theorem 2 notation pp. 8-9 | Lemma 5 minimum numerator, Theorem 2 residue term | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-min-numerator-residue-normalization-a5.md`; narrow finite arithmetic under existing source-facing definitions | `aoyagiLemma5MinNumerator_div_four_sq_eq_theorem2ResidueTerm` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`; proves `a*ell*(ell-a)/(4*ell^2)=a*(ell-a)/(4*ell)` for `ell=n+1`, with no `a<=ell` hypothesis needed for cancellation; not terminal-exponent identification, active-ratio minimality, chart count/order, pole order, normal crossings, or RLCT | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-min-numerator-residue-normalization-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-min-numerator-residue-normalization.md` |
| Lemma 5 terminal order formula bridge | A5/A6 handoff | PDF pp. 25-27 and Theorem 2 notation pp. 8-9 | terminal exactness cardinal-bound equivalence, Definition 3 order formula | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-terminal-order-formula-bridge-a5.md`; source audit says no new source-backed A5 target remains, so this is a downstream supplied-obstruction handoff | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_theorem2OrderFormula_bound` and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_card_bound_and_branchLabel_injOn` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean`; rewrites the remaining supplied obstruction in final order notation, not a source proof of the upper bound, branch-label injectivity, no-extra coverage, pole order, normal crossings, or RLCT | xhigh review passed after aggregator import-order fix in `threads/05-arithmetic-tail/review-lemma5-terminal-order-formula-bridge-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-order-formula-bridge.md` |
| Lemma 5 counted-datum classifier order-formula bridge | A5/A6 handoff | PDF pp. 25-27 and Theorem 2 notation pp. 8-9 | counted-datum classifier boundary, terminal order formula bridge | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-countdatum-classifier-order-formula-bridge-a5.md`; source audit freezes classifier/injectivity/back-to-label construction as supplied | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumClassifier` and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumClassifier_and_branchLabel_injOn` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean`; consumes a supplied `TerminalMinimumCountDatumClassifier` to produce the displayed order-formula upper bound, and adds supplied branch-label injectivity for equality; not a source proof of the classifier, injectivity, back-to-label map, no-extra coverage, pole order, normal crossings, or RLCT | xhigh freeze recommendation from `Planck the 2nd` and `Goodall the 2nd`, with API map from `Parfit the 2nd`, recorded in `threads/05-arithmetic-tail/review-lemma5-countdatum-classifier-order-formula-bridge-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-countdatum-classifier-order-formula-bridge.md` |
| Lemma 5 terminal order classifier-notation bridge | A5/A6 handoff | PDF pp. 25-27 and Theorem 2 notation pp. 8-9 | upper-bound classifier boundary, counted-datum back-to-label boundary, Definition 3 order formula | reproduced at `threads/05-arithmetic-tail/reproduction-lemma5-terminal-order-classifier-notation-a5.md`; source audit freezes classifier/injectivity/back-to-label construction as supplied | `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_upperBoundClassifier`, `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_upperBoundClassifier_and_branchLabel_injOn`, `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_theorem2OrderFormula_of_countDatumBackToBranchLabel`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_countDatumBackToBranchLabel_and_injOn` proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalOrderBridge.lean`; rewrites existing supplied-boundary routes from `a*(n+1-a)+1` to `data.theorem2OrderFormula`, not a source proof of classifiers, back-to-label, injectivity, no-extra coverage, pole order, normal crossings, or RLCT | xhigh review passed in `threads/05-arithmetic-tail/review-lemma5-terminal-order-classifier-notation-a5.md`; statement card `threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-order-classifier-notation.md` |
| Theorem 2 terminal-order handoff | A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | terminal order formula bridge, finite exponent final socket | reproduced at `threads/06-dln-translation/reproduction-theorem2-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card`, `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_terminalMinimumLabels_card`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_terminalMinimumLabels_card` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; replaces the direct supplied order field by supplied chart-order/terminal-label equality plus supplied Lemma 5 obstruction, not chart production, exponent-minimum computation, source-backed no-extra coverage, pole order without A0, normal crossings, or RLCT | xhigh review passed in `threads/06-dln-translation/review-theorem2-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-terminal-order-bridge.md` |
| Theorem 2 active-ratio terminal-order handoff | A0/A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | finite active-ratio minimum certificate, terminal order formula bridge, supplied final socket | reproduced at `threads/06-dln-translation/reproduction-theorem2-active-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card`, `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_terminalMinimumLabels_card`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_terminalMinimumLabels_card` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; replaces the direct supplied exponent-minimum equality by supplied active-ratio witness/lower-bound data while still requiring supplied chart-order/terminal-label equality and Lemma 5 obstruction | xhigh review passed in `threads/06-dln-translation/review-theorem2-active-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-active-terminal-order-bridge.md` |
| Theorem 2 active chart-terminal-order handoff | A0/A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | finite active-ratio minimum certificate, finite chart-count maximum certificate, terminal order formula bridge, supplied final socket | reproduced at `threads/06-dln-translation/reproduction-theorem2-active-chart-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_terminalMinimumLabels_card`, `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_chartCount_terminalMinimumLabels_card` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; replaces the raw supplied chart/order equality by supplied chart-count witness/all-chart upper-bound data while still requiring supplied Lemma 5 obstruction | xhigh review passed in `threads/06-dln-translation/review-theorem2-active-chart-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-active-chart-terminal-order-bridge.md` |
| Theorem 2 displayed-ratio count terminal-order handoff | A0/A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | active-ratio minimum certificate, ratio chart-count rewrite, terminal order formula bridge, supplied final socket | reproduced at `threads/06-dln-translation/reproduction-theorem2-ratio-count-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_terminalMinimumLabels_card`, `AoyagiLemma5SuppliedTerminalCandidateFamily.theorem2SuppliedFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card`, and `AoyagiLemma5SuppliedTerminalCandidateFamily.lambda_and_poleOrder_eq_of_activePair_ratioCount_terminalMinimumLabels_card` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; allows chart counts to be supplied at the displayed Theorem 2 lambda instead of internal `D.exponentMinimum`, while still requiring source-supplied count facts and Lemma 5 obstruction | xhigh review passed in `threads/06-dln-translation/review-theorem2-ratio-count-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-ratio-count-terminal-order-bridge.md` |
| Theorem 2 counted-datum terminal-order handoff | A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | counted-datum order-formula bridge, terminal-order A6 wrappers | reproduced at `threads/06-dln-translation/reproduction-theorem2-countdatum-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | counted-datum classifier variants proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`: `theorem2FiniteExponentFormulaHypothesis_of_terminalMinimumLabels_card_of_classifier`, `theorem2FiniteExponentFormulaHypothesis_of_activePair_terminalMinimumLabels_card_of_classifier`, `theorem2FiniteExponentFormulaHypothesis_of_activePair_chartCount_classifier`, `theorem2FiniteExponentFormulaHypothesis_of_activePair_ratioCount_classifier`, the corresponding four `theorem2SuppliedFinalBoundary...` wrappers, and the corresponding four pair-form wrappers; these replace only the raw terminal upper-bound hypothesis by a supplied `TerminalMinimumCountDatumClassifier` | xhigh scout `Boyle the 2nd` passed; review recorded in `threads/06-dln-translation/review-theorem2-countdatum-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-countdatum-terminal-order-bridge.md` |
| Theorem 2 chart terminal-order handoff | A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | chart-certificate final socket, active-ratio/chart-count terminal-order bridge, counted-datum classifier bridge | reproduced at `threads/06-dln-translation/reproduction-theorem2-chart-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | chart-certificate variants proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`: `theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_terminalMinimumLabels_card`, `theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_terminalMinimumLabels_card`, `theorem2SuppliedChartFinalBoundary_of_activePair_chartCount_classifier`, `theorem2SuppliedChartFinalBoundary_of_activePair_ratioCount_classifier`, and the four corresponding pair-form wrappers; these preserve `AoyagiTheorem2SuppliedChartFinalBoundary` while consuming the existing A5 terminal-order and counted-datum classifier routes | xhigh review passed in `threads/06-dln-translation/review-theorem2-chart-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-chart-terminal-order-bridge.md` |
| Definition 3 source-data counted-datum classifier final bridge | A6 source-facing handoff | PDF pp. 8-9 and pp. 25-27 | Definition 3 source data, source-range rank-width hypothesis, supplied terminal counted-datum classifier, branch-label injectivity, displayed-ratio chart-count final sockets | reproduced at `threads/06-dln-translation/reproduction-definition3-terminal-countdatum-classifier-final-bridge-a6.md`; no new source theorem, only composition for produced `m,data` | `AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier` and `AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_terminalMinimumCountDatumClassifier` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderBridge.lean`; the provider callback is indexed by the `m,data` produced from Definition 3 source data and uses the existing terminal counted-datum classifier route plus active-ratio/displayed-ratio chart-count certificates; this is not selected-cutpoint construction, rank-width from matrix data, classifier construction, branch-label injectivity, active-ratio bounds, chart counts, chart production, pole order without A0, or RLCT | xhigh review passed in `threads/06-dln-translation/review-definition3-terminal-countdatum-classifier-final-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-terminal-countdatum-classifier-final-bridge.md` |
| Theorem 2 terminal-order equality bridge | A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | exact terminal count, finite active-ratio/chart-count certificates, supplied final sockets | reproduced at `threads/06-dln-translation/reproduction-theorem2-terminal-order-equality-bridge-a6.md`; no new source theorem, only finite socket composition | equality variants proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2TerminalOrderEqualityBridge.lean`: finite formula, supplied final-boundary, chart-final, and pair-form wrappers accepting `TC.terminalMinimumLabels.card = data.theorem2OrderFormula` directly; this is the downstream socket for exact-count routes such as the Eq5 endpoint-family handoff, not a proof of that exact count or any chart/analytic obligation | xhigh review passed in `threads/06-dln-translation/review-theorem2-terminal-order-equality-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-terminal-order-equality-bridge.md` |
| Theorem 2 Eq5 terminal-order bridge | A5/A6 handoff | PDF pp. 5-9 and pp. 25-27 | supplied Eq5 endpoint block-width payload, exact terminal-order equality bridge, displayed-ratio chart-count final sockets | reproduced at `threads/06-dln-translation/reproduction-theorem2-eq5-terminal-order-bridge-a6.md`; no new source theorem, only finite socket composition | `AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload`, `AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload.terminalMinimumLabels_card_eq_theorem2OrderFormula`, and displayed-ratio finite/final/chart-final wrappers proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`; final-boundary wrappers use the same selected cutpoints `P.cut` carried by the supplied Eq5 payload; this packages the large supplied payload and feeds its exact count into the A6 equality bridge, not a proof of Eq5 source-family construction, Lemma 5 exactness, active-ratio bounds, chart counts, chart production, pole order, or RLCT | xhigh source and Lean reviews passed in `threads/06-dln-translation/review-theorem2-eq5-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-theorem2-eq5-terminal-order-bridge.md` |
| Definition 3 source-data Eq5 terminal-order bridge | A6 source-facing handoff | PDF pp. 8-9 and pp. 25-27 | Definition 3 source data, source-range rank-width hypothesis, supplied Eq5 endpoint block-width payload callback, displayed-ratio chart-count final sockets | reproduced at `threads/06-dln-translation/reproduction-definition3-source-data-eq5-terminal-order-bridge-a6.md`; no new source theorem, only composition for produced `m,data` | `AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload` and `AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload` proved in `lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`; the provider callback is indexed by the `m,data` produced from Definition 3 source data and includes `P.cut = C`, preventing cutpoint drift; this is not selected-cutpoint construction, rank-width from matrix data, Eq5 family construction, Lemma 5 exactness, active-ratio bounds, chart counts, chart production, pole order, or RLCT | xhigh review passed in `threads/06-dln-translation/review-definition3-source-data-eq5-terminal-order-bridge-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-source-data-eq5-terminal-order-bridge.md` |
| Definition 3 arbitrary source-data obstruction | A6 diagnostic | PDF pp. 8-9 | Definition 3 printed selected/nonselected inequalities; strict cutpoint bounds | reproduced at `threads/06-dln-translation/reproduction-definition3-source-data-obstruction-a6.md`; source scout confirmed the reduced-width profile `1,2,100` obstructs arbitrary source-data existence under the printed inequalities | `AoyagiDefinition3SourceData.not_exists_widths_one_two_hundred` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2`, `r=0`, and `H(1)=1,H(2)=2,H(3)=100`, no `ell,C` satisfy `AoyagiDefinition3SourceData 2 ell H 0 C`; this is a guardrail only, not a corrected Definition 3 or a classification theorem | xhigh review passed in `threads/06-dln-translation/review-definition3-source-data-obstruction-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-source-data-obstruction.md` |
| Definition 3 `ell=1` nonselected obstruction | A6 diagnostic | PDF pp. 8-9 | Definition 3 printed strict selected inequality; printed nonselected upper inequality; source-range rank-width nonnegativity | reproduced at `threads/06-dln-translation/reproduction-definition3-ell-one-nonselected-obstruction-a6.md`; xhigh checker passed the integer argument and source shape | `AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `ell=1`, any source-range reduced-width value must lie in the selected value set under source-range rank-width nonnegativity; this is a necessary condition only, not selected-cutpoint construction or an `ell>1` classification | xhigh review passed in `threads/06-dln-translation/review-definition3-ell-one-nonselected-obstruction-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-ell-one-nonselected-obstruction.md` |
| Theorem 2 remaining source obligations map | A6 roadmap | PDF pp. 5-27 | current supplied final socket, A4/A5 source audits, A2 boundary | boundary map recorded at `threads/06-dln-translation/boundary-map-theorem2-remaining-source-obligations-a6.md`; no new theorem | no Lean target; records that selected-width provenance, normal-crossing certificate production, active-ratio bounds, displayed-ratio chart counts, A4 source/chart production, A2 source-boundary handling, supplied/corrected A5 terminal-order data, and A3 avoidance/policy remain open | statement card `threads/06-dln-translation/statement-card-a6-theorem2-remaining-source-obligations.md`; citation boundary remains only normal-crossing-to-RLCT extraction |
| Notation translation to repo DLN dimensions | A6 | Aoyagi PDF pp. 7-9 and pp. 11-14 | source inventory; selected cutpoint API | formula reproduced at `threads/06-dln-translation/reproduction-definition3-theorem2-translation-a6.md`; dimension/rank convention reproduced at `threads/06-dln-translation/reproduction-dimension-rank-convention-a6.md`; source/API xhigh checks incorporated | `aoyagiReducedWidthInt`, `aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le`, `aoyagiReducedWidthInt_nonneg_of_rank_le`, `aoyagiSelectedReducedWidths`, `aoyagiSelectedReducedWidths_apply`, `aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le`, `aoyagiSelectedReducedWidths_nonneg_of_rank_le`, `aoyagiSelectedWidthNat_selectedReducedWidths_of_lt`, `aoyagiSelectedWidthNat_selectedReducedWidths_fin`, `aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le`, `AoyagiDefinition3CeilData`, `theorem2OrderFormula`, `aoyagiTheorem2Lambda_average`, `aoyagiTheorem2Lambda_ceil`, `aoyagiTheorem2Lambda_expanded`, `selectedWidthAverage_eq_ceil`, `aoyagiTheorem2Lambda_average_eq_fromCeilData`, and `aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData` proved in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`; rank-width hypotheses remain explicit | reviewed at `threads/06-dln-translation/review-final-formula-notation-a6.md` and `threads/06-dln-translation/review-dimension-rank-convention-a6.md`; statement cards `threads/06-dln-translation/statement-card-a6-final-formula-notation.md` and `threads/06-dln-translation/statement-card-a6-dimension-rank-convention.md` |
| Definition 3 selected-sum bridge | A6 | Aoyagi PDF pp. 8-9 and pp. 24-25 | A6 notation; Lemma 4/Htilde arithmetic | reproduced at `threads/06-dln-translation/reproduction-definition3-lemma4-bridge-a6.md`; source-data ceiling reproduced at `threads/06-dln-translation/reproduction-definition3-source-data-ceil-a6.md`; positive-remainder ceiling data reproduced at `threads/06-dln-translation/reproduction-definition3-positive-remainder-ceil-data-a6.md`; xhigh source checks incorporated | `AoyagiDefinition3SourceData`, `AoyagiDefinition3CeilData.nonempty_of_ell_pos`, `AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder`, `AoyagiDefinition3SourceData.exists_ceilData`, `AoyagiDefinition3CeilData.one_le_ell`, `one_le_aParam`, `terminalEndpoint_eq_zero`, `htildeLowerChain_last_eq_zero`, `htildeUpperChain_last_eq_zero`, `htildeLowerNat_last_eq_zero`, `htildeUpperNat_last_eq_zero`, `htildeUpperNat_pred_eq_sub_lastWidth`, `Hlast_eq_zero_of_htildeChainBounds`, `intervalSize_excess_sum_Icc_eq_theorem2OrderFormula`, `htildeIntervalValueSetNat_excess_sum_Icc_eq_theorem2OrderFormula`, `htildeIntervalValueSetNat_terminal_eq_singleton_zero`, `suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`, `lemma4_twoValueCount_of_htildeChainBounds`, `selectedWidth_le_pred_of_sourceSelectedInequality`, `htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`, `lemma5Eq4_localData_of_sourceSelectedInequality`, `lemma5Eq5_labelBounds_of_sourceSelectedInequality`, and `lemma5Eq3_localData_of_sourceSelectedInequality_and_slack` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; count/order wrappers are finite arithmetic only; ceiling data can be obtained by Euclidean division or by a supplied positive-remainder decomposition once selected widths and `0<ell` are supplied | reviewed at `threads/06-dln-translation/review-definition3-bridge-a6.md`, `threads/06-dln-translation/review-definition3-source-data-ceil-a6.md`, and `threads/06-dln-translation/review-definition3-positive-remainder-ceil-data-a6.md`; statement cards `threads/06-dln-translation/statement-card-a6-definition3-bridge.md`, `threads/06-dln-translation/statement-card-a6-definition3-source-data-ceil.md`, and `threads/06-dln-translation/statement-card-a6-definition3-positive-remainder-ceil-data.md` |
| Definition 3 all-source selected source data | A6 restricted source-data constructor | Aoyagi PDF pp. 8-9 | consecutive all-source cutpoints; strict all-source selected inequality | reproduced at `threads/06-dln-translation/reproduction-definition3-all-source-selected-source-data-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-all-source-selected-source-data.md` | `AoyagiDefinition3SourceData.exists_consecutive_of_all_selected_strict` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `0<L`, strict all-source selected inequalities give consecutive cutpoints with `ell=L` and `AoyagiDefinition3SourceData L L H r C`; no rank-width, positivity, or constant-width hypothesis is assumed, and nonselected clauses are vacuous because every source-range value is selected | xhigh `Erdos the 3rd` review passed in `threads/06-dln-translation/review-definition3-all-source-selected-source-data-a6.md`; not arbitrary selected-cutpoint existence, Definition 3 classification, ceiling data, Eq5 construction, chart production, pole order, or RLCT |
| Definition 3 all-source selected ceiling data | A6 restricted provenance package | Aoyagi PDF pp. 8-9 | all-source selected source data; source-range rank-width; generic ceiling-data package | reproduced at `threads/06-dln-translation/reproduction-definition3-all-source-ceil-data-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-all-source-ceil-data.md` | `AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; it constructs consecutive all-source source data and then packages selected reduced widths plus a Definition 3 ceiling datum under explicit source-range rank-width; no closed form for `ceilWidth`/`aParam` is asserted | xhigh `Anscombe the 3rd` review passed in `threads/06-dln-translation/review-definition3-all-source-ceil-data-a6.md`; not rank-width from matrix data, arbitrary cutpoint existence, Definition 3 classification, Eq5 construction, chart production, pole order, or RLCT |
| Definition 3 all-source source-rank ceiling data | A6/A2 restricted provenance package | Aoyagi PDF pp. 8-9 and p. 13 dimension/rank convention | all-source strict/rank-width ceiling package; source-rank-stratum rank-width bridge | reproduced at `threads/06-dln-translation/reproduction-definition3-all-source-source-rank-ceil-data-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-all-source-source-rank-ceil-data.md` | `AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict_sourceRankStratum` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3RankWidthBridge.lean`; source-rank stratum plus dimension convention discharge only the source-range rank-width input, while the strict all-source selected inequality remains explicit | xhigh `Popper the 3rd` review passed in `threads/06-dln-translation/review-definition3-all-source-source-rank-ceil-data-a6.md`, with warning not to clone final-socket variants without a downstream consumer; no strict-inequality proof, exact-rank openness, chart coverage, Eq5 construction, pole order, or RLCT |
| Definition 3 nonconstant `(1,2,2)` example | A6 diagnostic/example | Aoyagi PDF pp. 8-9 | all-source constructor; concrete reduced-width arithmetic | reproduced at `threads/06-dln-translation/reproduction-definition3-nonconstant-one-two-two-example-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-nonconstant-one-two-two-example.md` | `AoyagiDefinition3SourceData.exists_consecutive_nonconstant_widths_one_two_two_selectedReducedWidthCeilData` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2`, `r=0`, and widths `(1,2,2)`, consecutive all-source cutpoints produce source data and a ceiling package, with `m 0=1`, `m 1=2`, `m 2=2`, and `m 0 != m 1` | xhigh `Mencius the 3rd` review passed in `threads/06-dln-translation/review-definition3-nonconstant-one-two-two-example-a6.md`; diagnostic only, not arbitrary source-data existence, Definition 3 classification, Eq5 construction, chart production, pole order, or RLCT |
| Definition 3 three-width triangle constructor | A6 restricted all-source constructor | Aoyagi PDF pp. 8-9 | all-source selected source-data constructor; source-range rank-width; three strict `L=2` selected inequalities | reproduced at `threads/06-dln-translation/reproduction-definition3-three-width-triangle-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-three-width-triangle.md` | `AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2`, widths `w1,w2,w3`, and `2*w_i < w1+w2+w3` for each source layer, consecutive all-source cutpoints produce source data and a ceiling package, with `m 0=w1`, `m 1=w2`, `m 2=w3`; focused module check passed | xhigh `Chandrasekhar the 3rd` review passed at `threads/06-dln-translation/review-definition3-three-width-triangle-a6.md`; not arbitrary source-data existence, Definition 3 classification, closed-form ceiling data, Eq5 construction, chart production, pole order, or RLCT |
| Definition 3 `L=2` all-source triangle formula package | A6 finite formula package | Aoyagi PDF pp. 8-9 | all-source triangle source-data constructor; source-range rank-width; supplied positive-remainder decomposition; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-triangle-formula-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-triangle-formula.md` | `AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_remainder_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; constructs consecutive source data, explicit `ceilWidth=ceilPred+1`, `aParam=a`, order formula `a*(2-a)+1`, selected pair sum, and finite Theorem 2 lambda expression for the all-source `ell=2` triangle branch | xhigh review passed in `threads/06-dln-translation/review-definition3-l-eq-two-triangle-formula-a6.md`; no source-rank wrapper, final socket, repeated-positive `ell=1` branch, Eq5 payloads, chart production, pole order, normal crossings, or RLCT |
| Definition 3 `L=2` all-source triangle parity formula package | A6 finite formula package | Aoyagi PDF pp. 8-9 | all-source triangle source-data constructor; source-range rank-width; parity of `w1+w2+w3`; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-triangle-parity-formula-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-triangle-parity-formula.md` | `AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth` and `AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; odd total gives `ceilWidth=T/2+1`, `aParam=1`, order `2`; even total gives `ceilWidth=T/2`, `aParam=2`, order `1`, while retaining selected-width provenance, pair sum, and finite lambda formula | xhigh review passed in `threads/06-dln-translation/review-definition3-l-eq-two-triangle-parity-formula-a6.md`; removes supplied positive-remainder decomposition when parity is known; no source-rank wrapper, final socket, Eq5 payloads, chart production, pole order, normal crossings, or RLCT |
| Definition 3 `L=2` branch formula rank-width removal | A6 finite formula API hardening | Aoyagi PDF pp. 8-9 plus branch-selection audit | existing repeated-positive and triangle parity `_rankWidth` packages; Nat-valued reduced-width identities; all-source strict rank-width theorem | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-formula-rankwidth-removal-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-branch-formula-rankwidth-removal.md` | `AoyagiDefinition3SourceData.rank_le_of_aoyagiReducedWidthInt_eq_natCast`, `sourceRangeRankWidth_of_three_reducedWidthInt_eq_natCast`, `allSourceStrict_of_L_eq_two_triangle_widths`, `sourceRangeRankWidth_of_L_eq_two_triangle_widths`, `exists_consecutive_three_widths_theorem2Formula_of_triangle_odd`, `exists_consecutive_three_widths_theorem2Formula_of_triangle_even`, and `exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; the wrappers only derive the previous `hr` input and delegate to branch-specific formula theorems | xhigh `Raman the 3rd` review passed in `threads/06-dln-translation/review-definition3-l-eq-two-branch-formula-rankwidth-removal-a6.md`; no canonical branch selection, branch independence, final socket, Eq5 payload, chart production, normal crossings, pole order, or RLCT |
| Definition 3 `L=2` branch-disjunction finite formula | A6 finite formula dispatch | Aoyagi PDF pp. 8-9 plus branch-selection audit | `L=2` source-data classification; no-`hr` repeated-positive and triangle parity formula wrappers | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-disjunction-formula-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-branch-disjunction-formula.md` | `AoyagiDefinition3SourceData.L2RepeatedPositiveTheorem2FormulaBranch`, `L2TriangleOddTheorem2FormulaBranch`, `L2TriangleEvenTheorem2FormulaBranch`, and `exists_L_eq_two_theorem2Formula_branchDisjunction_of_sourceData` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; from concrete Nat-valued widths and some `L=2` source data, returns an explicit repeated-positive/triangle-odd/triangle-even branch disjunction | xhigh `Ptolemy the 3rd` review passed in `threads/06-dln-translation/review-definition3-l-eq-two-branch-disjunction-formula-a6.md`; no canonical branch selection, branch independence, unique lambda/order, final socket, Eq5 payload, chart production, normal crossings, pole order, or RLCT |
| Definition 3 `L=2`, `ell=1` selected-pair formula package | A6 finite formula package | Aoyagi PDF pp. 8-9 | exposed selected pair; selected-value cover; positive selected values; source-range rank-width; supplied remainder-one decomposition; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-ell-one-selected-pair-formula-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-ell-one-selected-pair-formula.md` | `AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_remainder_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; constructs `ell=1` source data, explicit `ceilWidth=ceilPred+1`, `aParam=1`, order formula `1`, pair sum `u*v`, and finite lambda `regularTerm+u*v/2` for the exposed selected pair | xhigh review passed in `threads/06-dln-translation/review-definition3-l-eq-two-ell-one-selected-pair-formula-a6.md`; no canonical repeated-branch formula, source-rank wrapper, final socket, Eq5 payloads, chart production, pole order, normal crossings, or RLCT |
| Definition 3 `ell=1` automatic ceiling and `L=2` repeated-positive formula package | A6 finite formula package | Aoyagi PDF pp. 8-9 | exposed selected pair or positive repeated `L=2` widths; selected-value cover; source-range rank-width; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-ell-one-automatic-ceil-formula-a6.md` and `threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-positive-formula-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-repeated-positive-formula.md` | `AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth` and `AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `ell=1`, constructs `ceilWidth=u+v`, `aParam=1`, order `1`, pair sum `u*v`, and finite lambda `regularTerm+u*v/2`; the repeated-positive theorem chooses an `ell=1` selected pair by cases and returns it existentially | xhigh review passed in `threads/06-dln-translation/review-definition3-l-eq-two-repeated-positive-formula-a6.md`; older `..._remainder_rankWidth` theorem remains compatibility; no unique/canonical selected pair, source-rank wrapper, final socket, Eq5 payloads, chart production, pole order, normal crossings, or RLCT |
| Definition 3 general `L`, `ell=1` selected-pair formula package | A6 finite formula package | Aoyagi PDF pp. 8-9 | exposed selected pair; selected-value cover; positive selected values; source-range rank-width; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-ell-one-selected-pair-cover-formula-general-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-ell-one-selected-pair-cover-formula-general.md` | `AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth_general` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for arbitrary `L` and an exposed `ell=1` selected pair, constructs source data, `ceilWidth=u+v`, `aParam=1`, order `1`, pair sum `u*v`, Nat-width/nonnegativity/strictness provenance, and finite lambda `aoyagiTheorem2RegularTerm L H r + u*v/2` | xhigh review passed in `threads/06-dln-translation/review-definition3-ell-one-selected-pair-cover-formula-general-a6.md`; no canonical selected pair, branch-independent arbitrary-source-data payload, source-rank wrapper, final socket, Eq5 payloads, chart production, pole order, normal crossings, or RLCT |
| Definition 3 `ell=1` ceiling-data simplification | A6 finite formula arithmetic | Aoyagi PDF pp. 8-9 | supplied `AoyagiDefinition3CeilData 1 m`; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-ell-one-ceil-data-simplification-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-ell-one-ceil-data-simplification.md` | `AoyagiDefinition3CeilData.aParam_eq_one_of_ell_eq_one`, `selectedSum_eq_ceilWidth_of_ell_eq_one`, `ceilWidth_eq_selectedSum_of_ell_eq_one`, `theorem2OrderFormula_eq_one_of_ell_eq_one`, `theorem2Lambda_fromCeilData_eq_regularTerm_add_pairSum_half_of_ell_eq_one`, and `theorem2Lambda_fromCeilData_eq_regularTerm_add_selectedPair_half_of_ell_eq_one` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; any `ell=1` ceiling datum has `aParam=1`, `ceilWidth=sum_j m_j`, order `1`, and lambda `regularTerm + pairSum/2`, with selected-pair form `regularTerm+u*v/2` | xhigh review passed in `threads/06-dln-translation/review-definition3-ell-one-ceil-data-simplification-a6.md`; finite arithmetic only, no selected-cutpoint construction, branch choice, final socket, Eq5 payloads, chart production, pole order, normal crossings, or RLCT |
| Definition 3 `L=2` branch formula disagreement diagnostic | A6 finite formula diagnostic | Aoyagi PDF pp. 8-9 | value-level selected set; repeated-positive `ell=1` formula; all-source triangle parity formula | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-branch-formula-disagreement-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-branch-formula-disagreement.md` | `AoyagiDefinition3SourceData.exists_L_eq_two_two_three_three_formula_disagreement` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2,r=0` and reduced widths `(2,3,3)`, constructs both an `ell=1` repeated-positive source-data package and an `ell=2` all-source triangle package, proving finite lambda values `3` and `5/2` and both finite order formulas `1` | xhigh scout and review passed in `threads/06-dln-translation/review-definition3-l-eq-two-branch-formula-disagreement-a6.md`; finite diagnostic only, not a correction of Aoyagi, not branch-independence, not RLCT ambiguity, and no Eq5, chart, normal-crossing, pole-order, or extraction claim |
| Definition 3 `L=2` branch order disagreement diagnostic | A6 finite formula diagnostic | Aoyagi PDF pp. 8-9 | value-level selected set; repeated-positive `ell=1` formula; all-source triangle parity formula | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-order-disagreement-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-order-disagreement.md` | `AoyagiDefinition3SourceData.exists_L_eq_two_one_two_two_order_disagreement` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2,r=0` and reduced widths `(1,2,2)`, constructs both an `ell=1` repeated-positive source-data package and an `ell=2` all-source triangle package, proving both finite lambda values `1`, finite order formulas `1` and `2`, and order disagreement | xhigh review passed in `threads/06-dln-translation/review-definition3-l-eq-two-order-disagreement-a6.md`; finite diagnostic only, not a correction of Aoyagi, not branch-independence, not RLCT or pole-order ambiguity, and no Eq5, chart, normal-crossing, pole-order, or extraction claim |
| Definition 3 `L=2` pairwise-distinct classification | A6 finite source-data classification | Aoyagi PDF pp. 8-9 | Definition 3 source-data structure; `ell=1` nonselected obstruction; pairwise distinct source-range reduced widths; rank-width nonnegativity | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-pairwise-distinct-classification-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-pairwise-distinct-classification.md` | `AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct`, `AoyagiDefinition3SourceData.cut_eq_consecutive_of_L_eq_two`, and `AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2`, rank-width and pairwise distinct widths force all-source cutpoints, so source-data existence is equivalent to all-source strict inequalities | xhigh `Maxwell the 3rd` review passed at `threads/06-dln-translation/review-definition3-l-eq-two-pairwise-distinct-classification-a6.md`; repeated-width profiles, ceiling closed forms, Eq5 construction, chart production, pole order, and RLCT remain open |
| Definition 3 `L=2` repeated-width/full finite classification | A6 finite source-data classification | Aoyagi PDF pp. 8-9 | value-level nonselected condition; `ell=1` selected strict positivity; all-source triangle constructor | reproduced at `threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-width-classification-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-repeated-width-classification.md` | `AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one`, `AoyagiDefinition3SourceData.of_ell_eq_one_selectedValueSet_covers`, `AoyagiDefinition3SourceData.exists_ell_one_of_L_eq_two_positive_repeated`, and `AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; for `L=2`, source-data existence is equivalent to either all three reduced widths being positive with a repeated value, or the three all-source triangle inequalities | xhigh `Kepler the 3rd` review passed at `threads/06-dln-translation/review-definition3-l-eq-two-repeated-width-classification-a6.md`; no rank-width hypothesis is needed for bare source-data existence; no `L>2` classification, ceiling package, Eq5 construction, chart production, pole order, or RLCT |
| Definition 3 equal-width explicit ceiling data | A6 equal-width example | Aoyagi PDF pp. 8-9 | constant reduced-width source data; positive-remainder decomposition `w=L*q+a`, `0<a<=L` | reproduced at `threads/06-dln-translation/reproduction-definition3-equal-width-explicit-ceil-data-a6.md`; source review checked the equal-width example and divisible-case convention | `AoyagiDefinition3CeilData.equalWidthOfDecomposition` and `AoyagiDefinition3SourceData.exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition` proved in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`; gives `ceilWidth=w+q+1` and `aParam=a` for the constant selected-width family and packages the equal-width source data; finite arithmetic only | xhigh review passed in `threads/06-dln-translation/review-definition3-equal-width-explicit-ceil-data-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-equal-width-explicit-ceil-data.md` |
| Definition 3 equal-width finite Theorem 2 formula | A6 equal-width example/formula | Aoyagi PDF pp. 8-9 | equal-width explicit ceiling data; constant selected-width pair count; Theorem 2 finite formula definitions | reproduced at `threads/06-dln-translation/reproduction-definition3-equal-width-theorem2-formula-a6.md`; statement card `threads/06-dln-translation/statement-card-a6-definition3-equal-width-theorem2-formula.md` | `aoyagiSelectedWidthPairCount_cast`, `aoyagiSelectedWidthPairSum_const`, and `AoyagiDefinition3SourceData.exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition` proved in `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean` and `Definition3Bridge.lean`; returns order `a*(L-a)+1`, pair sum `((L+1)*L*w^2)/2`, and unfolded finite lambda with pair contribution `((L+1)*L*w^2)/4` for the constructed equal-width branch | xhigh `Hypatia the 2nd` review passed in `threads/06-dln-translation/review-definition3-equal-width-theorem2-formula-a6.md`; restricted finite arithmetic only, no arbitrary branch selection, Eq5 production, chart production, normal crossings, pole order, or RLCT |

## Latest A4 Update

The selected-entry finite affine-overlap family certificate has landed.  New
Lean names in `SelectedEntryNormalCrossing.lean` include
`SelectedEntryFiniteAffineTransitionRegularFamily`,
`SelectedEntryFiniteAffineTransitionRegularPair`,
`SelectedEntryFiniteAffineTransitionRegularFamily.pair`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.finiteAffineTransitionRegular`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finiteAffineTransitionRegular`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finiteAffineTransitionRegular_displayedPair`.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-affine-transition-regularity-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-affine-transition-regularity.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-affine-transition-regularity-a4.md`.

This packages the finite all-pivot selected-entry chart overlap identities:
transition-point formula, target coordinate formula, finite chart-map equality
on the normalised target-coordinate overlap, inverse, self-transition, and
cocycle.  It is not analytic transition regularity, chart coverage, source
production, normal crossings, pole order, termination, or RLCT extraction.

The Case 1 selected-entry chart-family data slice has landed.  New Lean names
in `BlowupArithmetic.lean` include
`Case1CenterSelectedEntryChartFamilyData`,
`Case1CenterSelectedEntryChartFamilyData.standard`,
`Case1CenterSelectedEntryChartFamilyData.selectedOldPivot`,
`Case1CenterSelectedEntryChartFamilyData.displayedPivot`,
`Case1CenterSelectedEntryChartFamilyData.standard_value_selectedOldPivot`,
`Case1CenterSelectedEntryChartFamilyData.standard_value_displayedPivot`,
`Case1CenterSelectedEntryChartFamilyData.standard_selectedOld_selected_mem_valueSet`,
`Case1CenterSelectedEntryChartFamilyData.standard_displayedPivot_selected_mem_valueSet`,
`Case1CenterSelectedEntryChartFamilyData.standard_centerSq_selectedOldPivot`,
`Case1CenterSelectedEntryChartFamilyData.standard_centerSq_displayedPivot`,
`Case1CenterSelectedEntryChartFamilyData.standard_centerIdeal_selectedOldPivot_eq_span_singleton`,
and
`Case1CenterSelectedEntryChartFamilyData.standard_centerIdeal_displayedPivot_eq_span_singleton`.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-selected-entry-chart-family-data-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-entry-chart-family-data.md`.
Review:
`threads/04-blow-up-certificate/review-case1-selected-entry-chart-family-data-a4.md`.

This specializes the generic finite selected-entry chart-family data to the
Case 1 center and records finite coordinate algebra for the selected-old and
displayed top-left row-strip pivots.  It is not chart coverage, chart
regularity, transition regularity, analytic Jacobian control, global A0 data,
pole order, or RLCT extraction.

The Case 1 selected-entry local exponent slice has landed.  New Lean names in
`SelectedEntryNormalCrossing.lean` include
`case1SelectedOldCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`,
`case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
`case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`,
`case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`,
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.lossExp_zero_zero`,
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_ratioAt_zero_zero`,
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`,
and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_exponentOrder_eq_one`.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-selected-entry-local-exponent-min-order-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-entry-local-exponent-min-order.md`.
Review:
`threads/04-blow-up-certificate/review-case1-selected-entry-local-exponent-min-order-a4.md`.

This composes the Case 1 erased-center cardinality calculation with the
generic selected-entry one-chart exponent arithmetic.  For both displayed
Case 1 finite microcertificates, the local finite ratio and local finite
minimum are `(1 + J1 * (n(S+1)-J)) / 2`, and the local finite exponent order
is `1`.  This is not a global A0 active-ratio lower bound, global exponent
minimum, global chart-count/order theorem, analytic Jacobian/volume-form
theorem, pole order, or RLCT extraction.

## Latest A0 Update

The normal-crossing chart-certificate spine has landed.  New Lean names in
`NormalCrossingInterface.lean` include
`AoyagiNormalCrossingChartCertificate`,
`AoyagiNormalCrossingChartCertificate.exponentData`,
`AoyagiNormalCrossingChartCertificate.mem_exponentData_activePairs`, and
`AoyagiNormalCrossingChartCertificate.ExtractionHypothesis`.  New Lean names
in `Theorem2FinalAssembly.lean` include
`AoyagiTheorem2SuppliedChartFinalBoundary`,
`AoyagiTheorem2SuppliedChartFinalBoundary.toSuppliedFinalBoundary`,
`AoyagiTheorem2SuppliedChartFinalBoundary.lambda_eq_theorem2Lambda_fromCeilData`,
`AoyagiTheorem2SuppliedChartFinalBoundary.poleOrder_eq_theorem2OrderFormula`,
and
`AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula`.
Reproduction:
`threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-spine-a0.md`.
Statement card:
`threads/02-analytic-interface/statement-card-a0-normal-crossing-chart-certificate-spine.md`.
Review:
`threads/02-analytic-interface/review-normal-crossing-chart-certificate-spine-a0.md`.

This records the source-facing finite chart/unit/monomial spine and projects it
to the existing exponent interface.  It is not Hironaka, analytic chart
coverage, analytic unit nonvanishing, Aoyagi Lemma 1, finite formula
equality, pole order without A0, or RLCT extraction.

The finite Jacobian/prior loss-shift socket has also landed.  New Lean names in
`NormalCrossingInterface.lean` include `jacobianPriorLossShift`,
`ratioAt_jacobianPriorLossShift_of_mem_activePairs`,
`exponentMinimum_jacobianPriorLossShift`,
`coordsInChartAtRatio_jacobianPriorLossShift`,
`countInChartAtRatio_jacobianPriorLossShift`,
`minCoordsInChart_jacobianPriorLossShift`,
`minCountInChart_jacobianPriorLossShift`, and
`exponentOrder_jacobianPriorLossShift`.  Reproduction:
`threads/02-analytic-interface/reproduction-normal-crossing-jacobian-prior-loss-shift-a0.md`.
Statement card:
`threads/02-analytic-interface/statement-card-a0-normal-crossing-jacobian-prior-loss-shift.md`.
Review:
`threads/02-analytic-interface/review-normal-crossing-jacobian-prior-loss-shift-a0.md`.

This keeps the loss exponent array fixed and shifts each Jacobian/prior
exponent from `h` to `h + m*k`.  It is finite exponent-array arithmetic only:
no regular-coordinate chart construction, analytic Jacobian/volume-form
calculation, normal crossings, pole order, or RLCT additivity is proved.

The chart-certificate lift of the same finite shift has also landed.  New Lean
names in `NormalCrossingInterface.lean` include
`AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift`,
`AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift_lossExp`,
`AoyagiNormalCrossingChartCertificate.jacobianPriorLossShift_jacobianPriorExp`,
`AoyagiNormalCrossingChartCertificate.exponentData_jacobianPriorLossShift`,
`AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift`,
and
`AoyagiNormalCrossingChartCertificate.exponentData_exponentOrder_jacobianPriorLossShift`.
Reproduction:
`threads/02-analytic-interface/reproduction-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`.
Statement card:
`threads/02-analytic-interface/statement-card-a0-normal-crossing-chart-certificate-jacobian-prior-loss-shift.md`.
Review:
`threads/02-analytic-interface/review-normal-crossing-chart-certificate-jacobian-prior-loss-shift-a0.md`.

This is certificate algebra on supplied chart data: it changes the
`jacobianPrior` field by multiplying a coordinate monomial and projects
definitionally to the finite exponent-data shift.  It is not regular-coordinate
construction, analytic Jacobian/volume-form control, chart coverage, pole
order, RLCT additivity, or extraction transfer from a reduced certificate.

## Latest A6 Update

The chart-certificate final socket now has a finite-certificate constructor.
New Lean names in `Theorem2FinalAssembly.lean`:
`AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_chart_minCount_eq_of_forall_le`
and
`AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_chartCount`.
Reproduction:
`threads/06-dln-translation/reproduction-theorem2-chart-finite-certificate-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-theorem2-chart-finite-certificate-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-chart-finite-certificate-bridge-a6.md`.

This replaces the opaque finite formula field of the chart final boundary with
explicit active-ratio and chart-count witnesses, while still assuming the
chart-level A0 extraction hypothesis.  It does not construct the chart
certificate, prove active-ratio bounds, prove chart-count bounds, prove Lemma 5
exactness, pole order without A0, or RLCT extraction.

The chart-certificate final socket now also has a displayed-ratio count
variant.  New Lean names in `Theorem2FinalAssembly.lean`:
`AoyagiTheorem2SuppliedChartFinalBoundary.of_activePair_ratioAt_eq_of_forall_le_of_countInChartAtRatio_eq_of_forall_le`
and
`AoyagiTheorem2SuppliedChartFinalBoundary.lambda_and_poleOrder_eq_fromCeilData_and_orderFormula_of_activePair_ratioCount`.
Reproduction:
`threads/06-dln-translation/reproduction-theorem2-chart-ratio-count-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-theorem2-chart-ratio-count-bridge.md`.
Review:
`threads/06-dln-translation/review-theorem2-chart-ratio-count-bridge-a6.md`.

This variant accepts chart counts at the displayed Theorem 2 lambda ratio and
uses the active-ratio minimum certificate before converting them to
global-minimum chart counts.  It does not prove the active-ratio bound,
ratio-count facts, Lemma 5 exactness, pole order without A0, or RLCT
extraction.

## Latest A2 Update

The Aoyagi Theorem 3 residual-product endpoint wrapper has landed. The new
Lean names are `ChartLocalSuffixState.residualProduct`,
`ChartLocalSuffixState.residualProduct_self`,
`ChartLocalSuffixState.residualProduct_castSucc`,
`ChartLocalSuffixState.suffixState_D_eq_residualProduct`,
`ChartLocalSuffixState.suffixState_blockDiagonal_exists_triangularBlockDiagonal_residualProduct`,
`productReduction_chartLocal_suffixChain_triangularBlockDiagonal_residualProduct_indexed`,
and
`PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-product.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-product.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-product.md`.

This proves the existing fixed-base product-reduction certificate can be read
in the Aoyagi form

```text
[I 0; F3 I] * total * [I F2; 0 I]
  = [Ctop 0; 0 residualProduct],
```

where `residualProduct` is the deterministic product of transformed Schur
residual blocks visited by the suffix recursion. This is not the raw
lower-right edge-block product. The abstract suffix-chain wrapper still keeps
the older all-`Bprev` determinant-chart hypothesis. It is still not chart
coverage from source rank hypotheses, exact-rank openness, Aoyagi Lemma 1,
analytic ideal transport, regular-coordinate RLCT bookkeeping, normal
crossings, or an RLCT consequence.

The A2 rank-stratum boundary has also landed.  New Lean names in
`ProductReductionBoundary.lean` include `paperEndpointFixedBaseEdgeRankStratum`,
`paperEndpointFixedBaseSourceRankStratum`,
`paperEndpointFixedBaseContinuousEdgesRecursiveResidualRanks`,
`PaperEndpointFixedBaseProductReductionRankStratumCertificate`,
`PaperEndpointFixedBaseProductReductionCertificate.residualRanks_of_edgeRankStratum`,
`PaperEndpointFixedBaseProductReductionCertificate.rankStratumCertificate`,
`PaperEndpointFixedBaseProductReductionCertificate.residualBlock_rank_eq_sourceRankSubProductRank`,
`paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin`,
`paperEndpointFixedBaseProductReductionRankStratumCertificate_selfBase_mem_nhdsWithin_source`,
`PaperEndpointFixedBaseProductReductionRankStratumLocalCertificate`,
`PaperEndpointProductReductionRankStratumLocalCertificate`, and
`exists_paperEndpointProductReductionRankStratumLocalCertificate`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-rank-stratum-boundary.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-rank-stratum-boundary.md`.
This packages exact layer ranks as a relative stratum, not as an ambient open
neighborhood.  On the source-shaped stratum it rewrites the visited residual
rank to `rEdge p - r` using the basepoint certificate.

The A2 fixed-base/source-rank-stratum endpoint wrapper has also landed.  New
Lean names in `ProductReductionBoundary.lean`:
`PaperEndpointFixedBaseTriangularResidualProductSourceRanks` and
`PaperEndpointFixedBaseProductReductionCertificate.exists_triangularBlockDiagonal_residualProduct_sourceRanks`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-source-rank-stratum-theorem3-boundary.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-source-rank-stratum-theorem3-boundary.md`.
Review:
`threads/03-block-product-reduction/review-a2-source-rank-stratum-theorem3-boundary.md`.
This bundles the triangular residual-product endpoint form with source-stratum
residual ranks.  It remains fixed-base and certificate-relative: it does not
prove exact-rank openness, source-stratum nonemptiness, regular-corner chart
production, Lemma 1 normalization, ideal transport, normal crossings, pole
order, or RLCT.

The A2 local source-rank endpoint package has also landed.  New Lean names in
`ProductReductionBoundary.lean`:
`paperEndpointFixedBaseSourceRankStratum_selfBase_mem`,
`paperEndpointFixedBaseTriangularSourceRanks_selfBase_mem_nhdsWithin_source`,
`PaperEndpointTriangularSourceRanksLocalCertificate`, and
`exists_paperEndpointTriangularSourceRanksLocalCertificate`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-source-rank-endpoint-package.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-source-rank-endpoint-package.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-source-rank-endpoint-package.md`.
This proves basepoint source-stratum membership from supplied rank data and
lifts the pointwise fixed-base source-rank endpoint wrapper to a local
relative-neighborhood conclusion over
`paperEndpointFixedBaseSourceRankStratum`.  It is still not exact-rank
openness, ambient source-stratum nonemptiness, full Theorem 3, Lemma 1
normalization, analytic ideal transport, normal crossings, pole order, or RLCT.

## Latest A5 Update

The Eq5 alpha-indexed branch source-label slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  New Lean names:
`aoyagiLemma5Eq5_alphaIndexedBranch_actualWidthLabel_of_widthBound`,
`aoyagiLemma5Eq5_alphaIndexedBranchLabel_mem_actualWidthLabelFinset_of_widthBound`,
and `aoyagiLemma5Eq5_alphaIndexedBranchLabel_injOn`.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-source-label.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-source-label-a5.md`.
This proves branchwise actual-width label legality and supplied branch-label
injectivity for alpha-indexed Eq5 strict-offset branch families under explicit
branchwise hypotheses.  It does not construct Eq5 branches, prove alpha-domain
coverage, selected-span coverage, terminal exactness, classifier/back-to-label
coverage, pole order, normal crossings, or RLCT extraction.

The Eq5 alpha-indexed branch-label image wrapper has also landed in
`Lemma5SourceLabel.lean`.  New Lean names:
`aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_subset_actualWidthLabelFinset_of_widthBound`
and `aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_of_alphaInj`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-label-image.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-label-image-a5.md`.
This proves only that the supplied branch-label image is a subset of
`actualWidthLabelFinset L n` under the existing branchwise hypotheses, and
that the image has the supplied branch-family cardinality under supplied alpha
injectivity.  It is not branch construction, alpha-domain coverage,
selected-span coverage, terminal exactness, classifier/back-to-label coverage,
pole order, normal crossings, or RLCT extraction.

The Eq5 alpha-indexed branch cardinal-bound wrapper has also landed in
`Lemma5SourceLabel.lean`.  New Lean names:
`aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_le_actualWidthLabelFinset_card`
and `aoyagiLemma5Eq5_alphaIndexedBranch_card_le_actualWidthLabelFinset_card`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-card-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-card-bound-a5.md`.
This converts the supplied image subset into an image-cardinality bound, and
then, under supplied alpha injectivity, into a bound on the supplied branch
family itself.  It is not branch construction, alpha-domain coverage,
selected-span coverage, terminal exactness, classifier/back-to-label coverage,
pole order, normal crossings, or RLCT extraction.

The Eq5 alpha-indexed offset-cardinality bridge has also landed in
`Lemma5SourceLabel.lean`.  New Lean name:
`aoyagiLemma5Eq5_alphaIndexedBranchLabelImage_card_eq_offsetValueSet_card`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-offset-card-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-offset-card.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-offset-card-a5.md`.
This uses supplied alpha-domain coverage and supplied alpha injectivity to
show cardinal equality between the branch-label image and the strict Eq5
offset-value set.  It is not set equality between Sigma-valued labels and
integer offset values, and it is not branch construction, source-label
legality, actual-width coverage, terminal exactness, classifier/back-to-label
coverage, pole order, normal crossings, or RLCT extraction.

The terminal branch introduced-domain capacity wrapper has also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_introducedLabelFinset_card`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_introducedLabelFinset_card_of_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_introducedLabelFinset_card_of_branchLabel_injOn`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-branch-introduced-domain-capacity-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-branch-introduced-domain-capacity.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-branch-introduced-domain-capacity-a5.md`.
This is finite introduced-domain capacity bookkeeping for supplied terminal
branches.  It is not branch-label injectivity, no-extra terminal-minimum
coverage, exact terminal-minimum cardinality, pole order, normal crossings, or
RLCT extraction.

The terminal-minimum lower-bound wrapper has also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_card_le_terminalMinimumLabels_card`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card_le_terminalMinimumLabels_card_of_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.suppliedBranchCount_le_terminalMinimumLabels_card_of_branchLabel_injOn`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-lower-bound-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-lower-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-lower-bound-a5.md`.
This is the easy lower-bound direction from supplied candidates attaining the
minimum.  It is not no-extra terminal-minimum coverage, exact
terminal-minimum cardinality, pole order, normal crossings, or RLCT
extraction.

The upper-bound classifier exactness wrappers have also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_upperBoundClassifier`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_upperBoundClassifier`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_upperBoundClassifier_and_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_upperBoundClassifier`.
These prove that a supplied `UpperBoundClassifier` is enough to identify the
finite terminal-minimum label set with the supplied branch-label image; adding
supplied branch-label injectivity gives exactness, bijection, and the exact
finite count.  This does not prove the classifier or injectivity from
Aoyagi's source and does not prove pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-exactness-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-upper-bound-classifier-exactness.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-upper-bound-classifier-exactness-a5.md`.

The counted-datum classifier cardinal-squeeze wrappers have also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_countDatumClassifier_and_branchLabel_injOn`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumClassifier_and_branchLabel_injOn`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumClassifier_and_branchLabel_injOn`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_bijOn_terminalMinimumLabels_of_countDatumClassifier_and_branchLabel_injOn`.
These use the supplied counted-datum classifier upper bound and supplied
branch-label injectivity to identify `terminalMinimumLabels` with
`branchLabelImage` by finite cardinality squeeze.  They do not construct a
back-to-label map, source classifier, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-classifier-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-classifier-cardinal-squeeze-a5.md`.

The generic terminal exactness/cardinal-bound equivalence has also landed in
`Lemma5TerminalBridge.lean`.  New Lean names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_eq_branchLabelImage_of_card_bound_and_branchLabel_injOn`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound`.
This removes the counted-datum/classifier wrapper from the finite obstruction:
once supplied branches are known to attain the terminal minimum, supplied
branch-label injectivity and the supplied numeric upper bound
`terminalMinimumLabels.card <= a*(n+1-a)+1` are equivalent to terminal
exactness.  It does not prove the upper bound or injectivity from source and
does not prove pole order, normal crossings, or RLCT.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-card-bound-equivalence-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-card-bound-equivalence.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-card-bound-equivalence-a5.md`.

## Latest A4 Update

The Case 2 post-pivot source-residual representative has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  New Lean names:
`case2DisplayedPostPivotSourceResidual`,
`case2SourceResidualBlock_postPivotSourceResidual`, and
`case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_sourceFollowingFactor`.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-source-residual-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-source-residual.md`.
Review:
`threads/04-blow-up-certificate/review-case2-post-pivot-source-residual-a4.md`.

This packages the displayed post-pivot lower-right block as a zero-extended
source-coordinate residual function and proves restriction recovery at
`(S,J+1)`.  It also rewrites the existing paper-`C'` continuing lower-row
product using `case2SourceResidualBlock` and the next same-stage
`case2SourceFollowingFactor`.  It is finite representative bookkeeping only:
no chart production, source-produced successor post-data, transition
invariance, terminal relabeling, normal crossings, pole order, or RLCT follows.

The Lemma 4 same-coordinate bridge has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`.  Source check:
Aoyagi's Definition 4 defines componentwise vector order, but not a unique
endpoint-selection map from a vector `T` to `(H_j),(S_j)`.  Thus
`Ttilde <= T <= Ttilde'` alone is not accepted as a proof of the terminal
endpoint sandwich.  Lean proves only the conservative wrapper with explicit
same-coordinate hypotheses:
`aoyagiLemma4_terminalEndpointBounds_of_sameCoordinate`,
`aoyagiLemma4_Hlast_eq_zero_of_sameCoordinate`,
`aoyagiLemma4_twoValueCount_of_sameCoordinate`, and
`aoyagiLemma4_sameCoordinate_freeHighCount_lemma3A_eq_min`.  Reproduction and
review artifacts:
`threads/05-arithmetic-tail/reproduction-lemma4-same-coordinate-bridge-a5.md`,
`threads/05-arithmetic-tail/statement-card-a5-lemma4-same-coordinate-bridge.md`,
and
`threads/05-arithmetic-tail/review-lemma4-same-coordinate-bridge-a5.md`.
The full Lemma 4 theorem remains blocked by the source `T -> (H_j),(S_j)`
correspondence, the same-coordinate hypotheses for Aoyagi's displayed
extremal vectors, the two-value hypothesis, vector admissibility, terminal
exponent rewrite, and correspondence to `lambda`.

The `Htilde` chain arithmetic slice has landed in
`lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`.  It formalises the
finite displayed lower and upper chains from Aoyagi's Lemma 4/Lemma 5
discussion: selected-width prefix helpers, `H_0=M(S_1)`, high-first and
low-first increment patterns, terminal equality with
`aoyagiLemma4TerminalEndpoint`, and pointwise gap equal to
`aoyagiLemma5IntervalExcess`.  Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-htilde-chain-arithmetic-a5.md` and
`threads/05-arithmetic-tail/statement-card-a5-htilde-chain-arithmetic.md`.
Review artifact:
`threads/05-arithmetic-tail/review-htilde-chain-arithmetic-a5.md`.  This does
not prove the source `T -> (H_j),(S_j)` correspondence, same-coordinate
hypotheses for the displayed extremal vectors, arbitrary-vector two-value
increments, vector admissibility, Lemma 5 chart-family/order count, pole
order, normal crossings, or RLCT extraction.

The `Htilde` interval-bound slice has landed in the same Lean module.
It proves terminal zero for the displayed chains under the selected-width sum,
pointwise lower-to-upper chain order, finite interval offset/value sets with
cardinality `aoyagiLemma5IntervalSize`, equivalence between interval-value
membership and same-coordinate chain bounds, a supplied-coordinate vector
membership wrapper, chain-bound `H_ell=0`, displayed-chain two-value counts,
and conditional Lemma 4/Lemma 3 wrappers under the still-explicit arbitrary
chain two-value hypothesis.  Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-htilde-interval-bounds-a5.md` and
`threads/05-arithmetic-tail/statement-card-a5-htilde-interval-bounds.md`.
Review artifact:
`threads/05-arithmetic-tail/review-htilde-interval-bounds-a5.md`.  This still
does not prove the source `T -> (H_j),(S_j)` correspondence, same-coordinate
hypotheses for Aoyagi's displayed extremal vectors, arbitrary-vector
two-valued increments, vector admissibility, Lemma 5 chart-family/order count,
pole order, normal crossings, or RLCT extraction.

The Lemma 4 binary prefix-delta bridge has landed in
`lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`.  It defines
`aoyagiLemma4IncrementPrefix` as `D_j=P(j)-H_j-j*(M-1)`, proves
`aoyagiLemma4F_eq_pred_add_incrementPrefixDelta`, and derives the two-value
increment hypothesis and count wrappers from a supplied binary-delta
hypothesis.  Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-lemma4-binary-prefix-delta-a5.md` and
`threads/05-arithmetic-tail/statement-card-a5-lemma4-binary-prefix-delta.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma4-binary-prefix-delta-a5.md`.  This
does not prove source exponent vectors imply binary prefix deltas,
same-coordinate chain bounds imply binary prefix deltas, vector-coordinate
correspondence, vector admissibility, Lemma 5 chart-family/order count, pole
order, normal crossings, or RLCT extraction.

The `Htilde` value-set count has landed in the same module.  It adds the
Nat-indexed wrapper `aoyagiHtildeIntervalValueSetNat`, guarded cardinality
theorems, and the source-facing finite count
`aoyagiHtildeIntervalValueSetNat_excess_sum_Icc`.  This proves only
`1 + sum_{j=1}^{ell-1}(|I_j|-1)=a(ell-a)+1` for same-coordinate values between
the displayed chains.  Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-htilde-value-set-count-a5.md` and
`threads/05-arithmetic-tail/statement-card-a5-htilde-value-set-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-htilde-value-set-count-a5.md`.
This does not prove Lemma 5's
chart-family admissibility, coverage, displayed vector constructions,
pole-order interpretation, normal crossings, or RLCT extraction.

The Lemma 4 prefix-delta endpoint/count bridge has landed in the same
module.  It names `aoyagiLemma4IncrementPrefixDelta`, proves `D_0=0`,
`D_ell=a`, telescoping of successive deltas, sum of deltas `=a`, and exact
counts of supplied binary deltas, with a same-coordinate `Htilde`-chain-bound
wrapper.  Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-lemma4-prefix-delta-endpoint-count-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma4-prefix-delta-endpoint-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma4-prefix-delta-endpoint-count-a5.md`.
This does not prove source exponent vectors or chain bounds provide binary
deltas, vector-coordinate correspondence, vector admissibility, Lemma 5
chart-family/order count, pole order, normal crossings, or RLCT extraction.

The Lemma 4 same-coordinate binary-delta free-count wrapper has landed in the
same module.  The proved Lean names are
`aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta` and
`aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min`.
They combine supplied same-coordinate vector bounds with supplied binary
prefix deltas to reach the existing free-count Lemma 3 numerator equality.
Reproduction and statement card:
`threads/05-arithmetic-tail/reproduction-lemma4-same-coordinate-binary-delta-free-count-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma4-same-coordinate-binary-delta-free-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma4-same-coordinate-binary-delta-free-count-a5.md`.
This does not prove the source `T -> (H_j),(S_j)` correspondence,
binary deltas from source vectors, vector admissibility, terminal exponent
rewriting, correspondence to `lambda`, Lemma 5 chart-family/order count, pole
order, normal crossings, or RLCT extraction.  The next source-facing target is
Aoyagi's Lemma 5 displayed-family realisation, especially equations `(3)` and
`(4)` on pp. 26-27.

The Lemma 5 displayed-family audit and equation `(4)` own-coordinate sanity
check have landed in the same module.  The proved Lean names are
`aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min` and
`aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min`.  They prove only that
under `p<=a` and `p<=ell-a`, the printed equation `(4)` own-coordinate value
`Htilde'_p-p` equals `Htilde_p`.  The companion blocked audit records that
full equations `(3)`/`(4)` source-family realisation still lacks legal-label
bounds, terminal/tail conventions for `tilde t=0`, complete index guards, and
the Case 1(2) chart-sequence bridge. Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-own-coordinate-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-own-coordinate.md`.
Blocked audit:
`threads/05-arithmetic-tail/blocked-audit-lemma5-displayed-family-realisation-a5.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-own-coordinate-a5.md`.

The equation `(4)` guard arithmetic has also landed.  The proved Lean names
are `aoyagiLemma5IntervalExcess_eq_self_of_le_min`,
`aoyagiLemma5Eq4_selectedIndexGuard_iff`, and
`aoyagiHtildeLowerNat_add_one_labelBounds_iff_prefixCrossing`.  They expose
the exact selected-index guard `p+1<=a` for `S_(p+ell-a+2)` and rephrase
`1<=Htilde_p+1<=W_(p+1)` as the prefix-crossing condition
`P_p < pM <= P_(p+1)`.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-guard-arithmetic-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-guard-arithmetic.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-guard-arithmetic-a5.md`.

The equation `(3)` guard arithmetic has also landed.  The proved Lean names
are `aoyagiLemma5Eq3_selectedIndexGuard_iff`,
`aoyagiHtildeUpperNat_one_sub_lowerNat_one_of_pos_of_lt`, and
`aoyagiHtildeUpperNat_one_add_one_labelBounds_iff_widthGuards`.  They expose
the exact selected-index guard `1<=a` for `S_(ell-a+2)`, prove the first
Htilde gap is `1` in the interior case, and rephrase the bounds for
`k=Htilde'_1+1` as `M-1<=W_1+W_2` and `W_1+2<=M`.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-guard-arithmetic-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-guard-arithmetic.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-guard-arithmetic-a5.md`.

The first Definition 3 source-inequality consequence for Lemma 5 labels has
landed.  The proved Lean names are
`aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality`,
`aoyagiPrefixSum_sub_current_add_one_le_mul_of_selectedWidth_le_pred`,
`aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_selectedWidth_le_pred`, and
`aoyagiHtildeLowerNat_add_one_le_selectedWidth_of_sourceSelectedInequality`.
They prove that selected widths are at most `M-1`, hence equation `(4)`'s
upper label bound follows from Definition 3's strict selected-width
inequality.  Reproduction:
`threads/05-arithmetic-tail/reproduction-definition3-selected-width-upper-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-definition3-selected-width-upper-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-definition3-selected-width-upper-label-a5.md`.

The tail half of the same Definition 3 label calculation has also landed.
The proved Lean names are
`aoyagiPrefixSum_mul_le_of_selectedWidth_le_pred`,
`aoyagiPrefixSum_mul_le_of_sourceSelectedInequality`,
`aoyagiHtildeLowerNat_add_one_pos_of_selectedWidth_le_pred`,
`aoyagiHtildeLowerNat_add_one_pos_of_sourceSelectedInequality`, and
`aoyagiHtildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`.
They prove `pM<=P_(p+1)` by bounding the tail after `P_(p+1)`, hence combine
with the previous-prefix estimate to prove
`1<=Htilde_p+1<=W_(p+1)` under `1<=ell`, `a<=ell`, `1<=p`, `p<=a`, and
Definition 3's selected-width hypotheses.
Reproduction:
`threads/05-arithmetic-tail/reproduction-definition3-selected-width-label-bounds-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-definition3-selected-width-label-bounds.md`.
Review artifact:
`threads/05-arithmetic-tail/review-definition3-selected-width-label-bounds-a5.md`.

The corrected local equation `(4)` arithmetic package has also landed.  The
proved Lean name is
`aoyagiLemma5Eq4_localData_of_sourceSelectedInequality`.  Under Definition 3's
selected-width hypotheses and guards `1<=p`, `p+1<=a`, and `p<=ell-a`, it
packages the selected-index bound `p+(ell-a)+2<=ell+1`, the own-coordinate
identity `Htilde'_p-p=Htilde_p`, and the legal label bounds
`1<=Htilde_p+1<=W_(p+1)`.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-local-data-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-local-data.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-local-data-a5.md`.

The first conditional source-vector-facing equation `(4)` certificate has
landed in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved
objects are `AoyagiSelectedCutpoints`, `AoyagiSelectedCutpoints.point`,
`AoyagiSelectedCutpoints.block`,
`AoyagiSelectedCutpoints.leftEndpoint_mem_block`,
`AoyagiSelectedCutpoints.cut_strictMono`,
`AoyagiSelectedCutpoints.point_strict_of_lt`,
`AoyagiSelectedCutpoints.point_le_of_le`,
`AoyagiSelectedCutpoints.block_index_unique`,
`AoyagiSelectedCutpoints.block_leftEndpoint_iff`,
`AoyagiSelectedCutpoints.block_leftEndpoint_lt_of_ne`,
`AoyagiSelectedCutpoints.leftEndpoint_lt_of_lt_block`,
`AoyagiSelectedCutpoints.block_mem_selectedSpan`,
`AoyagiSelectedCutpoints.exists_block_of_mem_selectedSpan`,
`AoyagiSelectedCutpoints.exists_block_iff_mem_selectedSpan`,
`AoyagiSelectedCutpoints.not_block_terminalEndpoint`,
`AoyagiLemma5Eq4PiecewiseSourceVector`,
`aoyagiLemma5Eq4_boundaryIndex_le_ell_of_piecewiseSourceVector`,
`aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff`,
`aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff`,
`aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard`,
`aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard`,
`aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary`,
`aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary`,
`AoyagiLemma5Eq4SelectedSpanBranchValue`,
`aoyagiLemma5Eq4_branchValue_of_block`,
`aoyagiLemma5Eq4_selectedSpan_branchValue`,
`aoyagiLemma5Eq4_prefix_leftEndpoint`,
`aoyagiLemma5Eq4_middle_leftEndpoint`,
`aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt`,
`aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension`,
`aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary`,
`aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary`, and
`aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality`.  The
theorem says that a supplied equation `(4)` piecewise branch certificate gives
the correct own-coordinate value and legal label bounds under the repaired
guards and Definition 3 hypotheses; the selected-span classifier says that
the same supplied certificate gives one of the advertised branch values for
every source index in the selected span only; and the terminal-endpoint
boundary says a supplied endpoint extension to `Htilde'_ell` is zero, without
proving terminal-vector realisation.  The supplied certificate now carries
the source-boundary guards `a<=ell` and `p+1<=a`, and Lean records the
consequence `p+(ell-a)+1<=ell` so the displayed boundary is not accepted only
through the totalized `point` fallback.  Lean also records the strict versus
terminal split: `p+1<a` puts the boundary in the next selected block and
inside the half-open selected span, while `p+1=a` identifies it with the
terminal endpoint and excludes it from every half-open selected block.
Combining the terminal-collision branch with a separately supplied terminal
extension to `Htilde'_ell` forces the last-width compatibility
`W_(ell+1)=M-p+1`; if that compatibility fails, the supplied branch
certificate cannot also satisfy that terminal extension.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-piecewise-certificate-a5.md`.
Boundary-split reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-boundary-split-a5.md`.
Selected-block bookkeeping reproduction:
`threads/05-arithmetic-tail/reproduction-selected-block-bookkeeping-a5.md`.
Selected-block coverage reproduction:
`threads/05-arithmetic-tail/reproduction-selected-block-coverage-a5.md`.
Selected-span branch-value reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-selected-span-branch-value-a5.md`.
Terminal endpoint reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-endpoint-boundary-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-piecewise-certificate.md`.
Selected-span statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-selected-span-branch-value.md`.
Terminal endpoint statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-terminal-endpoint-boundary.md`.
Boundary-split statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-boundary-split.md`.
Terminal-extension obstruction reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-extension-obstruction-a5.md`.
Terminal-extension obstruction statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-terminal-extension-obstruction.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-piecewise-certificate-a5.md`.
Selected-block review:
`threads/05-arithmetic-tail/review-selected-block-bookkeeping-a5.md`.
Selected-block coverage review:
`threads/05-arithmetic-tail/review-selected-block-coverage-a5.md`.
Selected-span branch-value review:
`threads/05-arithmetic-tail/review-lemma5-eq4-selected-span-branch-value-a5.md`.
Terminal endpoint review:
`threads/05-arithmetic-tail/review-lemma5-eq4-terminal-endpoint-boundary-a5.md`.

The equation `(4)` actual-width label bridge has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`, imported by
`lean/DLNFibre.lean`.  The proved theorem is
`aoyagiLemma5Eq4_actualWidthLabel_of_widthCompatibility`.  It turns the
selected-width label bounds for `k=Htilde_p+1` into the blow-up predicate
`actualWidthLabel` only under explicit source-layer range, selected-width /
actual-width compatibility, and Nat/Int label compatibility hypotheses.  It
does not prove selected widths are actual widths, introduced-label status,
displayed-vector construction, terminality, chart coverage, or Lemma 5 order
count.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-actual-width-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-actual-width-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-actual-width-label-a5.md`.

## Latest A2 update

The A2 table row above was originally written before the endpoint packaging
wrapper landed. As of the current checkpoint,
`productReduction_paperChainMap_endpointChartData_suffixChain_rightElim` is
proved in `lean/DLNFibre/DLN/Aoyagi/ThroughLayerMatrix.lean`; its statement
card is
`threads/03-block-product-reduction/statement-card-a2-paper-endpoint-suffix-chain-right-elim.md`.
Xhigh statement-shape review confirms the reversal orientation and the
pointwise adapted-coordinate scope.
The remaining blocked A2 items are the topological rank/open-neighborhood
bridge, a source-faithful full Theorem 3 statement, and analytic/certificate
transport.

Second latest A2 update: the first rank/open split has landed. Proved Lean
theorems are `rank_toMatrix_eq_finrank_range`,
`rank_schurComplement_eq_sub_rank_fromBlocks`,
`lowerRightBlock_paperAdaptedReverseEdgeMatrix_rank_eq_sub`, and the
`ChartTopology.lean` determinant-chart openness/neighborhood theorems. Statement
cards:
`threads/03-block-product-reduction/statement-card-a2-residual-rank-bridge.md`
and
`threads/03-block-product-reduction/statement-card-a2-determinant-chart-topology.md`.
Remaining blocked A2 items are fixed basepoint chart data for nearby variable
layers, source-faithful exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Third latest A2 update: the endpoint fixed-chain basepoint certificate has
landed in `lean/DLNFibre/DLN/Aoyagi/BasepointCertificate.lean`. Proved Lean
objects/theorems include `paperTotalMap`, `paperEndpointChartData`,
`paperEndpointAdaptedEdgeMatrix`, `paperEndpointUnitriangularLeft`,
`paperEndpointAdaptedTotalMatrix`,
`lowerRightBlock_throughSubspaceEndpointAdaptedEdgeMatrix_rank_eq_sub`,
`lowerRightBlock_paperEndpointAdaptedEdgeMatrix_rank_eq_sub`,
`paperEndpointAdaptedTotalMatrix_eq_fromBlocks_one_zero_zero`,
`productReduction_paperEndpointAdaptedTotalMatrix_suffixChain_rightElim`,
`PaperEndpointBasepointCertificate`,
`paperEndpointBasepointCertificate_of_isCompl`, and
`exists_paperEndpointBasepointCertificate`. Statement card:
`threads/03-block-product-reduction/statement-card-a2-basepoint-certificate.md`.
Remaining blocked A2 items are fixed coordinate families for variable nearby
chains, source-faithful exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Fourth latest A2 update: the fixed-basepoint variable-chain layer has landed.
Generic block API in `ProductReduction.lean`: `lowerLeftBlock`,
`fromBlocks_corners`, `schurResidualBlock`, and
`rank_schurResidualBlock_eq_sub_rank_of_identityCornerDetChart`. Fixed-base
paper wrappers in `lean/DLNFibre/DLN/Aoyagi/FixedBasepointChart.lean`:
`paperEndpointFixedBaseBasis`, `paperEndpointFixedBaseChainMapMatrix`,
`paperEndpointFixedBaseEdgeMatrix`, `paperEndpointFixedBaseTotalMatrix`,
`paperEndpointFixedBaseChainMapMatrix_succ_right`,
`paperEndpointFixedBaseTotalMatrix_eq_chainMapMatrix`,
`paperEndpointFixedBaseEdgeMatrix_selfBase`,
`paperEndpointFixedBaseTotalMatrix_selfBase`,
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_sub`, and
`paperEndpointFixedBaseTwoEdgeTotalMatrix_eq_edge1_mul_edge0`. Statement card:
`threads/03-block-product-reduction/statement-card-a2-fixed-basepoint-chart.md`.
Remaining blocked A2 items are the iterated chart-local product reduction in
fixed bases, fixed-coordinate determinant-neighborhood packaging for variable
chains, source-faithful exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Fifth latest A2 update: the first fixed-base variable-chart suffix step has
landed. Generic theorem:
`productReduction_chartLocal_suffixStep_fromBlocks_indexed` in
`ProductReduction.lean`; fixed-base wrapper:
`paperEndpointFixedBase_chartLocal_suffixStep` in
`FixedBasepointChart.lean`; supporting rank bridge:
`rank_paperEndpointFixedBaseEdgeMatrix_eq_finrank_range` and
`rank_schurResidualBlock_paperEndpointFixedBaseEdgeMatrix_eq_range_sub`.
The statement card
`threads/03-block-product-reduction/statement-card-a2-fixed-basepoint-chart.md`
was updated.

Sixth latest A2 update: the all-layer explicit-chart suffix-chain induction has
landed. Generic theorem:
`productReduction_chartLocal_suffixChain_blockDiagonal_indexed` in
`ProductReduction.lean`; fixed-base wrapper:
`productReduction_paperEndpointFixedBaseChainMapMatrix_chartLocal_blockDiagonal`
in `FixedBasepointChart.lean`, supported by
`paperEndpointFixedBaseChainMapMatrix_proof_irrel`. At that checkpoint the next
blocked item was fixed-coordinate determinant-neighborhood packaging for
variable chains, followed by exact rank-stratum packaging, the full Theorem 3
statement, and analytic/certificate transport.

Seventh latest A2 update: the matrix-local transformed determinant-neighborhood
package has landed. Generic topology helpers:
`leftMul_identityCornerDetChart_mem_nhds` and
`fromBlocks_leftMul_identityCornerDetChart_mem_nhds` in `ChartTopology.lean`;
fixed-base wrapper:
`paperEndpointFixedBaseEdgeMatrix_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean`. The theorem is pointwise in a fixed edge `p` and
fixed accumulated block `Bprev`; it does not assert a single neighborhood
working for all `Bprev`. Remaining blocked A2 items are pulling these
matrix-space neighborhoods back along a formal topology/continuity statement
for fixed-coordinate variable chains, source-faithful exact rank-stratum
packaging, the full Theorem 3 statement, and analytic/certificate transport.

Eighth latest A2 update: the single-edge continuous-linear-map pullback has
landed. Generic theorem `continuous_linearMap_toMatrix` in `ChartTopology.lean`
proves continuity of fixed-basis matrix coordinates on `E →L[K] F`; fixed-base
wrapper
`paperEndpointFixedBaseContinuousEdge_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` pulls the transformed determinant chart back to a
neighborhood of the base edge in the continuous-linear-map topology. Remaining
blocked A2 items are product/chain-neighborhood assembly beyond a fixed
prescribed edge-family chart datum, source-faithful exact rank-stratum
packaging, the full Theorem 3 statement, and analytic/certificate transport.

Ninth latest A2 update: finite product-topology assembly for fixed transformed
edge charts has landed. Fixed-base wrapper
`paperEndpointFixedBaseContinuousEdges_selfBase_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` says that, for a prescribed family of accumulated
upper blocks `Bprev p`, all transformed determinant-chart predicates hold on a
neighborhood of the base continuous reversed-edge family. This uses only finite
intersection/Pi-topology assembly from the one-edge theorem. It does not assert
a neighborhood working for all `Bprev`, does not connect to the
induction-produced `Bprev`, does not make exact rank strata open, and does not
prove Aoyagi Theorem 3.

Tenth latest A2 update: the variable-`Bprev` continuity handoff has landed.
Fixed-base wrapper
`paperEndpointFixedBaseContinuousEdges_variableBprev_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` says that if a parameterized continuous
reversed-edge family and a parameterized accumulated-upper-block family `Bprev`
are continuous at `x0`, and all transformed determinant charts hold at `x0`,
then they hold in a neighborhood of `x0`. This is not a construction of the
recursive `Bprev`; pen-and-paper reproduction identifies the next algebraic
target as the deterministic update
`Bnext = (topLeftCorner ([I Bprev; 0 I] * E p))⁻¹ *
upperRightBlock ([I Bprev; 0 I] * E p)` under recursive chart hypotheses.

Eleventh latest A2 update: the deterministic one-step suffix state has landed.
`ChartLocalSuffixState` packages the current chart-local suffix data, while
`ChartLocalSuffixState.transformedEdge`, `ChartLocalSuffixState.step`, and
`ChartLocalSuffixState.step_blockDiagonal` in `ProductReduction.lean` formalize
the recurrence that was hidden inside the existential suffix-chain proof. The
step theorem proves preservation of the block-diagonal invariant under the
recursive determinant-chart hypothesis for the transformed edge. It does not
yet define or prove the full recursive suffix-chain state from `j` down to `i`.

Twelfth latest A2 update: the deterministic recursive suffix state has landed.
`ChartLocalSuffixState.terminal`, `ChartLocalSuffixState.suffixState`,
`ChartLocalSuffixState.suffixState_self`,
`ChartLocalSuffixState.terminal_blockDiagonal`,
`ChartLocalSuffixState.suffixState_castSucc`, and
`ChartLocalSuffixState.suffixState_blockDiagonal` now define the state obtained
by iterating the one-step recurrence downward and prove the recursive
block-diagonal invariant under recursive determinant-chart hypotheses. The
older public theorem `productReduction_chartLocal_suffixChain_blockDiagonal_indexed`
is now a wrapper extracting its witnesses from this deterministic state. This
is still algebraic: continuity of the recursive state and source-faithful chart
neighborhoods remain open.

Thirteenth latest A2 update: the recursive `Bprev` topology handoff has landed.
`continuousAt_matrix_inv_of_isUnit_det`,
`continuousAt_chartLocalSuffixState_step_B`, and
`continuousAt_chartLocalSuffixState_suffixState_B` in `ChartTopology.lean`
prove continuity of the accumulated upper block produced by the deterministic
suffix recursion, under recursive basepoint determinant-chart hypotheses. The
fixed-base theorem
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart`
in `FixedBasepointChart.lean` feeds that actual recursive `Bprev` family into
the existing variable-`Bprev` chart-neighborhood handoff. This remains a chart
neighborhood theorem under supplied basepoint chart hypotheses; exact-rank
neighborhoods, certificate transport, and the full source Theorem 3 statement
remain open.

Fourteenth latest A2 update: the endpoint block-diagonal neighborhood handoff
has landed. `FixedBasepointChart.lean` now includes fixed-base coordinate
wrappers for arbitrary reversed edge families,
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges`,
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges`, and
`paperEndpointFixedBaseTotalMatrixOfReverseEdges`. The theorem
`paperEndpointFixedBaseChainMapMatrixOfReverseEdges_recursiveChart_blockDiagonal`
applies `ChartLocalSuffixState.suffixState_blockDiagonal` directly at the
endpoint, using only the recursive determinant charts actually visited by the
suffix recursion. The topology wrappers
`paperEndpointFixedBaseContinuousEdgesRecursiveBlockDiagonal`,
`paperEndpointFixedBaseContinuousEdges_recursiveBprev_blockDiagonal_mem_nhds`,
and
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_mem_nhds`
then say that a continuous reversed-edge family based at `reverseEdge W B` has
a neighborhood on which the endpoint product has the deterministic block form
in endpoint bases fixed from `B`. This still does not prove exact-rank
neighborhoods, certificate transport, or the full source Theorem 3 statement.

Fifteenth latest A2 update: a small residual-rank and `D` recurrence API has
landed. `ChartLocalSuffixState.residualBlock`,
`ChartLocalSuffixState.suffixState_D_self`, and
`ChartLocalSuffixState.suffixState_D_castSucc` in `ProductReduction.lean` name
the Schur residual block actually visited by the recursive suffix state and the
recurrence `D_next = D_tail * residualBlock`; this is an adapted residual
recurrence, not a product of raw edge residuals. In `FixedBasepointChart.lean`,
`rank_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_eq_finrank_range` and the
transformed residual-rank wrappers prove pointwise rank formulas for arbitrary
reversed edge families under explicit determinant-chart and exact-rank
hypotheses. These theorems do not assert that exact-rank conditions hold in a
neighborhood. The follow-on theorem
`paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_blockDiagonal_rankImp_mem_nhds`
packages the honest neighborhood boundary: recursive charts and endpoint block
form hold nearby, and transformed residual-rank conclusions are available
nearby as implications from exact pointwise edge ranks.

Sixteenth latest A2 update: the source-facing elementary product-reduction
boundary has landed in `lean/DLNFibre/DLN/Aoyagi/ProductReductionBoundary.lean`.
`PaperEndpointFixedBaseProductReductionCertificate` packages the three proved
fixed-base fields: recursive determinant charts, deterministic endpoint block
form, and residual-rank implications. The local certificate
`PaperEndpointFixedBaseProductReductionLocalCertificate` adds the basepoint
certificate and the neighborhood membership, and
`exists_paperEndpointProductReductionLocalCertificate` chooses a total-kernel
complement for a continuous reversed-edge family based at `B`. This remains an
elementary/topological A2 boundary only: no exact-rank openness, no analytic
ideal-germ transport, no regular-suspension/RLCT additivity, and no
normal-crossing extraction is included.

Seventeenth latest A2 update: the product-difference entry-ideal boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`,
with generic support in `lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`.  The new
generic facts are `matrixEntryIdeal_neg_eq`,
`matrixEntryIdeal_fromBlocks_eq_fourMatrixEntryIdeal`, and
`matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_fourMatrixEntryIdeal`.
The boundary facts include
`matrixEntryIdeal_triangularBlockProductDifference_eq_fourMatrixEntryIdeal`,
`PaperEndpointFixedBaseProductDifferenceEntryIdealSourceRanks`,
`PaperEndpointFixedBaseTriangularResidualProductSourceRanks.exists_productDifferenceEntryIdeal`,
`PaperEndpointFixedBaseTriangularResidualProductSourceRanks.toProductDifferenceEntryIdealSourceRanks`,
`paperEndpointFixedBaseProductDifferenceEntryIdeal_selfBase_mem_nhdsWithin_source`,
`PaperEndpointProductDifferenceEntryIdealLocalCertificate`, and
`exists_paperEndpointProductDifferenceEntryIdealLocalCertificate`.  This is
only scalar matrix-entry-ideal algebra for endpoint matrices: no analytic
germ-ideal transport, exact-rank openness, full Theorem 3, regular-suspension,
normal crossings, pole order, or RLCT is included.

## Latest A4 update

The arbitrary selected-entry center facts have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
`case2_selectedEntryChartMap_value_mem_of_mem`,
`case2_selectedEntryChartMap_center_dvd_of_mem`,
`case1_selectedEntryChartMap_value_mem_of_mem`, and
`case1_selectedEntryChartMap_center_dvd_of_mem`. They specialize the finite
map `selectedEntryChartMap` to arbitrary selected entries/generators already
known to belong to the Case 2 residual-block center or Case 1 center. The
result is only chart-index bookkeeping: `u` occurs in the finite substitution
value set, witnessed by the selected pivot, and all transformed finite-center
generators are divisible by `u`. It does not prove an affine blow-up atlas,
chart coverage, non-displayed transition formulas, row/column permutation
symmetry, regularity/Jacobian facts, exponent updates, termination,
normal-crossing certificates, or RLCT extraction.

Second latest A4 update: the generic pivot-first `Q/P` algebra bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names
include `pivotComplement`, `pivotFirstIndexEquiv`, `pivotFirstMatrix`,
`pivotFirstX`, `pivotFirstY`, `pivotFirstD`,
`pivotFirstMatrix_eq_pivotPreQBlock`,
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul_pivotQ`, and
`weightedPivotBlockRowOp_mul_diagonal_mul_pivotFirstMatrix_mul`. This is not a
source reproduction of arbitrary non-displayed pivot charts. It proves only
that a matrix with selected pivot entry `1` can be put in the existing
normalised top-left block shape and that the existing `Q/P` identities apply
under explicit quotient witnesses `forall i, b i = q i * b0`, with the
following factor and weights already in pivot-first coordinates.

Third latest A4 update: generic pivot-row quotient witnesses have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`exists_right_quotients_of_forall_dvd`,
`exists_right_quotients_of_forall_eq`,
`exists_right_quotients_of_forall_eq_or_dvd`,
`monomialRec_tail_eq_right_mul`,
`exists_right_quotients_monomialRec_of_le`,
`exists_right_quotients_monomialRec_of_eq_or_le`,
`exists_right_quotients_pivotMul_monomialRec_of_le`,
`exists_right_quotients_pivotMul_monomialRec_of_eq_or_le`,
`exists_right_quotients_const`, and
`exists_weightedPivotBlockRowOp_mul_diagonal_mul_of_forall_dvd`. These are
generic algebraic witnesses for the `P` matrix quotient hypothesis, not
Aoyagi-specific chart construction or transition data.

Fourth latest A4 update: pivot-first existential `Q/P` wrappers have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`exists_pivotFirstQP_mul_pivotQ_of_forall_dvd`,
`exists_pivotFirstQP_mul_pivotQ_of_monomialRec_eq_or_le`,
`exists_pivotFirstQP_mul_pivotQ_of_pivotMul_monomialRec_eq_or_le`,
`exists_pivotFirstQP_mul_of_forall_dvd`,
`exists_pivotFirstQP_mul_of_monomialRec_eq_or_le`,
`exists_pivotFirstQP_mul_of_pivotMul_monomialRec_eq_or_le`,
`Case1FirstJumpHypotheses.displayedPivot_mem_center_of_colBound`,
`Case1FirstJumpHypotheses.displayedPivot_mem_residualBlockPivotEntries_of_colBound`,
and `Case1FirstJumpHypotheses.stripEntry_mem_residualBlockPivotEntries`.
These theorems choose the `q` witnesses needed by the pivot-first `Q/P`
identities from divisibility or recurrence hypotheses. They still assume
normalised pivot-first coordinates and do not prove Aoyagi selected-entry chart
construction, coordinate/weight transport, arbitrary row hypotheses, chart
coverage, exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-pivot-first-existential-q-p.md`.

Fifth latest A4 update: the source-displayed Case 2 top-left pivot `Q/P`
instantiation has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
Proved Lean names include `Case2ResidualRowIndex`,
`Case2ResidualColIndex`, `case2DisplayedPivotRow`,
`case2DisplayedPivotCol`, `selectedEntryNormalizedMap`,
`selectedEntrySubstitutionMatrix`, `selectedEntryNormalizedMatrix`, and
`exists_case2DisplayedQP_mul_of_flat_weights`. This checkpoint packages the
displayed pivot row/column under the continuation bound, splits the
selected-entry substitution as `u` times a normalised matrix with pivot entry
`1`, and applies the pivot-first product `Q/P` identity under flat displayed
row weights. It does not prove arbitrary selected-entry charts, atlas
coverage, full coordinate/weight transport, exponent updates, or transition
invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-pivot-q-p.md`.

Sixth latest A4 update: pivot-first following-factor transport has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names are
`pivotFirstFollowingFactor` and
`pivotFirstMatrix_mul_pivotFirstFollowingFactor`. These prove that the
following factor reindexed by `pivotFirstIndexEquiv colPivot` multiplies with
the pivot-first residual block to give the pre-reindexed product reindexed by
`pivotFirstIndexEquiv rowPivot`. This is finite matrix reindexing only; it
does not prove source coordinate construction, regularity, chart coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-pivot-first-following-factor.md`.

Seventh latest A4 update: pivot-first diagonal row-weight transport has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean name is
`weightedPivotDiagonal_eq_pivotFirst_diagonal`. It identifies the split
diagonal matrix used by the pivot-first `P` operation with the original
diagonal row-weight matrix reindexed by `pivotFirstIndexEquiv` on rows and
columns. This is finite matrix reindexing only; it does not prove source
row-weight assignment, recurrence flatness, quotient witnesses, chart coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-pivot-first-diagonal-weights.md`.

Eighth latest A4 update: the displayed Case 2 pivot-first following-factor
package has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
Proved Lean names include `case2DisplayedNormalizedMatrix`,
`case2DisplayedFollowingFactor`,
`case2DisplayedNormalizedMatrix_mul_followingFactor`, and
`exists_case2DisplayedQP_mul_pivotFirstFollowingFactor_of_flat_weights`.
These package the displayed normalised residual block and a residual following
factor supplied before pivot-first reindexing, reindex that factor into
pivot-first column coordinates, and apply the displayed flat-row-weight `Q/P`
theorem. This is local finite algebra only; it does not prove source-coordinate
construction, arbitrary-pivot coverage, regularity, exponent updates, or
transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-pivot-first-following-factor.md`.

Ninth latest A4 update: the displayed Case 2 source-substitution factorisation
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean
names include `diagonal_mul_selectedEntrySubstitutionMatrix`,
`pivotFirst_diagonal_mul_selectedEntrySubstitutionMatrix`,
`case2DisplayedSubstitutionMatrix`,
`case2DisplayedSubstitutionMatrix_eq_mul_normalized`,
`case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst`,
`case2Displayed_diagonal_mul_substitutionMatrix_mul_followingFactor`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_flat_weights`. These prove
that, in the displayed selected-entry chart, `diag(weight)` times the
source-substituted residual block equals the normalised residual block with
row weights updated to `u * weight`, including pivot-first and following-factor
forms. This counts the selected variable once; it does not prove the full
source blockdiag identity, chart regularity/Jacobian, arbitrary-pivot coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-substitution-factor.md`.

Tenth latest A4 update: the displayed Case 2 transported following-factor and
row-index monomial-recurrence wrapper have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`case2ResidualRowLevel`, `case2ResidualRowLevel_ge`,
`case2ResidualRowLevel_displayedPivotRow`,
`case2DisplayedTransportedFollowingFactor`, and
`exists_case2DisplayedQP_mul_transportedFollowingFactor_of_rowIndex_monomialRec`.
These name the displayed `Q^{-1}C` following-factor update and instantiate the
pivot-first `Q/P` identity when updated row weights are
`u * monomialRec step rowLevel`; quotient witnesses come from the residual-row
bound `J+1 <= rowLevel`. This does not prove that Aoyagi's recursive state
produces those row weights, nor chart regularity, arbitrary-pivot coverage,
exponent updates, or transition invariants. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transported-following-factor-monomial.md`.

Latest A4 update: the displayed Case 2 finite label-product gap bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names
include `levelProductStep`, `levelProductStep_eq_one_of_forall_ne`,
`levelProductStep_eq_one_of_gap`,
`case2ResidualRow_levelProduct_monomialRec_eq_pivot_of_gap`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_labelGap`. These prove that
if the recurrence factor at level `r` is the product over a supplied finite
label set with `level=r`, and no supplied label has level in `J+1..mu_S-1`,
then the recurrence factors in that interval are `1` and the displayed Case 2
source-substitution `Q/P` wrapper applies. This does not prove that the supplied
labels are Aoyagi's actual introduced labels, nor that the recursive invariant
establishes the gap. The residual rows are `J+1..mu_S`, the residual columns are
actual-width `J+1..n_(S+1)`, and the selected variable is counted once in the
updated weights `u*b_i`. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-label-product-gap.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-label-product-gap-a4.md`.

Latest A4 update: the displayed Case 2 introduced-label finite-domain bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names
include `actualWidthLabelFinset`, `mem_actualWidthLabelFinset`,
`introducedLabelFinset`, `mem_introducedLabelFinset`,
`levelProductStep_introducedLabelFinset_eq_one_of_gap`,
`case2ResidualRow_introducedLabel_monomialRec_eq_pivot_of_gap`, and
`exists_case2DisplayedQP_mul_sourceSubstitution_of_introducedLabelGap`. These
instantiate the finite label-product Case 2 row-weight bridge over Lean's
introduced-label predicate. This removes the arbitrary supplied-label domain,
but still assumes the Nat-valued `level` map is Aoyagi's current `tilde_t`, the
variable map is the source recurrence variable assignment, the introduced-label
gap holds, and row weights are generated by this recurrence. It does not prove
the recursive invariant, the source's Case 2 comparability sentence,
arbitrary-pivot chart coverage, chart regularity/Jacobian facts, exponent
updates, transition invariants, termination, normal crossings, RLCT extraction,
or the printed Case 2 vector repair. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-introduced-label-gap.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-introduced-label-gap-a4.md`.

Latest A4 update: the displayed Case 2 recurrence-state interface has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`IntroducedLabelRecurrenceState`, `IntroducedLabelLevelInvariants`,
`case2IntroducedLabelLeastValueGap`,
`IntroducedLabelRecurrenceState.case2Gap`,
`IntroducedLabelRecurrenceState.case2Gap_of_leastValueGap`,
`IntroducedLabelRecurrenceState.step`, `IntroducedLabelRecurrenceState.weight`,
`IntroducedLabelRecurrenceState.case2ResidualRowWeight`,
`IntroducedLabelRecurrenceState.step_eq_one_of_case2Gap`,
`IntroducedLabelRecurrenceState.case2ResidualRow_weight_eq_pivot_of_case2Gap`,
`IntroducedLabelRecurrenceState.case2ResidualRowWeight_eq_pivot_of_case2Gap`,
`IntroducedLabelRecurrenceState.case2ResidualRowWeight_eq_displayedPivot_of_case2Gap`,
and `exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap`.
This packages the introduced-label recurrence data while keeping `step` and
row weights derived from `level`, `var`, and `introducedLabelFinset`. It bridges
integer least-value gaps to Nat-level recurrence gaps through the equality-only
`IntroducedLabelLevelInvariants`. This is not a transition invariant and
does not prove the Case 2 gap, source comparability, arbitrary-pivot chart
coverage, chart regularity/Jacobian facts, exponent updates, termination,
normal crossings, RLCT extraction, or the printed Case 2 vector repair.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-recurrence-state-interface.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-recurrence-state-interface-a4.md`.

Latest A4 update: the conditional Case 2 recurrence-weight update has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`introducedLabelFinset_succ_eq_insert`,
`not_mem_introducedLabelFinset_case2_new_before`,
`IntroducedLabelRecurrenceState.case2Succ`,
`IntroducedLabelRecurrenceState.case2Succ_case2Gap`,
`IntroducedLabelRecurrenceState.case2IntroducedLabelLeastValueGap_succ`,
`IntroducedLabelRecurrenceState.case2Succ_levelInvariants`,
`IntroducedLabelRecurrenceState.case2Succ_case2Gap_of_leastValueGap`,
`monomialRec_eq_of_step_eq_on_lt`,
`monomialRec_eq_mul_of_step_eq_mul_at`,
`levelProductStep_insert_eq_mul_of_new`,
`levelProductStep_insert_eq_of_ne`,
`IntroducedLabelRecurrenceState.step_succ_current_eq_new_mul`,
`IntroducedLabelRecurrenceState.step_succ_current_eq_of_ne`,
`IntroducedLabelRecurrenceState.weight_succ_current_eq_of_le`,
`IntroducedLabelRecurrenceState.weight_succ_current_eq_new_mul_of_ge`,
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul`,
and
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap`.
This proves that if a supplied successor recurrence state keeps old
introduced-label levels and variables and assigns the new label `(S,J+1)` level
`J` and variable `u`, then every post weight from `J+1` onward is `u` times the
old weight. Under the old Case 2 gap, the displayed residual-row weights remain
flat after this common multiplication. This is not a chart-production theorem,
does not repair the printed Case 2 vector mismatch, and does not prove source
comparability, exponent updates, transition invariants, normal crossings, or
RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-recurrence-weight-update.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-recurrence-weight-update-a4.md`.

Latest A4 update: the displayed Case 2 successor source-substitution handoff
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean
names are
`CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`
and
`CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`.
These theorems combine the previous displayed selected-entry substitution
factorisation with the conditional recurrence-weight update, rewriting the
right-side diagonal in the displayed pivot-first and `Q/P` identities with a
supplied successor state's weights. The left side remains the old-weighted
source substitution. This is still conditional post-state bookkeeping, not a
proof of chart production, arbitrary-pivot chart coverage, coordinate
regularity/Jacobian, exponent updates, transition invariants, normal crossings,
RLCT extraction, source comparability, or the printed Case 2 vector repair.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-successor-source-substitution.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-successor-source-substitution-a4.md`.

Latest A4 update: the Case 2 supplied recurrence post-data package has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. Proved Lean names include
`IntroducedLabelRecurrenceState.Case2SuppliedPostData`,
`IntroducedLabelRecurrenceState.case2Succ_case2SuppliedPostData`,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge`,
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_eq_newVar_mul_of_postData`,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_residual_flat_of_preGap`,
`CorrectedCase2NewLabelCertificate.case2_weight_succ_current_residual_flat_of_preGap_of_postData`,
`CorrectedCase2NewLabelCertificate.case2Displayed_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
and
`CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`.
The package is recurrence-local: it records old-label agreement and the new
label's level/variable assignment, while keeping source validity, the old gap,
and displayed pivot bounds separate. It is not chart production, chart
coverage, coordinate regularity/Jacobian, exponent update, transition
invariant, normal crossing, RLCT extraction, source comparability, or the
printed Case 2 vector repair. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-supplied-post-data.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-supplied-post-data-a4.md`.

Latest A4 update: the corrected Case 2 exponent update-data wrapper has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean name is
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_updateData_of_prefixBound`.
It applies the existing corrected Case 2 new-label domain-extension theorem to
concrete selected-label update functions for `t`, `numerator`, and
`leastValue`, changing only `(S,J+1)`. This is exponent-domain bookkeeping
only: recurrence post-data does not imply these exponent assignments, and the
theorem does not prove chart production, exponent transition invariance,
source comparability, arbitrary-pivot transport, normal crossings, RLCT
extraction, or that the corrected vector is the PDF's printed vector.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-exponent-update-data.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-exponent-update-data-a4.md`.

Latest A4 update: the corrected Case 2 exponent post-data package has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case2CorrectedExponentPostData`,
`IntroducedLabelExponentCertificates.extendDomain_correctedCase2NewLabel_of_postData`,
`Case2CorrectedExponentPostData.updateSelected`,
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.levelInvariants_of_correctedExponentPostData`,
and
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.case2Gap_of_leastValueGap_of_correctedExponentPostData`.
The package records explicit old/new corrected exponent-map fields, the
concrete selected-label update wrapper factors through it, and supplied
recurrence post-data can now use supplied corrected exponent least-value data
to advance the recurrence-level Case 2 gap. This is corrected invariant
bookkeeping only: it does not prove chart production, an exponent transition
invariant, arbitrary-pivot transport, source comparability, normal crossings,
RLCT extraction, or that the corrected vector is the PDF's printed Case 2
vector. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-corrected-exponent-post-data.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-corrected-exponent-post-data-a4.md`.

Latest A4 update: arbitrary selected-entry Case 2 source-substitution transport
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names include `case2ResidualBlockPivotRowOfMem`,
`case2ResidualBlockPivotColOfMem`, `case2ResidualBlockPivotOfMem_pair`,
`case2SelectedNormalizedMatrix`,
`case2SelectedSubstitutionMatrix`,
`case2Selected_diagonal_mul_substitutionMatrix_pivotFirst`,
`case2SelectedFollowingFactor`, `case2SelectedTransportedFollowingFactor`,
`case2Selected_diagonal_mul_substitutionMatrix_mul_followingFactor`,
`exists_case2SelectedQP_mul_sourceSubstitution_of_forall_dvd`, and
`exists_case2SelectedQP_mul_sourceSubstitution_of_flat_weights`. The theorem
family is finite algebra for a supplied residual-block pivot: it reindexes the
selected substitution and following factor into pivot-first coordinates and
applies `Q/P` only under explicit row-weight divisibility or flatness. It does
not prove arbitrary-pivot chart coverage, chart regularity/Jacobian facts,
recurrence post-state production, exponent updates, source comparability,
normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-selected-source-substitution.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-arbitrary-selected-source-substitution-a4.md`.

Latest A4 update: arbitrary selected-entry Case 2 recurrence handoff has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
`CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights`,
`CorrectedCase2NewLabelCertificate.case2Selected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
`CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights`,
and
`CorrectedCase2NewLabelCertificate.exists_case2SelectedQP_mul_sourceSubstitution_of_recurrenceStateGap_succWeights_of_postData`.
The theorem family lifts the arbitrary selected finite-algebra wrapper to
packaged old recurrence states and supplied successor post-data, while keeping
the selected pivot and post-state supplied. It does not prove chart production,
arbitrary-pivot chart coverage, regularity/Jacobian, exponent updates, source
comparability, normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-selected-recurrence-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-arbitrary-selected-recurrence-handoff-a4.md`.

Latest A4 update: the Case 2 source-selected pair wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2SourceResidualBlock`, `case2SourceFollowingFactor`,
`case2SourceSelectedNormalizedMatrixOfMem`,
`case2SourceSelectedSubstitutionMatrixOfMem`,
`case2SourceSelectedFollowingFactorOfMem`,
`case2SourceSelectedTransportedFollowingFactorOfMem`,
`case2SourceSelectedNormalizedMatrixOfMem_pivot`,
`case2SourceSelectedSubstitutionMatrixOfMem_pivot`,
`exists_case2SourceSelectedQP_mul_sourceSubstitution_of_recurrenceStateGap`,
`CorrectedCase2NewLabelCertificate.case2SourceSelected_diagonal_mul_substitutionMatrix_pivotFirst_succWeights_of_postData`,
and
`CorrectedCase2NewLabelCertificate.exists_case2SourceSelectedQP_of_recurrenceStateGap_succWeights_of_postData`.
The theorem family restricts source-coordinate residual/following data to the
residual row/column subtypes and instantiates arbitrary selected-pivot
recurrence/post-data wrappers from a supplied source pivot pair in
`case2ResidualBlockPivotEntries`. It does not prove chart coverage,
source-order transition formulas for non-displayed pivots, chart-produced
post-data, regularity/Jacobian, exponent updates, normal crossings, or RLCT
extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-pair-wrapper.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-selected-pair-wrapper-a4.md`.

Latest A4 update: selected-entry principalization and finite operation unit
facts have landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The
proved Lean names are `weightedPivotBlockRowOp_isUnit`,
`weightedPivotBlockRowOp_det_isUnit`, `pivotQ_isUnit`, `pivotQ_det_isUnit`,
`pivotQinv_isUnit`, `pivotQinv_det_isUnit`,
`selectedEntryChartMap_centerIdeal_eq_span_singleton`,
`case2_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`, and
`case1_selectedEntryChartMap_centerIdeal_eq_span_singleton_of_mem`. The theorem
family proves that the finite `P/Q` operation matrices are units and that a
supplied selected-entry chart pulls the finite center ideal back to the
principal ideal `(u)`. It does not prove affine blow-up atlas coverage,
polynomial-coordinate Jacobian formulas, source-order transition formulas,
chart-produced recurrence/exponent post-data, normal crossings, or RLCT
extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-principalization-unit-facts.md`.
Review artifact:
`threads/04-blow-up-certificate/review-selected-entry-principalization-unit-facts-a4.md`.

Latest A4 update: the Case 2 chart-family boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`SelectedEntryChartFamilyBoundary`, `Case2ResidualBlockChartFamilyBoundary`,
`case2ResidualBlockPivotEntries_nonempty_of_cont`,
`Case2ResidualBlockChartFamilyBoundary.chart_regular_of_mem`,
`Case2ResidualBlockChartFamilyBoundary.transition_regular_of_mem`, and
`Case2ResidualBlockChartFamilyBoundary.chart_regular_displayedPivot_of_cont`.
This checkpoint names chart regularity and transition regularity as supplied
predicates over the finite Case 2 residual-block center, while proving only
that the displayed pivot makes that finite center nonempty under continuation.
It does not prove chart regularity, transition regularity, affine blow-up atlas
coverage, source-order transition formulas, chart-produced post-data,
Jacobians, normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-chart-family-boundary-a4.md`.

Latest A4 update: the Case 1 chart-family boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case1CenterGenerators_nonempty`, `case1StripEntries_nonempty_of_bounds`,
`mem_case1CenterGenerators_inr_iff`, `Case1CenterChartFamilyBoundary`,
`Case1CenterChartFamilyBoundary.chart_regular_of_mem`,
`Case1CenterChartFamilyBoundary.transition_regular_of_mem`,
`Case1CenterChartFamilyBoundary.chart_regular_selectedOld`,
`Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_bounds`, and
`Case1CenterChartFamilyBoundary.chart_regular_displayedPivot_of_firstJump_colBound`.
This checkpoint specializes the generic selected-entry chart-family boundary
to the Case 1 finite center: one `Unit` old-exceptional generator plus the
actual-width row strip. It proves only finite center nonemptiness, row-strip
nonemptiness under displayed bounds, right-branch membership, and supplied
regularity projections. It does not prove chart coverage, chart regularity,
transition regularity, the source validity of the hidden old label, arbitrary
row-strip pivot source-order transitions, chart-produced post-data, Jacobians,
normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-chart-family-boundary-a4.md`.

Latest A4 update: the displayed top-left source-order adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1FirstJumpHypotheses.continuationBound_of_colBound`,
`WeightedPivotFirstSubstitutionData`,
`WeightedPivotFirstSubstitutionData.sourceOrder_identity`, and
`exists_weightedPivotFirstSubstitution_sourceOrder_identity_of_forall_dvd`.
This checkpoint packages the common finite `Q/P` handoff after a selected
chart has already produced a weighted, pivot-first source block. It proves
only finite width bookkeeping and the supplied source-order product identity;
it does not construct the selected chart, prove Case 1 full residual-block
substitution, produce recurrence/exponent post-data, decide continuation vs
advance, or prove chart coverage/regularity/Jacobians. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-displayed-top-left-source-order-adapter.md`.
Review artifact:
`threads/04-blow-up-certificate/review-displayed-top-left-source-order-adapter-a4.md`.

Latest A4 update: the displayed Case 1(2) local handoff has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`IntroducedLabelRecurrenceState.Case2SuppliedPostData.exists_case1DisplayedRowStrip_sourceOrder_identity_sourceWeights_succWeights_of_postData`,
`Case1DisplayedRowStripSuppliedTransitionBoundary`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.stage_pos`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.continuationBound`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.newLabelActualWidth`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_sourceWeights`,
and `Case1DisplayedRowStripSuppliedTransitionBoundary.extendExponentDomain`.
This checkpoint packages first-jump data, actual source bounds, a supplied
factored-base recurrence post-state, supplied pre-state exponent certificates,
level-tail invariants, and supplied Case 1 exponent post-data. It proves the
displayed top-left source-order identity with original source recurrence
weights on the left and supplied post-state weights on the right, and extends
the exponent certificate domain to `(S,J+1)`. It does not construct the
factored-base recurrence from the original pre-state, prove hidden old-label
source validity, prove chart-produced post-data, chart coverage, regularity,
Jacobians, normal crossings, or RLCT extraction. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-displayed-row-strip-local-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-displayed-row-strip-local-handoff-a4.md`.

Latest A4 update: the selected-old source substitution boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`levelProductStep_updateVar_eq_mul_of_mem`,
`levelProductStep_updateVar_eq_of_ne`,
`levelProductStep_eq_mulStepAt_of_updateSelected`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_selectedLevel_eq_mul`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_of_ne_selectedLevel`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_selectedLevel`,
`IntroducedLabelRecurrenceState.Case1SelectedOldFactoredBaseData.step_eq_mulStepAt_of_firstJump`,
and
`case1ResidualRowStripOldWeight_eq_sourceWeight_of_selectedOldFactoredBase`.
This checkpoint proves the finite-product recurrence effect of replacing the
selected old variable by `u*old'` in the pulled-back source recurrence:
`source.step = mulStepAt factoredBase.step u (J+J1)`, under supplied
same-domain factorisation data. It does not construct the selected-old chart,
identify the hidden old label behind the `Unit` center generator, construct the
factored-base state, produce post-data, prove coverage/regularity/Jacobians,
or prove normal crossings/RLCT. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-source-substitution.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-source-substitution-a4.md`.

Latest A4 update: the Case 1 source-substituted local handoff has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean name is
`Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights`.
It combines the supplied displayed row-strip local handoff with the supplied
selected-old source substitution boundary, rewriting the left diagonal from
`monomialRec (mulStepAt factoredBase.step u (J+J1))` to
`source.weight (case2ResidualRowLevel n S J i)`. The theorem requires the
explicit level identification `level = factoredBase.level`; this is the bridge
needed to use the first-jump selected level with the recurrence-state data. It
does not construct the source pullback, selected-old chart, hidden old-label
source validity, factored-base or post states, chart-produced post-data,
coverage/regularity/Jacobians, normal crossings, or RLCT extraction. Statement
card:
`threads/04-blow-up-certificate/statement-card-a4-case1-source-substituted-local-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-source-substituted-local-handoff-a4.md`.

Latest A4 update: the Case 1 selected-old pullback boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1DisplayedRowStripSelectedOldPullbackBoundary`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.factoredBaseFirstJump`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.selectedOld_mem_center`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.sourcePullback_selectedIntroduced`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.selectedLevel`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.source_step_eq_mulStepAt`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.residualRowStripOldWeight_eq_sourceWeight`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.sourceOrder_identity`, and
`Case1DisplayedRowStripSelectedOldPullbackBoundary.extendExponentDomain`. This
checkpoint bundles the supplied selected-old source pullback with the supplied
displayed row-strip local handoff specialized to `factoredBase.level`, so the
source-facing handoff no longer needs a separate
`level = factoredBase.level` argument. It does not construct the selected-old
chart, prove that the `Unit` center token determines `(s0,k0)`, construct the
raw-coordinate source pullback, prove chart-produced post-data,
coverage/regularity/Jacobians, normal crossings, or RLCT extraction. Statement
card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-pullback-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-pullback-boundary-a4.md`.

Latest A4 update: the Case 1 selected-old supplied chart-family boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourcePullback_selectedIntroduced`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.selectedLevel`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.selectedOld_mem_center`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_mem_center`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.chart_regular_selectedOld`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.chart_regular_displayedPivot`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.transition_regular_selectedOld_displayedPivot`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.transition_regular_displayedPivot_selectedOld`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.source_step_eq_mulStepAt`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity`,
and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.extendExponentDomain`.
This checkpoint combines the selected-old pullback/local handoff boundary with
a supplied `Case1CenterChartFamilyBoundary`, exposing regularity and
transition-regularity projections for the selected old token and displayed
top-left row-strip pivot. It does not construct charts, prove coverage, derive
the old source label from `Unit`, construct the raw source pullback, compute
Jacobians, prove normal crossings, or extract RLCT. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-supplied-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-supplied-chart-family-boundary-a4.md`.

Latest A4 update: the Case 1 selected-old source-coordinate wrapper has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_selectedEntryChartMap_value_mem`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_center_dvd`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.displayedPivot_centerIdeal_eq_span_singleton`,
`case2DisplayedSourceFollowingFactor`, and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates`.
This checkpoint adapts the existing displayed Case 1(2) source-order
identity from source-coordinate residual/following-factor functions under
`residual (J+1,J+1)=1`, and projects finite selected-entry principalization
facts for the displayed top-left chart token. It does not
construct the selected-old chart, prove atlas coverage, derive `(s0,k0)` from
`Unit`, project selected-old `Unit` principalization with the displayed pivot
variable, construct the source pullback, produce chart post-data, compute
Jacobians, prove normal crossings, extract RLCT, or prove a transition
invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-source-coordinate-wrapper.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-source-coordinate-wrapper-a4.md`.

Latest A4 update: the Case 1(1) selected-old chart source-coordinate identity
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `case1SelectedOldPostWeight`,
`case1SelectedOld_diagonal_mul_sourceMatrix`, and
`case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates`. This checkpoint
proves the row-wise identity for the selected-old chart denominator:
`diag(baseWeight) * sourceRowStripMatrix = diag(postWeight) * dividedMatrix`,
where the post weight absorbs the selected old factor exactly on the Case 1
row strip. It is independent of the displayed Case 1(2) pivot
`u_(S,J+1)`, introduces no `(S,J+1)` label, and asserts no `Q/P` transition,
chart construction, coverage/regularity/Jacobians, normal crossings, RLCT, or
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-chart-source-coordinates.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-chart-source-coordinates-a4.md`.

Latest A4 update: the Case 1(1) selected-old same-domain boundary has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case1SelectedOldLowerTailExponentPostData`,
`IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_postData`,
`IntroducedLabelExponentCertificates.case1_selectedLowerTail_of_levelTailInvariants_postData`,
`Case1SelectedOldSuppliedSameDomainBoundary`,
`Case1SelectedOldSuppliedSameDomainBoundary.selectedIntroduced`,
`Case1SelectedOldSuppliedSameDomainBoundary.selectedLevel`,
`Case1SelectedOldSuppliedSameDomainBoundary.sourceMatrix_identity`,
`Case1SelectedOldSuppliedSameDomainBoundary.sourceCoordinates_identity`, and
`Case1SelectedOldSuppliedSameDomainBoundary.updateExponentCertificates`.
This checkpoint packages supplied Case 1(1) exponent post-data with the
already proved row-strip identity and lower-tail update. It stays at `(S,J)`,
uses the actual-width numerator increment, and does not introduce `(S,J+1)`,
use the displayed Case 1(2) pivot, assert `Q/P`, construct charts, prove
coverage/regularity/Jacobians, prove normal crossings/RLCT, or prove a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-same-domain-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-same-domain-boundary-a4.md`.

Latest A4 update: the Case 1(1) selected-old recurrence post-weight
calculation has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean names are
`monomialRec_mulStepAt_case1_selectedOld_postWeight`,
`case1SelectedOldPostWeight_eq_monomialRec_loweredLevel`,
`case1SelectedOld_diagonal_mul_sourceMatrix_loweredLevel`, and
`case1SelectedOld_diagonal_mul_sourceMatrix_sourceCoordinates_loweredLevel`.
This checkpoint proves, from a supplied base recurrence, that moving the
selected old factor from level `J+J1` down to level `J` gives exactly the
Case 1(1) piecewise strip post weights on active residual rows. It does not
construct the selected-old chart, derive the base recurrence from source data,
prove recurrence-state post-data, introduce `(S,J+1)`, use the displayed
Case 1(2) pivot, assert `Q/P`, construct charts, prove
coverage/regularity/Jacobians, prove normal crossings/RLCT, or prove a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-recurrence-postweight.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-recurrence-postweight-a4.md`.

Latest A4 update: the Case 1(1) selected-old lowered-recurrence boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `Case1SelectedOldLoweredRecurrenceBoundary`,
`Case1SelectedOldLoweredRecurrenceBoundary.selectedIntroduced`,
`Case1SelectedOldLoweredRecurrenceBoundary.selectedLevel`,
`Case1SelectedOldLoweredRecurrenceBoundary.selectedOldPostWeight_eq_postWeight`,
`Case1SelectedOldLoweredRecurrenceBoundary.sourceMatrix_identity_postWeights`,
`Case1SelectedOldLoweredRecurrenceBoundary.sourceCoordinates_identity_postWeights`,
and `Case1SelectedOldLoweredRecurrenceBoundary.updateExponentCertificates`.
This checkpoint packages the pure recurrence post-weight calculation with
supplied pre/post recurrence states and same-domain exponent data. It assumes
the base-step equalities and does not derive them from a chart or source
coordinates. It stays at `(S,J)`, does not introduce `(S,J+1)`, does not use
the displayed Case 1(2) pivot, and does not assert `Q/P`, chart construction,
coverage/regularity/Jacobians, normal crossings/RLCT, or a transition
invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-lowered-recurrence-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-lowered-recurrence-boundary-a4.md`.

Latest A4 update: the Case 1(1) selected-old `Unit` chart-family boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `Case1SelectedOldUnitSuppliedChartFamilyBoundary`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedIntroduced`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedLevel`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_mem_center`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.chart_regular_selectedOld`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.transition_regular_selectedOld_of_mem`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.transition_regular_of_mem_selectedOld`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_selectedEntryChartMap_value_mem`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_center_dvd`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.selectedOld_centerIdeal_eq_span_singleton`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.sourceMatrix_identity_postWeights`,
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.sourceCoordinates_identity_postWeights`,
and `Case1SelectedOldUnitSuppliedChartFamilyBoundary.updateExponentCertificates`.
This checkpoint combines the supplied lowered recurrence boundary with the
supplied finite Case 1 chart-family boundary. It projects finite
selected-entry principalization for the selected-old `Sum.inl ()` token and
keeps the recurrence and exponent projections over `(S,J)`. It does not
identify the hidden old source label from the `Unit` token, construct the
selected-old chart, derive source recurrence states, introduce `(S,J+1)`, use
the displayed Case 1(2) pivot, assert `Q/P`, prove
coverage/regularity/Jacobians, prove normal crossings/RLCT, or prove a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-unit-chart-family-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-unit-chart-family-boundary-a4.md`.

Latest A4 update: the Case 1(1) selected-old erased-base source model has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `levelProductStep_eq_mulStepAt_erase`,
`levelProductStep_erase_eq_of_eq_on_erase`,
`IntroducedLabelRecurrenceState.erasedStep`,
`IntroducedLabelRecurrenceState.step_eq_mulStepAt_erasedStep`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.post_erasedStep_eq_pre_erasedStep`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.pre_step_eq_mulStepAt`,
`IntroducedLabelRecurrenceState.Case1SelectedOldLevelMoveData.post_step_eq_mulStepAt`,
and `Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData`. This
checkpoint defines the base recurrence as the introduced-label product with
the selected old label erased, proves pre/post `mulStepAt` equalities from a
supplied same-domain level move, and instantiates the existing lowered
boundary with that erased base. It does not construct the selected-old chart,
infer `(s0,k0)` from the `Unit` token, produce chart data, introduce
`(S,J+1)`, use Case 1(2), assert `Q/P`, prove coverage/regularity/Jacobians,
prove normal crossings/RLCT, or prove a transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-erased-base-source-model.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-erased-base-source-model-a4.md`.

Latest A4 update: the Case 1(1) selected-old concrete level move has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_level_selected`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_level_of_ne`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_var`,
`IntroducedLabelRecurrenceState.case1SelectedOldLevelMove_levelMoveData`, and
`Case1SelectedOldLoweredRecurrenceBoundary.of_sameDomain_case1SelectedOldLevelMove`.
This checkpoint gives a canonical same-domain post-state for Case 1(1): only
the selected old label's recurrence level is lowered to `J`; recurrence-label
variables and non-selected levels are unchanged. It instantiates the
erased-base lowered boundary from a same-domain package over `pre.level`.
This does not construct the selected-old chart, prove raw source-coordinate
post-state production, infer `(s0,k0)` from `Unit`, introduce `(S,J+1)`, use
Case 1(2), assert `Q/P`, prove coverage/regularity/Jacobians, prove normal
crossings/RLCT, or prove a transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-concrete-level-move.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-concrete-level-move-a4.md`.

Latest A4 update: the Case 1(1) selected-old Unit boundary from the concrete
level move has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean name is
`Case1SelectedOldUnitSuppliedChartFamilyBoundary.of_sameDomain_case1SelectedOldLevelMove`.
This checkpoint packages the concrete lowered recurrence boundary with a
supplied finite Case 1 chart-family boundary, yielding a Unit chart-family
boundary with `post = pre.case1SelectedOldLevelMove s0 k0`,
`u = pre.var s0 k0`, and `baseStep = pre.erasedStep s0 k0`. It does not
construct chart regularity, transitions, coverage, Jacobians, normal
crossings/RLCT, Case 1(2), `Q/P`, or a transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-selected-old-unit-concrete-level-move.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-selected-old-unit-concrete-level-move-a4.md`.

Latest A4 update: the Case 2 printed mismatch boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`terminalExponent_printedCase2Vector_sub_prefixFormula`,
`terminalExponent_printedCase2Vector_eq_prefixFormula_iff`, and
`terminalExponent_case2Printed_ne_corrected_of_prefixDrop_of_cont`.
This checkpoint isolates the exact arithmetic boundary between the PDF's
printed actual-width Case 2 vector and the prefix-minimum numerator increment:
the difference is `(M^(S)-M(S))*(M^(S+1)-J)`, equality occurs only in the
equal-row-width or zero-column-factor cases, and under the continuation bound
`J+1<=M(S+1)` a genuine prefix-width drop `M(S)<M^(S)` gives unequal printed
and corrected terminal exponents. It does not prove a Case 2 transition
theorem, erratum, reachable-state
equal-width invariant, chart coverage, Jacobians, normal crossings/RLCT, or
termination. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-printed-mismatch-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-printed-mismatch-boundary-a4.md`.

Latest A4 update: the displayed Case 1(2) paper `Q/P` adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case1DisplayedPaperDchart`, `case1DisplayedPaperDchart_pivot`,
`case1DisplayedPaperSourceBlock`, `case1DisplayedPaperQ`,
`case1DisplayedPaperQinv`, `case1DisplayedPaperDpp`,
`case1DisplayedPaperCprime`, `case1DisplayedPaperDppp`,
`case1DisplayedPaperDpp_eq_pivotPostQBlock`,
`case1DisplayedPaperDpp_mul_Cprime`, and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.sourceOrder_identity_sourceCoordinates_paperQP`.
This checkpoint exposes Aoyagi's printed `Q`, `Q^-1`, `D''`, `C'`, and `D'''`
notation over the already supplied displayed source-order identity. It proves
the `D''` post-`Q` block identification and the orientation
`D'' * C' = D_chart^pivot * C`, but remains a local adapter: normalized chart
data, recurrence/exponent post-data, quotient witnesses, regularity, and
transition data are still supplied. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-displayed-paper-qp-adapter.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case1-displayed-paper-qp-adapter-a4.md`.

Latest A4 update: the Case 2 supplied source-selected pivot boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `Case2SourceSelectedSuppliedChartFamilyBoundary`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.correctedNewLabel`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.preCase2Gap`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.extendExponentDomain`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.postLevelInvariants`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.successorLeastValueGap`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.postCase2Gap`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_selectedPivot`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_of_mem`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.transition_regular_selectedPivot_of_mem`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.selectedPivot_centerIdeal_eq_span_singleton`,
and `Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP`. This
checkpoint packages a supplied residual-block pivot with corrected exponent
post-data, recurrence post-data, supplied chart-family predicates, finite
principalization, and source-selected arbitrary-pivot `Q/P` transport; it does
not prove atlas coverage, source-displayed non-top-left charts, chart-produced
post-data, Jacobians, normal crossings/RLCT, termination, or a transition
invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-supplied-source-selected-pivot-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-supplied-source-selected-pivot-boundary-a4.md`.

Latest A4 update: the Case 2 displayed concrete-update boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case2SourceSelectedSuppliedChartFamilyBoundary.displayedPivot_mem`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.chart_regular_displayedPivot`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.transition_regular_selectedPivot_displayedPivot`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`,
`Case2DisplayedSuppliedChartFamilyBoundary`,
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_mem`,
`Case2DisplayedSuppliedChartFamilyBoundary.sourceSelectedBoundary`,
`Case2DisplayedSuppliedChartFamilyBoundary.correctedNewLabel`,
`Case2DisplayedSuppliedChartFamilyBoundary.preCase2Gap`,
`Case2DisplayedSuppliedChartFamilyBoundary.extendExponentDomain`,
`Case2DisplayedSuppliedChartFamilyBoundary.chart_regular_displayedPivot`,
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_centerIdeal_eq_span_singleton`,
`Case2DisplayedSuppliedChartFamilyBoundary.of_case2Succ_updateSelected`, and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceCoordinates`.
This checkpoint specializes the supplied source-selected boundary to Aoyagi's
displayed top-left pivot and chooses concrete recurrence/exponent assignment
functions `pre.case2Succ u` and `Case2CorrectedExponentPostData.updateSelected`;
it does not prove those assignments are chart-produced, nor coverage,
coordinate regularity, Jacobians, normal crossings/RLCT, termination, or a
transition invariant. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-concrete-update-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-concrete-update-boundary-a4.md`.

Latest A4 update: the Case 2 displayed source-chart map has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2DisplayedSourceChartMap`, `case2DisplayedSourceNormalizedMap`,
`case2DisplayedSourceChartMap_pivot`,
`case2DisplayedSourceNormalizedMap_pivot`,
`case2DisplayedSourceChartMap_of_ne`,
`case2DisplayedSourceChartMap_eq_mul_normalized`,
`case2Displayed_source_pair_eq_pivot_iff`,
`case2DisplayedSourceSubstitutionBlock`,
`case2DisplayedSourceNormalizedBlock`,
`case2DisplayedSourceNormalizedBlock_eq_displayedNormalizedMatrix`,
`case2DisplayedSourceSubstitutionBlock_eq_displayedSubstitutionMatrix`,
`case2DisplayedSourceSubstitutionBlock_eq_mul_normalized`,
`case2DisplayedSource_diagonal_mul_substitutionBlock_pivotFirst`,
`case2DisplayedSourceNormalizedBlock_mul_sourceFollowingFactor`,
`case2DisplayedSourceTransportedFollowingFactor`,
`case2DisplayedSourceTransportedFollowingFactor_eq_displayedTransportedFollowingFactor`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap`.
This checkpoint names Aoyagi's displayed top-left source substitution and
proves that its residual-block restriction is the already-proved displayed
selected-entry block API. It also rewrites the supplied displayed `Q/P`
identity in source-chart block names. It does not prove chart coverage,
non-top-left source-displayed formulas, chart-produced recurrence/exponent
post-data, coordinate regularity, Jacobians, normal crossings/RLCT,
termination, a transition invariant, or repair of the printed vector mismatch.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-source-chart-map.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-source-chart-map-a4.md`.

Latest A4 update: the Case 2 displayed center count has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2_continuation_le_prefixMinNat_current`,
`case2_continuation_le_width_next`, `case2ResidualBlockRows_card`,
`case2ResidualBlockCols_card`, `case2ResidualBlockPivotEntries_card`,
`correctedCase2NewLabelNumerator`,
`correctedCase2NewLabelNumerator_eq_card_of_bounds`, and
`correctedCase2NewLabelNumerator_eq_card_of_cont`. This checkpoint proves that
the displayed Case 2 residual-block coordinate count is
`(M(S)-J)(M^(S+1)-J)`, with prefix-minimum rows and actual-width columns kept
separate. It is not a Jacobian exponent, chart-produced post-data, chart
coverage, normal-crossing/RLCT theorem, termination theorem, transition
invariant, or printed-vector repair. Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-center-count.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-center-count-a4.md`.

Latest A4 update: the Case 2 corrected post-data center-count projection has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are
`Case2CorrectedExponentPostData.numerator_new_eq_correctedNumerator`,
`Case2CorrectedExponentPostData.numerator_new_eq_card_of_cont`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.numerator_new_eq_correctedNumerator`,
`Case2SourceSelectedSuppliedChartFamilyBoundary.numerator_new_eq_card`,
`Case2DisplayedSuppliedChartFamilyBoundary.numerator_new_eq_correctedNumerator`,
and `Case2DisplayedSuppliedChartFamilyBoundary.numerator_new_eq_card`. This
checkpoint reads the supplied corrected Case 2 exponent post-data and projects
the new-label numerator to the already-proved displayed residual-block
coordinate count under continuation. It does not prove chart-produced
post-data, a Jacobian or volume exponent, chart coverage, coordinate
regularity, normal crossings/RLCT, termination, a transition invariant, or
repair of the printed vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-corrected-postdata-center-count-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-corrected-postdata-center-count.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-corrected-postdata-center-count-a4.md`.

Latest A4 update: the Case 2 displayed source-chart principalization has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `case2DisplayedSourceChartMap_value_mem`,
`case2DisplayedSourceChartMap_center_dvd`,
`case2DisplayedSourceChartMap_centerIdeal_eq_span_singleton`,
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_sourceChartMap_value_mem`,
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_sourceChartMap_center_dvd`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.displayedPivot_sourceChartMap_centerIdeal_eq_span_singleton`.
This checkpoint re-expresses the existing selected-entry finite center
principalization in Aoyagi's displayed source-coordinate chart-map names: the
selected variable occurs, every transformed finite center value is divisible by
it, and the transformed finite residual-block center ideal is `Ideal.span {u}`.
It does not prove arbitrary-pivot source chart data, chart production, atlas
coverage, coordinate regularity, Jacobian/volume arithmetic, normal
crossings/RLCT, termination, a transition invariant, or repair of the printed
vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-source-chart-principalization-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-source-chart-principalization.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-source-chart-principalization-a4.md`.

Latest A4 update: the Case 2 displayed successor gap projections have landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`Case2DisplayedSuppliedChartFamilyBoundary.postLevelInvariants`,
`Case2DisplayedSuppliedChartFamilyBoundary.successorLeastValueGap`, and
`Case2DisplayedSuppliedChartFamilyBoundary.postCase2Gap`. This checkpoint
forwards the already proved source-selected supplied-boundary successor facts
through the displayed boundary: the post-state level/least-value bridge, the
successor least-value Case 2 gap, and the successor recurrence Case 2 gap. It
does not prove chart-produced recurrence/exponent post-data, chart coverage,
coordinate regularity, Jacobian/volume arithmetic, normal crossings/RLCT,
termination, a transition invariant, or repair of the printed vector mismatch.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-successor-gap-projections-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-successor-gap-projections.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-successor-gap-projections-a4.md`.

Latest A4 update: the Case 2 source-selected chart-map adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2SourceSelectedChartMapOfMem`,
`case2SourceSelectedNormalizedMapOfMem`,
`case2SourceSelectedChartMapOfMem_pivot`,
`case2SourceSelectedNormalizedMapOfMem_pivot`,
`case2SourceSelectedChartMapOfMem_of_ne`,
`case2SourceSelectedChartMapOfMem_eq_mul_normalized`,
`case2SourceSelected_source_pair_eq_pivot_iff`,
`case2SourceSelectedSubstitutionBlockOfMem`,
`case2SourceSelectedNormalizedBlockOfMem`,
`case2SourceSelectedNormalizedBlockOfMem_eq_selectedNormalizedMatrixOfMem`,
`case2SourceSelectedSubstitutionBlockOfMem_eq_selectedSubstitutionMatrixOfMem`,
and
`Case2SourceSelectedSuppliedChartFamilyBoundary.sourceSelectedQP_sourceChartMap`.
This checkpoint names the selected-entry source chart map for any supplied
Case 2 residual-block pivot and rewrites the already proved source-selected
`Q/P` identity in those source-chart names. It does not prove atlas coverage,
non-top-left displayed source formulas, chart-produced recurrence/exponent
post-data, coordinate regularity, Jacobian/volume arithmetic, normal
crossings/RLCT, termination, a transition invariant, or repair of the printed
vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-chart-map-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-chart-map.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-selected-chart-map-a4.md`.

Latest A4 update: the Case 2 displayed source-chart recurrence boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
names are `case2DisplayedSourceChartMap_case2Succ_postData`,
`case2DisplayedSourceChartMap_case2Succ_weight_update`, and
`case2DisplayedSourceChartMap_case2Succ_residualRowWeight_update`. This
checkpoint ties the concrete recurrence successor `pre.case2Succ u` to the
displayed source chart pivot value and proves the recurrence row-weight update
from `J+1` onward, including the residual-row specialization. It does not
prove affine chart construction, chart-produced exponent post-data,
Jacobian/volume arithmetic, chart coverage, coordinate regularity, normal
crossings/RLCT, termination, a transition invariant, or repair of the printed
vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-source-chart-recurrence-boundary-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-source-chart-recurrence-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-source-chart-recurrence-boundary-a4.md`.

Latest A4 update: the Case 2 displayed source-chart boundary constructor has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.of_sourceChartMap_case2Succ_updateSelected`.
This checkpoint packages the displayed supplied boundary with scalar equal to
the displayed source chart pivot value and with post recurrence state
`pre.case2Succ` of that same pivot value. The corrected exponent post-data and
chart-family predicates are still supplied by the existing corrected
selected-label update and chart-family boundary. It does not prove
chart-produced recurrence/exponent post-data, atlas coverage, coordinate
regularity, Jacobian/volume arithmetic, normal crossings/RLCT, termination, a
transition invariant, or repair of the printed vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-source-chart-boundary-constructor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-source-chart-boundary-constructor.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-source-chart-boundary-constructor-a4.md`.

Latest A4 update: the Case 2 post-pivot exhaustion boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2PostPivotRows`, `case2PostPivotCols`, `case2PostPivotEntries`,
`case2PostPivotRows_card`, `case2PostPivotCols_card`,
`case2PostPivotEntries_card`,
`case2PostPivotEntries_nonempty_iff_next_cont`,
`case2_next_frontier_eq_of_cont_of_not_next`,
`case2PostPivotRows_empty_or_cols_empty_of_not_next_cont`, and
`case2PostPivotEntries_eq_empty_of_not_next_cont`, together with membership
and row/column nonemptiness lemmas. This checkpoint proves that the finite
lower-right domain after the displayed pivot is nonempty exactly under the
next continuation bound `J+2 <= M(S+1)`, and is empty when that bound fails.
It does not construct the `S+1` advance, produce chart recurrence/exponent
post-data, compute Jacobians, prove coverage or coordinate regularity, prove
normal crossings/RLCT, prove termination or transition invariance, or repair
the printed vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-exhaustion-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-exhaustion.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-post-pivot-exhaustion-a4.md`.

Latest A4 update: the Case 2 displayed pivot-complement exhaustion boundary
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved
Lean names include
`case2DisplayedPivotRowComplementEquivPostPivotRows`,
`case2DisplayedPivotColComplementEquivPostPivotCols`,
`case2DisplayedPivotRowComplement_isEmpty_iff_postPivotRows_isEmpty`,
`case2DisplayedPivotColComplement_isEmpty_iff_postPivotCols_isEmpty`,
`case2DisplayedPivotComplement_isEmpty_or_isEmpty_of_not_next_cont`,
`case2DisplayedPivotComplement_matrix_subsingleton_of_not_next_cont`, and
`case2DisplayedPivotComplement_matrix_eq_zero_of_not_next_cont`, together with
raw-value simp lemmas for the two equivalences. This checkpoint identifies the
displayed pivot complements with the old post-pivot domains and packages the
lower-right complement matrix vacuity when the next continuation bound fails.
It does not prove the full terminal `D'''_J = (1,0,...,0)` or transpose
statement, construct `D'''_J`, produce the `S+1` recurrence/exponent state,
prove chart coverage or regularity, compute Jacobians, prove normal
crossings/RLCT, prove termination or transition invariance, or repair the
printed vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-pivot-complement-exhaustion-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-pivot-complement-exhaustion.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-pivot-complement-exhaustion-a4.md`.

Latest A4 update: the Case 2 post-pivot domain handoff has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`case2PostPivotRows_eq_case2ResidualBlockRows_succ`,
`case2PostPivotCols_eq_case2ResidualBlockCols_succ`,
`case2PostPivotEntries_eq_case2ResidualBlockPivotEntries_succ`,
`case2ResidualBlockPivotEntries_succ_nonempty_iff_next_cont`,
`case2DisplayedPivotRowComplementEquivResidualRowSucc`, and
`case2DisplayedPivotColComplementEquivResidualColSucc`. This checkpoint proves
that deleting the displayed pivot row/column leaves exactly the next
same-stage residual row/column/entry domains for `(S,J+1)`, with nonemptiness
equivalent to `J+2 <= prefixMinNat n (S+1)`. It does not produce the next
residual matrix or following product, prove chart coverage or coordinate
regularity, compute Jacobians, prove normal crossings/RLCT, prove termination
or transition invariance, or handle the terminal `(S+1,0)` relabel branch.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-domain-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-domain-handoff.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-post-pivot-domain-handoff-a4.md`.

Latest A4 update: the Case 2 post-pivot next-block adapter has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`weightedPivotClearedBlock_mul_verticalBlock`,
`case2DisplayedPostPivotResidualBlock`,
`case2DisplayedPostPivotFollowingFactor`,
`case2DisplayedPostPivotResidualBlock_nonempty_of_next`, and
`case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct`. This
checkpoint reindexes the displayed cleared lower-right block `D - x*y` and
the transported following-factor tail of `C' = Q^-1 C` onto the next
same-stage `(S,J+1)` residual row/column domains, and proves the lower rows of
`D''' * C'` equal the product of those supplied next-block objects. It does
not prove chart production, recurrence/exponent post-data from coordinates,
chart coverage or coordinate regularity, Jacobians, normal crossings/RLCT,
termination or transition invariance, arbitrary pivot coverage, terminal
`(S+1,0)` relabeling, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-next-block-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-next-block.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-post-pivot-next-block-a4.md`.

Latest A4 update: the Case 2 stage-relabel domain audit has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq`,
`introducedLabelFinset_currentSucc_eq_succStage_zero_of_nextWidth_eq`,
`not_introducedLabel_current_of_lt_index`,
`introducedLabel_succStage_zero_extra_witness_of_nextWidth_ge`, and
`case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next`.
This checkpoint proves that the terminal frontier side split is row-prefix
exhaustion or actual next-width exhaustion, proves the old `(S,J+1)` to
`(S+1,0)` introduced-label equality under the actual-width side condition
`n(S+1)=J+1`, and records the explicit extra-label obstruction `(S,J+2)` when
actual width has not been exhausted. It does not prove the `S+1` transition,
terminal `D'''` block shape, chart production, Jacobian arithmetic, normal
crossings/RLCT, termination, transition invariance, or printed-vector repair.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-stage-relabel-domain-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-stage-relabel-domain.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-stage-relabel-domain-a4.md`.

Latest A4 update: the Case 2 displayed cleared-block vacuity corollary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean
name is `case2DisplayedClearedBlock_eq_pivotOnly_of_not_next_cont`. This
checkpoint applies displayed pivot-complement matrix vacuity to the
already-cleared pivot-first block and proves
`weightedPivotClearedBlock (D - x*y) = weightedPivotClearedBlock 0` under
displayed pivot validity and failed next continuation. It does not construct
Aoyagi's full terminal `D'''_J` branch, choose the row/column presentation,
construct `C'^(S+1)`, build the `S+1` recurrence/exponent state, prove chart
coverage or regularity, compute Jacobians, prove normal crossings/RLCT, prove
termination or transition invariance, or repair the printed vector mismatch.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-cleared-block-vacuity-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-cleared-block-vacuity.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-cleared-block-vacuity-a4.md`.

Latest A4 update: the Case 2 displayed cleared-block following-factor
absorption scaffold has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names are
`weightedPivotClearedBlock_zero_mul_verticalBlock` and
`case2DisplayedClearedBlock_mul_verticalBlock_eq_pivotOnly_of_not_next_cont`.
This checkpoint proves that a pivot-only cleared block keeps the top row of a
pivot-first following factor and kills the lower block, with a displayed
Case 2 specialization under failed next continuation. It does not construct
or identify Aoyagi's `C'^(S+1)`, construct the full terminal `D'''_J` branch,
choose the row/column presentation, build `S+1` post-data, prove chart
coverage or regularity, compute Jacobians, prove normal crossings/RLCT, prove
termination or transition invariance, or repair the printed vector mismatch.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-cleared-block-following-factor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-cleared-block-following-factor.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-cleared-block-following-factor-a4.md`.

Latest A4 update: the Case 2 displayed paper terminal absorption layer has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`.  The proved Lean names include
`matrixEntryIdeal_sumElim_zero_bottom`,
`case2DisplayedPaperDchart`, `case2DisplayedPaperQ`,
`case2DisplayedPaperQinv`, `case2DisplayedPaperDpp`,
`case2DisplayedPaperCprime`, `case2DisplayedPaperCprimeTop`,
`case2DisplayedPaperCprimeTail`,
`case2DisplayedPaperCprime_eq_verticalBlock`,
`case2DisplayedPaperDppp`, `case2DisplayedPaperDpp_eq_pivotPostQBlock`,
`case2DisplayedPaperDpp_mul_Cprime`,
`matrixEntryIdeal_case2DisplayedPaperDppp_mul_Cprime_eq_top_of_not_next_cont`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_sourceChartMap_paperQP`.
This checkpoint exposes Aoyagi's displayed Case 2 paper notation and proves
that, under displayed pivot validity and failed next continuation, `D''' * C'`
has the same matrix-entry ideal as the top pivot row of `C'`.  It does not
construct or identify Aoyagi's next-stage `C'^(S+1)`, choose the source-order
row/column terminal presentation, build `S+1` post-data, prove chart coverage
or regularity, compute Jacobians, prove normal crossings/RLCT, prove
termination or transition invariance, or repair the printed vector mismatch.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-paper-terminal-absorption-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-paper-terminal-absorption.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-paper-terminal-absorption-a4.md`.

Latest A4 update: the Case 2 displayed terminal stack layer has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`.  The proved Lean names are
`matrixEntryIdeal_sumElim_eq_sup`,
`matrixEntryIdeal_sumElim_congr_bottom`, and
`matrixEntryIdeal_case2DisplayedPaperTerminalStack_eq_topStack_of_not_next_cont`.
This checkpoint stacks an arbitrary supplied old top block over the stopped
displayed terminal bottom block and proves the matrix-entry ideal equality
`<entries([Cold; D''' * C'])> = <entries([Cold; C0])>`.  It does not identify
`Cold` with the source old top rows or `[Cold;C0]` with Aoyagi's full
`C'^(S+1)`, prove the diagonal-weighted full terminal product ideal, choose
the source-order row/column terminal presentation, build `S+1` post-data,
prove chart coverage or regularity, compute Jacobians, prove normal
crossings/RLCT, prove termination or transition invariance, or repair the
printed vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-terminal-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-terminal-stack.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-terminal-stack-a4.md`.

Latest A4 update: the Case 2 displayed weighted terminal-product layer has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean`.  The proved Lean names are
`sumElim_mul`, `matrixEntryIdeal_sumElim_zero_bottom_mul`,
`matrixEntryIdeal_sumElim_congr_bottom_mul`, and
`matrixEntryIdeal_case2DisplayedPaperWeightedTerminalProduct_eq_topStack_of_not_next_cont`.
This checkpoint keeps the supplied following suffix `F` inside the matrix
product before deleting zero residual rows and proves
`<entries((blockdiag(Wold,diag(b0,b))*[Cold;D'''*C'])*F)> =
<entries([(Wold*Cold)*F;(b0*C0)*F])>`.  It keeps the pivot-row weight `b0`;
there is no unit cancellation.  It does not identify `Cold`, `Wold`, or `F`
with the source old top rows, source diagonal weights, or source remaining
product, identify the right hand side with Aoyagi's full `C'^(S+1)`, choose
the source-order row/column terminal presentation, build `S+1` post-data,
prove chart coverage or regularity, compute Jacobians, prove normal
crossings/RLCT, prove termination or transition invariance, or repair the
printed vector mismatch. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-weighted-terminal-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-weighted-terminal-product.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-weighted-terminal-product-a4.md`.

Latest A4 update: the Case 2 displayed source-terminal candidate layer has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are `case2DisplayedPaperTerminalWeight`,
`case2DisplayedPaperTerminalCnext`,
`case2DisplayedPaperTerminalCprimeCandidate`,
`case2DisplayedPaperTerminalCprimeCandidate_eq_weight_mul_cnext_mul`,
`case2DisplayedPaperTerminalCprimeCandidate_eq_verticalBlock_mul`, and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedWeightedTerminalProduct_entryIdeal_eq_topStack_of_not_next_cont`.
This checkpoint rewrites the expanded weighted stack into Aoyagi's
source-order product shape `(blockdiag(Wold,[b0]) * [Cold;C0]) * F`, with
`b0` sourced as `post.weight (J+1)` in the supplied displayed boundary.  It
keeps `Atop`, `Ctop`, and `F` supplied; it does not identify them with the
source old diagonal weights, source old top rows, or source remaining product,
and it does not prove `[Ctop;C0]` is source-produced `C'^(S+1)`. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-source-terminal-candidate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-source-terminal-candidate.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-source-terminal-candidate-a4.md`.

Latest A4 update: the Case 2 displayed terminal source-model layer has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case2DisplayedSuppliedActualWidthTerminalSourceModel`,
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalWeightCandidate`,
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalCnextCandidate`,
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.terminalProductCandidate`,
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.not_next_cont_of_actualWidth_exhausted`,
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.introducedLabel_terminal_iff_succStage_zero`,
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.introducedLabelFinset_terminal_eq_succStage_zero`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_weightedTerminalProduct_entryIdeal_eq_terminalProductCandidate_of_actualWidth`.
This checkpoint packages supplied `Atop`, `Ctop`, and `F` with actual
next-width exhaustion `n(S+1)=J+1`.  It derives failed next continuation and
the finite introduced-label-domain equality between `(S,J+1)` and `(S+1,0)`,
then reuses the supplied displayed-boundary terminal theorem.  It does not
construct recurrence/exponent post-data over `(S+1,0)`, does not prove
`[Ctop;C0]` is source-produced `C'^(S+1)`, and does not prove chart production,
coverage, Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-terminal-source-model-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-terminal-source-model.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-displayed-terminal-source-model-a4.md`.

Latest A4 update: the Case 2 actual-width terminal relabel layer has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names
include
`IntroducedLabelExponentCertificates.relabel_currentSucc_succStage_zero_of_nextWidth_eq`,
`IntroducedLabelLevelInvariants.relabel_currentSucc_succStage_zero_of_nextWidth_eq`,
`IntroducedLabelRecurrenceState.stageRelabelSuccZero`,
`IntroducedLabelRecurrenceState.stageRelabelSuccZero_step_eq`,
`IntroducedLabelRecurrenceState.stageRelabelSuccZero_weight_eq`,
`Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost`,
`Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_step_eq_of_actualWidth`,
`Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPost_weight_eq_of_actualWidth`,
`Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelPostLevelInvariants_of_actualWidth`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.terminalRelabelExponentDomain_of_actualWidth`.
This checkpoint copies supplied old post-state recurrence maps from
`(S,J+1)` to `(S+1,0)` and transports level/exponent certificate packages
only under actual next-width exhaustion `n(S+1)=J+1`.  It does not prove chart
production, source-produced `C'^(S+1)`, automatic Case 2 gap/tail transport,
coverage, Jacobians, normal crossings/RLCT, termination, transition
invariance, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-actual-width-terminal-relabel-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-terminal-relabel.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-actual-width-terminal-relabel-a4.md`.

Latest A4 update: the Case 2 terminal relabel-weight candidate bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceTerminalEntryIdeal_eq_relabelCandidate_of_actualWidth`
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_oldTopSourceSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_actualWidth`.
This checkpoint restates the stopped supplied terminal product candidate using
the relabelled `(S+1,0)` post-state pivot weight
`terminalRelabelPost.weight(J+1)`; actual-width exhaustion derives failed next
continuation and the equality with the old `post.weight(J+1)`.  The same
scalar rewrite is now available for the source old-top/source suffix theorem
through a supplied terminal `Cterm`.  It is only a presentational bridge.  It
does not construct source-produced `C'^(S+1)`,
chart production, automatic Case 2 gap/tail transport, coverage, Jacobians,
normal crossings/RLCT, termination, transition invariance, or printed-vector
repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-terminal-relabel-weight-candidate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-relabel-weight-candidate.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-terminal-relabel-weight-candidate-a4.md`.

Latest A4 update: the Case 2 actual-width original-row terminal bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperCprimeTop_apply_of_width_next_eq`,
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperCprimeTop_eq_sourceRow_of_width_next_eq`,
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalOriginalRows`,
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_of_width_next_eq`,
`Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.of_originalRows_width_next_eq`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_oldTopSourceSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth`.
This checkpoint uses actual next-width exhaustion `n(S+1)=J+1` to empty the
displayed pivot-column complement, so the top row of `Q^-1 C` is the original
source row `C(J+1,-)`.  Consequently the terminal `C'` bridge can be
instantiated with the original source rows `1..J+1`, and the relabelled
old-top/source-suffix terminal theorem can be stated with those rows directly.
It does not generalize to failed next-continuation, prefix exhaustion, or the
row-exhausted wide-next branch, and it does not prove chart coverage,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, automatic Case 2 gap/tail transport, or printed-vector repair.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-terminal-frontier-bridges-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-frontier-bridges.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-terminal-frontier-bridges-a4.md`.

Latest A4 update: the Case 2 source-chart terminal model constructor has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.exists_terminalModelEntryIdeal_eq_relabelProductCandidate_of_sourceChartMap_actualWidth`.
This checkpoint combines
`of_sourceChartMap_case2Succ_updateSelected` with the actual-width terminal
relabel-model theorem.  It fixes the concrete successor recurrence state and
corrected selected-label exponent update, while the chart-family predicates
and terminal old-top/suffix model remain supplied.  It does not construct
source-produced `C'^(S+1)`, coverage, Jacobians, normal crossings/RLCT,
termination, transition invariance, automatic Case 2 gap/tail transport, or
printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-terminal-model-constructor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-terminal-model-constructor.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-chart-terminal-model-constructor-a4.md`.

Latest A4 update: the Case 2 actual-width column-exhaustion fact has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names
are `case2DisplayedPivotColComplement_isEmpty_of_width_next_eq` and
`Case2DisplayedSuppliedActualWidthTerminalSourceModel.displayedPivotColComplement_isEmpty`.
This checkpoint says that, under `n(S+1)=J+1`, the displayed pivot's column
complement is empty.  It identifies the exhausted side of the stopped terminal
branch only; it does not construct source-produced `C'^(S+1)`, following
data, chart production, coverage, Jacobians, normal crossings/RLCT,
termination, transition invariance, automatic Case 2 gap/tail transport, or
printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-actual-width-column-exhaustion-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-column-exhaustion.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-actual-width-column-exhaustion-a4.md`.

Latest A4 update: the Case 2 current-prefix row-exhaustion fact has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean name is
`case2DisplayedPivotRowComplement_isEmpty_of_prefixMin_current_eq`.  This
checkpoint says that, under `prefixMinNat n S=J+1`, the displayed pivot's row
complement is empty.  It identifies the row-exhausted side only; it does not
assert actual-width exhaustion, column-complement emptiness, source-produced
`C'^(S+1)`, following data, chart production, coverage, Jacobians, normal
crossings/RLCT, termination, transition invariance, automatic Case 2 gap/tail
transport, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-current-prefix-row-exhaustion-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-current-prefix-row-exhaustion.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-current-prefix-row-exhaustion-a4.md`.

Latest A4 update: the Case 2 row-exhausted transported terminal bridge has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are `case2_not_next_cont_of_prefixMin_current_eq`,
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalTransportedRows`,
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedSourceTerminalCprimeCandidate_eq_transportedRows`,
`Case2DisplayedSuppliedChartFamilyBoundary.SuppliedTerminalCprimeBridge.of_transportedRows`,
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSuffix_entryIdeal_eq_prefixProduct_of_rowExhausted`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`.
This checkpoint uses current-prefix row exhaustion `prefixMinNat n S=J+1` to
derive failed next continuation and restates the stopped source old-top/source
suffix theorem with the terminal-prefix product.  It also names the explicit
transported-row terminal matrix: rows `1..J` are original source rows, while
row `J+1` is the top row of `Q^-1 C`, including any post-pivot column
correction.  It does not assert actual next-width exhaustion, original-row
equality for the pivot row, `(S+1,0)` recurrence/exponent relabel, chart
production, coverage, Jacobian arithmetic, normal crossings/RLCT,
termination, transition invariance, automatic Case 2 gap/tail transport, or
printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-transported-terminal-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-row-exhausted-transported-terminal.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-row-exhausted-transported-terminal-a4.md`.

Latest A4 update: the Case 2 source old-top/suffix specialization has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names
are `case2SourceOldTopRowIndex`, `case2DisplayedSourceOldTopWeight`,
`case2DisplayedSourceOldTopBlock`, and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSuffixTerminalProduct_entryIdeal_eq_of_not_next_cont`.
This checkpoint specializes the stopped displayed terminal theorem by taking
the old top rows to be source rows `1..J`, the old top multiplier to be
`diag(pre.weight i)`, and the old top block to be the source row restriction
of the supplied following matrix.  The suffix `F` remains supplied; this does
not construct `prod_{s=S+2}^L C^(s)`, source-produced `C'^(S+1)`, chart
production, coverage, Jacobians, normal crossings/RLCT, termination,
transition invariance, automatic Case 2 gap/tail transport, or printed-vector
repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-old-top-suffix-specialization-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-old-top-suffix-specialization.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-old-top-suffix-specialization-a4.md`.

Latest A4 update: the Case 2 source suffix-chain checkpoint has landed in
`lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean` and
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`. The proved Lean names
include `paperMatrixChain`, `paperMatrixChain_self`,
`paperMatrixChain_proof_irrel`, `paperMatrixChain_succ_right`,
`paperMatrixChain_edge`, `sourceLayerIndex`, `sourceEdgeIndex`,
`sourceEdgeIndex_castSucc`, `sourceEdgeIndex_succ`, `sourceSuffixProduct`, and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceDisplayedOldTopSourceSuffixProduct_entryIdeal_eq_of_not_next_cont`.
This checkpoint names Aoyagi's remaining right product
`prod_{s=S+2}^L C^(s)` and instantiates the stopped source old-top terminal
theorem with that named suffix. It does not construct source-produced
`C'^(S+1)`, chart production, coverage, Jacobians, normal crossings/RLCT,
termination, transition invariance, automatic Case 2 gap/tail transport, or
printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-suffix-chain-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-suffix-chain.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-suffix-chain-a4.md`.

Latest A4 update: the Case 2 source terminal product candidate, product form,
and terminal-frontier bridges have landed in
`lean/DLNFibre/DLN/Aoyagi/EntryIdeal.lean` and
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names
include `matrixEntryIdeal_submatrix_equiv`,
`pivotQinv_mul_top_apply`,
`case2DisplayedPaperCprimeTop_apply`,
`case2SourceTerminalRowIndex`, `case2SourceTerminalRowEquiv`,
`case2DisplayedSourceTerminalCprimeCandidate`,
`case2DisplayedSourceTerminalProductReindexedCandidate`,
`case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_cprimeCandidate_mul`,
`case2SourceTerminalPrefixRowIndex`,
`case2SourceTerminalRowEquivPrefixOfNotNext`,
`SuppliedTerminalCprimeBridge`,
`case2DisplayedSourceTerminalCprimeCandidate_eq_of_oldRows_pivotRow`,
`case2DisplayedSourceTerminalProductReindexedCandidate_eq_weight_mul_suppliedCterm_mul`,
`SuppliedTerminalCprimeBridge.cprimeCandidate_eq`,
`SuppliedTerminalCprimeBridge.terminalProduct_eq_weight_mul_Cterm_mul`,
`SuppliedTerminalCprimeBridge.cprimePrefixCandidate_eq`,
`SuppliedTerminalCprimeBridge.terminalPrefixProduct_eq_weight_mul_CtermPrefix_mul`,
`case2DisplayedSourceTerminalProductPrefixCandidate`,
`case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_cprimePrefixCandidate_mul`,
`matrixEntryIdeal_sourceTerminalProductPrefixCandidate_eq_sourceTerminalProduct`,
`matrixEntryIdeal_sourceTerminalProductReindexedCandidate_eq_terminalCprimeCandidate`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`,
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`,
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_suppliedTerminalPrefixProduct_of_not_next_cont`,
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopSourceSuffix_entryIdeal_eq_sourceTerminalPrefixProduct_of_not_next_cont`.
These checkpoints reindex the already proved stopped terminal candidate into
one-based source rows `1..J+1`, reindex it again onto terminal prefix rows
`1..M(S+1)` under stopped continuation, and prove that the reindexed candidate is
`(case2DisplayedSourceTerminalWeight *
case2DisplayedSourceTerminalCprimeCandidate) * F`. The surviving top row of
`Q^-1 C` is now expanded entrywise as the old pivot-column row plus the
displayed pivot-row weighted post-pivot column sum. The supplied bridge is now
usable in the source-row product, the terminal-prefix product, and the stopped
source old-top/source suffix theorem in both source-row and prefix-row form.
They do not prove
source-produced `C'^(S+1)`, chart production, coverage, Jacobians, normal
crossings/RLCT, termination, transition invariance, automatic Case 2 gap/tail
transport, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-terminal-product-candidate-a4.md`.
Product-form reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-terminal-product-form-a4.md`.
Terminal-frontier reproduction:
`threads/04-blow-up-certificate/reproduction-case2-terminal-frontier-bridges-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-terminal-product-candidate.md`.
Product-form statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-terminal-product-form.md`.
Terminal-frontier statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-frontier-bridges.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-terminal-product-candidate-a4.md`.
Product-form review artifact:
`threads/04-blow-up-certificate/review-case2-source-terminal-product-form-a4.md`.
Terminal-frontier review artifact:
`threads/04-blow-up-certificate/review-case2-terminal-frontier-bridges-a4.md`.

Latest A4 update: the Case 2 source-chart terminal source-suffix wrappers have
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopSuffix_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`.
This checkpoint composes
`of_sourceChartMap_case2Succ_updateSelected` with the actual-width original-row
terminal theorem and the row-exhausted transported-row terminal theorem.  The
post recurrence state is now the displayed source-chart successor
`pre.case2Succ(case2DisplayedSourceChartMap(...)(J+1,J+1))`, and the exponent
post-data are the corrected selected-label overrides.  It keeps the two
terminal sides separate: actual-width exhaustion gives original terminal rows
`1..J+1`, while current-prefix row exhaustion keeps row `J+1` transported as
the top row of `Q^-1 C`.  It does not prove chart coverage, chart-produced
post-data, source-produced `C'^(S+1)`, Jacobian arithmetic, normal
crossings/RLCT, termination, transition invariance, automatic Case 2 gap/tail
transport, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-terminal-source-suffix-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-terminal-source-suffix.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-chart-terminal-source-suffix-a4.md`.

Latest A4 update: the raw source suffix chain split has landed in
`lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`.  The proved Lean name is
`paperMatrixChain_trans`.  It states that the raw paper-order chain splits at
an intermediate layer as
`paperMatrixChain(i,j)=paperMatrixChain(i,m)*paperMatrixChain(m,j)`, with the
orientation matching the existing right-extension theorem
`paperMatrixChain_succ_right`.  This is only raw matrix-chain algebra; it does
not yet prove source-suffix empty/peel wrappers, chart production, or any
analytic result. Reproduction:
`threads/04-blow-up-certificate/reproduction-source-suffix-chain-split-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-source-suffix-chain-split.md`.
Review artifact:
`threads/04-blow-up-certificate/review-source-suffix-chain-split-and-actual-width-boundary-a4.md`.

Latest A4 update: the Case 2 actual-width source-chart terminal boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsBoundary`.
This checkpoint packages the actual-width original-row terminal source-suffix
entry-ideal equality with the actual-width relabelled level invariant and
exponent-domain certificate for `(S+1,0)`.  It uses
`n(S+1)=J+1`; it does not apply to the row-exhausted wide-next branch and does
not prove source-produced `C'^(S+1)`, chart coverage, chart-produced post-data,
Jacobian arithmetic, normal crossings/RLCT, termination, transition
invariance, automatic Case 2 gap/tail transport, or printed-vector repair.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-actual-width-source-chart-terminal-boundary-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-source-chart-terminal-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-source-suffix-chain-split-and-actual-width-boundary-a4.md`.

Latest A4 update: source-suffix utility wrappers have landed in
`lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`.  The proved Lean names are
`sourceSuffixProduct_proof_irrel`,
`sourceSuffixProduct_eq_paperMatrixChain`, and
`sourceSuffixProduct_split_at`.  They show that Aoyagi's raw suffix
`prod_{s=S+2}^L C^(s)` is proof-irrelevant in the endpoint bound, is the raw
paper-order chain from source layer `S+2` to the final source layer, and splits
at a source layer `T` under `S+2<=T<=L+1`.  Endpoint splits are allowed, but
endpoint identity simplifications are not proved.  They do not prove the
one-edge source-suffix peel, empty suffix identity, chart production, or any
analytic result. Reproduction:
`threads/04-blow-up-certificate/reproduction-source-suffix-utilities-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-source-suffix-utilities.md`.
Review artifact:
`threads/04-blow-up-certificate/review-source-suffix-utilities-a4.md`.

Latest A4 update: the source-suffix one-edge peel has landed in
`lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`.  The proved Lean names are
`paperMatrixChain_succ_left`, `sourceSuffixFirstEdge`, and
`sourceSuffixProduct_peel`.  Under `S+2<=L`, Aoyagi's raw suffix
`prod_{s=S+2}^L C^(s)` rewrites as the first source edge times the next
suffix, with the first edge reindexed to the adjacent source-suffix endpoints.
This is raw matrix-chain algebra only; it does not prove the empty-suffix
identity, chart production, or any analytic result. Reproduction:
`threads/04-blow-up-certificate/reproduction-source-suffix-peel-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-source-suffix-peel.md`.
Review artifact:
`threads/04-blow-up-certificate/review-source-suffix-peel-a4.md`.

Latest A4 update: arbitrary supplied-suffix terminal wrappers have landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`exists_sourceOldTopSuffix_entryIdeal_eq_sourceTerminalProduct_of_not_next_cont`,
`exists_sourceOldTopSuffix_entryIdeal_eq_suppliedTerminalCprimeProduct_of_not_next_cont`,
`exists_oldTopSuffix_entryIdeal_eq_relabelSuppliedTerminalProduct_of_actualWidth`,
and
`exists_oldTopSuffix_entryIdeal_eq_relabelOriginalRowsTerminalProduct_of_actualWidth`.
They keep the following product as an arbitrary supplied matrix `F`, then
reindex the stopped paper terminal candidate into source rows and optionally
rewrite through a supplied terminal `C'` bridge.  The actual-width original-row
specialization still requires `n(S+1)=J+1` and does not cover row-exhausted
wide-next cases.  These are packaging/reindexing theorems only; they do not
prove chart production or any analytic result. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-arbitrary-suffix-terminal-wrapper-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-arbitrary-suffix-terminal-wrapper.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-arbitrary-suffix-terminal-wrapper-a4.md`.

Latest A4 update: the concrete source-chart actual-width terminal boundary now
also has an arbitrary supplied-suffix form in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`exists_sourceChart_oldTopSuppliedSuffix_entryIdeal_eq_originalRowsProduct_of_actualWidth`
and `sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary`.
They compose the displayed source-chart constructor with the arbitrary-`F`
actual-width original-row wrapper, keeping `F : Matrix τ υ R` supplied while
fixing the post recurrence state and relabelled level/exponent certificates.
This does not apply to row-exhausted wide-next cases and does not prove chart
coverage, source-produced `C'^(S+1)`, chart-produced following product, or any
analytic result. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-arbitrary-suffix-actual-width-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-arbitrary-suffix-actual-width.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-chart-arbitrary-suffix-actual-width-a4.md`.

Latest A4 update: the displayed source-chart actual-width terminal boundary is
now packaged together with finite residual-block center principalization in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary_withFiniteCenterIdeal`.
It conjoins the arbitrary-`F` actual-width original-row terminal boundary with
the finite center facts that `u` is a transformed center value, every
transformed center value is divisible by `u`, and the transformed finite center
ideal is `Ideal.span {u}`.  The following matrix `F` and the residual-block
`chartFamily` remain supplied, and actual-width exhaustion `n(S+1)=J+1` remains
the original-row/relabel side condition.  This does not principalize the
terminal product ideal, construct chart coverage, produce `C'^(S+1)` or the
following product, or prove any analytic result. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-principalized-source-chart-actual-width-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-principalized-source-chart-actual-width.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-principalized-source-chart-actual-width-a4.md`.

Latest A4 update: the terminal-last source suffix identity has landed in
`lean/DLNFibre/DLN/Aoyagi/MatrixChain.lean`.  The proved Lean names are
`sourceLayerIndex_terminalLast` and
`sourceSuffixProduct_terminalLast_eq_cast_one`.  Under `S+1=L`, the lower
source-suffix endpoint `S+2` is the final source layer, so
`sourceSuffixProduct` is the empty raw paper-order chain; the identity matrix
is stated with the required dependent endpoint transport.  This is raw
matrix-chain algebra only.  It supplies an identity for terminal-last wrappers
whose following factor is exactly this source suffix, but it does not justify
setting an arbitrary supplied matrix `F` to `1` away from the empty-suffix
case. Reproduction:
`threads/04-blow-up-certificate/reproduction-source-suffix-terminal-last-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-source-suffix-terminal-last.md`.
Review artifact:
`threads/04-blow-up-certificate/review-source-suffix-terminal-last-a4.md`.

Latest A4 update: the Case 2 actual-width identity-following boundary has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary`.
It specializes the arbitrary-following displayed source-chart actual-width
boundary to `F = 1`, removes the rightmost following factor by unit
simplification, and keeps actual-width exhaustion `n(S+1)=J+1` visible.  This
does not prove that a source suffix is empty; applying it to the source suffix
requires the separate raw terminal-last identity
`sourceSuffixProduct_terminalLast_eq_cast_one`.  It does not apply to
row-exhausted wide-next cases, source-produce `C'^(S+1)`, or prove chart
coverage/Jacobian/analytic results. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-identity-following-actual-width-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-identity-following-actual-width.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-identity-following-actual-width-a4.md`.

Latest A4 update: the Case 2 actual-width terminal-last boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case2DisplayedSuppliedChartFamilyBoundary.matrixEntryIdeal_mul_ndrec_one`,
`Case2DisplayedSuppliedChartFamilyBoundary.matrixEntryIdeal_mul_sourceSuffixProduct_terminalLast`,
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_originalRowsProduct_of_actualWidth`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalLastOriginalRowsBoundary`.
It consumes Aoyagi's raw source suffix under `S+1=L`, removes it by the
terminal-last empty-chain identity, and packages the resulting actual-width
original-row boundary with the relabelled level/exponent certificates.  This
still requires `n(S+1)=J+1` and does not cover row-exhausted wide-next cases,
source-produce `C'^(S+1)`, or prove chart coverage/Jacobian/analytic results.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-terminal-last-actual-width-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-last-actual-width.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-terminal-last-actual-width-a4.md`.

Latest A4 update: the Case 2 row-exhausted terminal-last boundary has landed
in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names
are
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceOldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`
and
`Case2DisplayedSuppliedChartFamilyBoundary.exists_sourceChart_oldTopTerminalLast_entryIdeal_eq_transportedPrefixProduct_of_rowExhausted`.
It consumes Aoyagi's raw source suffix under `S+1=L`, removes it by the
terminal-last empty-chain identity at the matrix-entry-ideal level, and keeps
the terminal side as transported prefix rows under `prefixMinNat n S=J+1`.
It does not identify row `J+1` with original source rows, does not relabel to
`(S+1,0)`, and does not prove chart coverage/source-production/Jacobian or
analytic results. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-terminal-last-row-exhausted-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-last-row-exhausted.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-terminal-last-row-exhausted-a4.md`.

Latest A4 update: the terminal-last source-chart boundaries are now packaged
with finite residual-block center principalization in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalLastOriginalRowsBoundary_withFiniteCenterIdeal`
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_terminalLastTransportedPrefixBoundary_withFiniteCenterIdeal`.
They conjoin the terminal-last product boundary with the finite center facts
that `u` is a transformed center value, all transformed center values are
divisible by `u`, and the transformed finite center ideal is `Ideal.span {u}`.
The row-exhausted package keeps transported prefix rows and no `(S+1,0)`
relabelled certificates.  These do not principalize the terminal product ideal
or prove chart coverage/source-production/Jacobian or analytic results.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-principalized-terminal-last-boundaries-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-principalized-terminal-last-boundaries.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-principalized-terminal-last-boundaries-a4.md`.

Latest A4 update: the Case 2 source-chart post-pivot boundary has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct`,
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotResidualBlock_nonempty_of_next`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withCorrectedPostData`.
They project the continuing-branch post-pivot next-block adapter from the
displayed supplied boundary, keep the nonempty next-center condition as the
explicit bound `J+2 <= prefixMinNat n (S+1)`, and instantiate the concrete
displayed source-chart constructor with corrected supplied post-data
projections.  This connects the lower-row `D''' * C'` product to the same
`(S,J+1)` successor slot as the corrected recurrence/exponent boundary.  It
does not claim chart production, successor chart-family construction,
coverage, coordinate regularity, transition invariance, Jacobian arithmetic,
normal crossings/RLCT, arbitrary pivot coverage, terminal relabeling, or
printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-post-pivot-boundary-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-post-pivot-boundary.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-source-chart-post-pivot-boundary-a4.md`.

Latest A4 update: the Case 2 post-pivot following-factor tail has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`pivotQinv_mul_tail_apply`, `case2DisplayedPaperCprimeTail_apply`, and
`case2DisplayedPostPivotFollowingFactor_eq_sourceFollowingFactor_succ`,
together with raw-value simp lemmas for the displayed pivot-complement
equivalences to the next same-stage row/column domains.  This checkpoint
records that `Q^-1 = [1 y; 0 I]` changes only the pivot row of the following
factor.  Therefore the post-pivot following-factor candidate, reindexed to
`(S,J+1)` columns, is exactly the source following factor restricted to those
next same-stage columns.  It does not identify this with Aoyagi's full next
`C'^(S+1)`, prove chart-produced recurrence/exponent data, construct a
successor chart-family boundary, prove coverage, coordinate regularity,
transition invariance, Jacobian arithmetic, normal crossings/RLCT, arbitrary
pivot coverage, terminal relabeling, or printed-vector repair. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-following-factor-tail-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-following-factor-tail.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-post-pivot-following-factor-tail-a4.md`.

Latest A4 update: the Case 2 post-pivot source-following product adapter has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are
`case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_nextSameStageProduct_sourceFollowingFactor`,
`Case2DisplayedSuppliedChartFamilyBoundary.postPivotNextSameStageProduct_sourceFollowingFactor`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData`.
They combine the post-pivot next-block product with the tail identity for
`C' = Q^-1 C`, so the lower rows of `D''' * C'` are written directly as the
post-pivot residual block times
`case2SourceFollowingFactor (J := J+1) C`.  The concrete package keeps the
corrected supplied post-data projections.  This is still a supplied-data
continuing-branch adapter; it does not prove chart production, successor
chart-family construction, full source-produced `C'^(S+1)`, transition
invariance, chart coverage, Jacobian arithmetic, normal crossings/RLCT,
terminal relabeling, arbitrary pivot coverage, or printed-vector repair.
The companion blocker audit records that these stronger chart-production
claims are not source-faithful from the present PDF/API boundary. Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-post-pivot-source-following-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-post-pivot-source-following-product.md`.
Blocked audit:
`threads/04-blow-up-certificate/blocked-audit-case2-chart-production-next-following-a4.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-post-pivot-source-following-product-a4.md`.

Latest A4 update: the displayed Case 2 free-`Cprime` lower-row product now
has a nondependent two-edge factor-product name in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct` and
`case2DisplayedPaperDppp_mul_freeCprime_postPivot_eq_freeTwoEdgeFactorProduct`.
They name the already-proved RHS
`case2DisplayedPostPivotResidualBlock * case2DisplayedPostPivotFreeFollowingFactor`
without introducing a dependent residual-factor family.  This is a vocabulary
boundary for later residual-factor sockets only: it does not construct the
ambient p.13 factor family, source-produce `Cprime`, prove source coverage,
construct a residual-index equivalence, or prove normal crossings/RLCT.
Updated artifacts:
`threads/04-blow-up-certificate/reproduction-case2-free-cprime-continuing-branch-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-free-cprime-continuing-branch.md`,
and
`threads/04-blow-up-certificate/review-case2-free-cprime-continuing-branch-a4.md`.

Latest A4 update: the displayed Case 2 constructed-`Cprime` coordinate
direction has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean names are
`case2DisplayedPaperConstructedFollowingFactor`,
`case2DisplayedPaperCprime_of_constructedFollowingFactor`, and
`case2DisplayedPaperDpp_mul_constructedCprime`.  Given an arbitrary
pivot-first chart-coordinate following matrix `Cprime`, Lean constructs the
old pivot-first following factor as `Q*Cprime`, proves
`Q^-1*(Q*Cprime)=Cprime`, and rewrites `D''*Cprime` as
`D_chart*(Q*Cprime)`.  This is finite matrix algebra only.  It does not
construct a total source-coordinate following function, recurrence/exponent
post-data, a successor chart family, chart coverage, Jacobian arithmetic,
normal crossings/RLCT, arbitrary pivot coverage, terminal relabeling, or the
printed-vector repair.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-cprime-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-cprime.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-constructed-cprime-a4.md`.

Latest A4 update: the displayed Case 2 constructed-`Cprime` `Q/P` product
identity has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean names are
`exists_case2DisplayedQP_mul_arbitraryPivotFirstFollowingFactor_of_flat_weights`,
`CorrectedCase2NewLabelCertificate.exists_case2DisplayedQP_mul_freeFollowingFactor_of_postData`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedCprime_paperQP`.
Given a free pivot-first chart-coordinate following matrix `Cprime`, Lean uses
the constructed old factor `Q*Cprime` in the displayed `Q/P` row-operation
identity and rewrites the right side to `(weighted D''')*Cprime`.  This is
finite product algebra only.  It does not construct a total source-coordinate
following function, source-produce next `C'^(S+1)`, produce
recurrence/exponent post-data, build a successor chart family, prove chart
coverage, Jacobian arithmetic, normal crossings/RLCT, arbitrary pivot
coverage, terminal relabeling, or the printed-vector repair.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-cprime-qp-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-cprime-qp.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-constructed-cprime-qp-a4.md`.

Latest A4 update: the displayed Case 2 constructed source following-factor
lift has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean names are
`case2DisplayedConstructedSourceFollowingFactor`,
`case2DisplayedSourceFollowingFactor_constructed`,
`case2DisplayedPaperCprime_of_constructedSourceFollowingFactor`, and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceDisplayedQP_constructedSourceFollowingFactor_paperQP`.
Lean zero-extends a supplied pivot-first residual following matrix to a total
source-coordinate function and proves that restricting it back with
`case2DisplayedSourceFollowingFactor` recovers the supplied matrix.  With the
special supplied matrix `Q*Cprime`, the paper-named inverse update recovers
`Cprime`, and the supplied-boundary `Q/P` identity can be expressed using this
total source-coordinate old following factor.  This is finite reindexing and
matrix algebra only.  It does not source-produce the full next
`C'^(S+1)`, produce recurrence or exponent post-data, build a successor chart
family, prove chart coverage, Jacobian arithmetic, normal crossings/RLCT,
arbitrary pivot coverage, terminal relabeling, or the printed-vector repair.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-source-following-factor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-source-following-factor.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-constructed-source-following-factor-a4.md`.

Latest A4 update: the displayed Case 2 terminal-prefix transported-product
rewrite has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.
The proved Lean name is
`case2DisplayedSourceTerminalProductPrefixCandidate_eq_weight_mul_transportedRowsPrefix_mul`.
It rewrites the stopped terminal-prefix product candidate as terminal-prefix
weight times the explicit transported terminal rows, followed by the supplied
suffix.  The pivot row remains the transported top row of `Q^{-1}C`; no
original-row identification is made without actual-width exhaustion.  This is
finite terminal-prefix algebra only, not chart production, source-produced
`C'^(S+1)`, recurrence/exponent post-data, transition invariance, Jacobian
arithmetic, normal crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-terminal-prefix-transported-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-terminal-prefix-transported-product.md`.
Review artifact:
`threads/04-blow-up-certificate/review-case2-terminal-prefix-transported-product-a4.md`.

Latest A5 update: the Lemma 5 equation `(3)` local-data and actual-label
bridge has landed in
`lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The proved Lean names are
`aoyagiLemma5Eq3_localData_of_widthGuards`,
`aoyagiHtildeUpperNat_one_add_one_labelBounds_of_sourceSelectedInequality_and_slack`,
`aoyagiLemma5Eq3_slack_not_forced_by_selectedWidthHypotheses_example`,
`aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack`,
`aoyagiLemma5Eq3_actualWidthLabel_of_widthCompatibility`, and
`aoyagiLemma5Eq3_actualWidthLabel_of_sourceSelectedInequality_and_slack`.
They prove equation `(3)`'s selected cutoff, first Htilde gap, selected-label
bounds, and actual-label bridge only under the explicit one-unit slack
`W_1+2<=M`.  Lean now records a closed Definition 3-shaped counterexample
`ell=3`, `a=2`, `M=3`, all selected widths `2`, where the selected-sum and
strict selected-width inequalities hold but the slack and selected-label upper
bound fail.  Thus label legality from Definition 3 alone remains blocked.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-local-data-and-label-a5.md`.
Slack counterexample reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-slack-counterexample-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-local-data-and-label.md`.
Slack counterexample statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-slack-counterexample.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-local-data-and-piecewise-a5.md`.
Slack counterexample review:
`threads/05-arithmetic-tail/review-lemma5-eq3-slack-counterexample-a5.md`.

Latest A5 update: the Lemma 5 equation `(3)` supplied piecewise certificate
has landed in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The
proved Lean names are `AoyagiLemma5Eq3PiecewiseSourceVector`,
`AoyagiLemma5Eq3SelectedSpanBranchValue`,
`aoyagiLemma5Eq3_branchValue_of_block`,
`aoyagiLemma5Eq3_selectedSpan_branchValue`, and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack`.
They classify supplied equation `(3)` branch data on the half-open selected
span and recover the own-coordinate selected-label handoff under Definition 3
plus the explicit slack `W_1+2<=M`.  This is not a displayed-vector
construction, terminal endpoint theorem, or order-count theorem.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-piecewise-certificate-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-piecewise-certificate.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-local-data-and-piecewise-a5.md`.

Latest A5 update: the Lemma 5 equation `(3)` terminal obstruction has landed
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean
name is `aoyagiLemma5Eq3_terminalEndpoint_one_of_one`.  It says that for a
supplied equation `(3)` certificate with `a=1`, the special boundary is the
terminal selected endpoint and the selected-sum identity forces the supplied
boundary value to be `1`.  Thus terminal endpoint zero cannot follow from the
printed equation `(3)` branch assignment in that boundary case.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-terminal-obstruction-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-terminal-obstruction.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-terminal-obstruction-a5.md`.

Latest A5 update: the Lemma 5 equation `(3)` boundary split has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are
`aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector`,
`aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff`,
`aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le`,
`aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le`,
`aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le`,
`aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one`,
`aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one`, and
`aoyagiLemma5Eq3_no_terminalEndpointZero_of_one`.  They say that under the
supplied equation `(3)` guards, the special boundary `S_(ell-a+2)-1` is in
the half-open selected span exactly in the case `2<=a`; when `a=1` it is the
terminal selected endpoint, belongs to no selected block, and cannot also be
assigned value zero under the selected-sum identity.  This is boundary
bookkeeping only, not displayed-vector construction, terminal `tilde t=0`, or
order count.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-boundary-split-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-boundary-split.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-boundary-split-a5.md`.

Latest A5 update: the Lemma 5 equation `(3)` interval obstruction has landed
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean
names are `aoyagiLemma5Eq3_boundaryValue_gt_upperNat`,
`aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat`, and
`aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le`.  They
say that for a supplied equation `(3)` certificate, the special boundary value
is `Htilde'_(ell-a+1)+1`, hence is strictly above the upper endpoint of the
same-coordinate interval and is not in
`aoyagiHtildeIntervalValueSetNat ell a M m (ell-a+1)`.  Under `2<=a`, the
previous boundary split places that same point in the half-open selected span,
so this records that the selected-span singleton is outside the interval-value
family counted by the `Htilde` arithmetic layer.  This is interval
bookkeeping only, not displayed-vector construction, terminal `tilde t=0`, or
order count.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-interval-obstruction-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-interval-obstruction.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-interval-obstruction-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` terminal-collision arithmetic has
landed in `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are `aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum`,
`aoyagiLemma5Eq4_lastWidthCompatibility_not_forced_by_selectedWidthHypotheses_example`,
`aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary`, and
`aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary`.  They
say that when `p+1=a`, the supplied equation `(4)` special boundary is the
terminal selected endpoint and its displayed branch value is
`M-W_(ell+1)-p+1`; zero at this endpoint is equivalent to the extra condition
`W_(ell+1)=M-p+1`.  The concrete Lean example
`ell=3`, `a=2`, `p=1`, `M=3`, all selected widths `2`, satisfies the
selected-sum and strict selected-width inequalities but fails this
compatibility, so Definition 3 does not force it.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-collision-a5.md`.
Counterexample reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-compatibility-counterexample-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-terminal-collision.md`.
Counterexample statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-terminal-compatibility-counterexample.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-terminal-collision-a5.md`.
Counterexample review:
`threads/05-arithmetic-tail/review-lemma5-eq4-terminal-compatibility-counterexample-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` `p=1` terminal-extension
obstruction has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean name
is
`aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality`.
It says that in the `p=1` terminal-collision case, Definition 3's
selected-width hypotheses rule out the supplied terminal upper-chain extension:
the extension would force `W_(ell+1)=M`, while Definition 3 gives
`W_(ell+1)<=M-1`.  This is finite supplied-data arithmetic only; it does not
construct the supplied certificate, construct a terminal extension, prove
terminal `tilde t=0`, or prove Lemma 5.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-p1-terminal-extension-obstruction-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-p1-terminal-extension-obstruction.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-p1-terminal-extension-obstruction-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` terminal-extension necessary
condition has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are
`aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected`
and
`aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two`.
They say that in the terminal-collision case, Definition 3's selected-width
hypotheses force `2<=p` if a supplied terminal upper-chain extension is also
imposed; equivalently, `p<2` rules out that extension.  The theorem is stated
for the totalized supplied-certificate API, so the `p=0` edge is a
Lean-totalized supplied-certificate consequence, not an additional printed
source case.  This is finite supplied-data arithmetic only; it does not
construct the supplied certificate, construct a terminal extension, prove
terminal `tilde t=0`, or prove Lemma 5.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-terminal-extension-forces-p-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-terminal-extension-forces-p.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-terminal-extension-forces-p-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` no-terminal-upper-extension
example has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are
`aoyagiLemma5Eq4_terminalEndpoint_values_ell3_a2_p1_allWidthsTwo` and
`aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo`.
It says that for `ell=3`, `a=2`, `p=1`, `M=3`, and all selected widths equal
to `2`, any supplied equation `(4)` certificate is incompatible with the
supplied terminal upper-chain extension
`T(S_(ell+1)-1)=Htilde'_ell`.  Lean also records the concrete endpoint values:
the supplied branch value is `1`, while `Htilde'_ell=0`.  This is the finite
incompatibility obtained by combining the existing terminal-extension
obstruction with the closed Definition 3-shaped counterexample; it does not
construct the supplied certificate, construct a terminal extension, prove
terminal `tilde t=0`, or prove Lemma 5.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-no-terminal-upper-extension-example-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-no-terminal-upper-extension-example.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-no-terminal-upper-extension-example-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` strict-boundary interval
classifier has landed in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.
The proved Lean names are
`aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le`,
`aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_of_two_mul_le`, and
`aoyagiLemma5Eq4_boundaryValue_not_mem_intervalValueSetNat_of_lt_two_mul`.
They say that for a supplied equation `(4)` certificate with `1<=p`,
`p+1<a`, and `p<=ell-a`, the special boundary value belongs to the
same-coordinate interval value set at coordinate `p+(ell-a)` exactly when
`2*p<=a+1`.  This is a classifier, not a uniform nonmembership result; a
blanket Eq3-style obstruction for Eq4 would be false.  It makes no
normal-crossing or RLCT extraction claim.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-interval-classifier-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-interval-classifier.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-interval-classifier-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` boundary-coordinate width-window
classifier has landed in
`lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`,
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`, and
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are `aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment`,
`aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min`,
`aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate`,
`aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow`,
`aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min`,
`aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected`, and
`aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_p1_sourceSelected`.
They say that in the strict equation `(4)` boundary case, at the boundary
block's own coordinate `r=p+(ell-a)+1`, interval membership is equivalent to
the width window `M-p+1 <= W_r <= M-p+1+excess(ell,a,r)`, with
`excess(ell,a,r)=min(ell-a,a-p-1)`.  For `p=1`, Definition 3's selected-width
upper bound forces nonmembership by putting the boundary value strictly above
the upper endpoint.  This is finite supplied-branch arithmetic only and makes
no displayed-vector, order-count, normal-crossing, or RLCT extraction claim.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-boundary-coordinate-window-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-boundary-coordinate-window.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-boundary-coordinate-window-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` boundary-coordinate
source-selected obstruction has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are
`aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected`
and
`aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two`.
They say that for a supplied equation `(4)` certificate in the strict boundary
case `p+1<a`, Definition 3's selected-width hypotheses force `2<=p` if the
boundary value belongs to its own boundary-coordinate interval.  Equivalently,
`p<2` rules out boundary-coordinate membership.  This is only a necessary
condition: it does not assert membership for `p>=2`, construct the displayed
vector, prove terminal `tilde t=0`, chart sequence, introduced-label status,
Lemma 5 order count, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-boundary-membership-forces-p-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-boundary-membership-forces-p.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-boundary-membership-forces-p-a5.md`.

Latest A5 update: the Lemma 5 equation `(4)` `p=2` boundary-coordinate
membership guardrail has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are
`aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example`
and
`aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_sourceSelected_example`.
For `ell=5`, `a=4`, `p=2`, `M=5`, and all selected widths equal to `4`, any
supplied equation `(4)` certificate puts the strict boundary value in its
boundary-coordinate interval; the source-selected wrapper also packages the
selected-width sum and strict selected-width inequalities for the same tuple.
This shows that the previous theorem `membership -> 2<=p` is only a necessary
condition, not a uniform
nonmembership theorem for `p>=2`.  The example does not construct the supplied
certificate or displayed vector, and it does not prove terminal `tilde t=0`,
chart sequence, introduced-label status, Lemma 5 order count, normal
crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-boundary-membership-p2-example-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-boundary-membership-p2-example.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-boundary-membership-p2-example-a5.md`.

Latest A5 update: the Lemma 5 equation `(5)` own-coordinate offset slice has
landed in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved
Lean names are `AoyagiLemma5Eq5OwnCoordinateBranch`,
`aoyagiLemma5Eq5OffsetValueSet`,
`aoyagiLemma5Eq5_offsetValue_injective`,
`aoyagiLemma5Eq5OffsetValueSet_card`,
`aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat`,
`aoyagiLemma5Eq5_ownCoordinate_value`,
`aoyagiLemma5Eq5_ownCoordinate_eq_label_pred`,
`aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat`, and
`aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet`.  They record only a
supplied own-coordinate equation `(5)` branch: with paper `j0` represented by
Lean coordinate `p`, the own block gives `T(s)=Htilde'_p-alpha`; under the
label relation `k=Htilde'_p+1-alpha`, this is `k-1`; and under
`alpha<=Htilde'_p-Htilde_p`, the value lies in the same-coordinate interval.
The finite offset-value set has cardinality `min(excess(ell,a,p),p-1)`.  This
does not construct equation `(5)`'s displayed vector, prove source-label
legality, selected-span classification, terminal `tilde t=0`, chart sequence,
Lemma 5 order count, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-own-coordinate-offset-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-own-coordinate-offset.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-own-coordinate-offset-a5.md`.

Latest A5 update: the Eq5 strict alpha-family value-image API wrapper has
landed in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved
Lean name is
`aoyagiLemma5Eq5_alphaFamily_value_image_eq_offsetValueSet`.  It states that
the image of
`1<=alpha<=min(excess(ell,a,p),p-1)` under
`alpha |-> Htilde'_p-alpha` is exactly
`aoyagiLemma5Eq5OffsetValueSet ell a p M m`; the proof is definitional.  This
is not displayed-vector construction, source-label legality, selected-span
coverage, terminal `tilde t=0`, chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-value-image-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-family-value-image.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-family-value-image-a5.md`.

Latest A5 update: the Eq5 strict alpha-family source-label adapter has landed
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The proved Lean names are
`aoyagiLemma5Eq5_alphaFamily_mem_iff_guards` and
`aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound`.  The guard
theorem rewrites strict-alpha-domain membership as `1<=alpha`,
`alpha<=excess(ell,a,p)`, and `alpha<p`; the label adapter feeds the first two
guards into the existing Eq5 source-label theorem under explicit source-index
bounds, actual-width dominance, selected-width hypotheses, and the supplied
label relation.  This does not construct Eq5 vectors, prove branch existence,
derive the cutoff guard, prove selected-span coverage, terminal `tilde t=0`,
chart sequence, classifier/injection/back-to-label coverage, Lemma 5 order
count, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-family-source-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-family-source-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-family-source-label-a5.md`.

Latest A5 update: the Eq5 alpha-indexed branch value-image bridge has landed
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean
names are `aoyagiLemma5Eq5AlphaDomain` and
`aoyagiLemma5Eq5_alphaIndexedBranch_value_image_eq_offsetValueSet`.  If a
supplied finite branch family has alpha image exactly the strict Eq5 alpha
domain and branchwise values `Htilde'_p-alphaOf b`, Lean proves its value
image is `aoyagiLemma5Eq5OffsetValueSet ell a p M m`.  This is finite-set
bookkeeping only, not branch construction, source-label legality,
selected-span/cutoff coverage, injection, classifier/back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-indexed-branch-value-image.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-indexed-branch-value-image-a5.md`.

Latest A5 update: the Eq5 post-`p` lower exact-guard slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are `aoyagiLemma5Eq5PostPLowerGuard`,
`aoyagiLemma5Eq5PostPLowerGuard_of_terminalRoom`,
`aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_iff_offset_le_intervalExcess`,
`aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_offset_le_intervalExcess`,
`aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_postPLowerGuard`,
`aoyagiLemma5Eq5_alphaDomain_and_postPRange_not_lowerGuard`, and
`aoyagiLemma5Eq5_not_postPLowerGuard_counterexample`.  This proves the exact
local Htilde interval-membership guard for a supplied post-`p` branch point
and records that strict alpha-domain membership plus post-`p` range is not
enough.  It is not Eq5 construction, source-label legality, source-backed
guard production, cutoff coverage, classifier exactness, order count, pole
order, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-exact-guard-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-postp-lower-exact-guard.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-postp-lower-exact-guard-a5.md`.

Latest A5 update: the Eq5 early/tail interval-guard slice has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are `aoyagiLemma5Eq5PreAlphaLowerGuard`,
`aoyagiLemma5Eq5AlphaToPLowerGuard`,
`aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_iff_index_le_intervalExcess`,
`aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_iff_predAlpha_le_intervalExcess`,
`aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_of_preAlphaLowerGuard`,
`aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_of_alphaToPLowerGuard`,
`aoyagiLemma5Eq5_tail_mem_intervalValueSetNat`,
`aoyagiLemma5Eq5PreAlphaLowerGuard_of_alphaDomain`, and
`aoyagiLemma5Eq5AlphaToPLowerGuard_of_alphaDomain`.  Strict alpha-domain
membership supplies the early-branch guards, but not the post-`p` guard.
This is not Eq5 construction, source-label legality, selected-span exactness,
order count, pole order, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-early-tail-interval-guards-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-early-tail-interval-guards.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-early-tail-interval-guards-a5.md`.

Latest A5 update: the Eq5 nonfirst block admissibility wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean name
is
`aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard`.
It assembles branch-local interval facts to show that a supplied Eq5 piecewise
certificate is Htilde-interval-admissible on every selected block `b` with
`1<=b`, assuming strict alpha-domain membership and the explicit post-`p`
lower guard.  The first branch is excluded and the post-`p` guard remains
supplied.  This is not Eq5 construction, source-label legality, source-backed
guard production, selected-span exactness, order count, pole order, normal
crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-admissibility-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-nonfirst-block-admissibility.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-nonfirst-block-admissibility-a5.md`.

Latest A5 update: the Eq5 post-`p` lower guard now has an exact
terminal-room characterization in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are `aoyagiLemma5Eq5PostPLowerGuard_iff_terminalRoom_of_alphaDomain` and
`aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom`.
Under strict Eq5 alpha-domain membership, the global post-`p` lower guard is
equivalent to `p+2*a-alpha<=ell`; the nonfirst-block wrapper can therefore use
that concrete inequality instead of the opaque guard.  This is finite
arithmetic for supplied Eq5 piecewise data.  It is not Eq5 construction,
source-label legality, source-backed terminal-room production, selected-span
exactness, order count, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-room-guard-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-room-guard.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-room-guard-a5.md`.

Latest A5 update: the Eq5 nonfirst block explicit-bounds wrapper has landed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved Lean names
are
`aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_postPLowerGuard` and
`aoyagiLemma5Eq5_nonfirstBlock_bounds_of_alphaDomain_of_terminalRoom`.
They unwrap the existing nonfirst interval-membership theorem into
`Htilde_b <= T S <= Htilde'_b` under the same supplied Eq5 piecewise
certificate, strict alpha-domain membership, nonfirst-block condition, and
either the explicit post-`p` lower guard or terminal-room inequality.  This is
only same-coordinate interval bookkeeping.  It is not Eq5 construction,
source-label legality, source-backed guard production, selected-span
exactness, order count, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonfirst-block-bounds-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-nonfirst-block-bounds.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-nonfirst-block-bounds-a5.md`.

Latest A5 update: the Lemma 5 equation `(5)` supplied piecewise certificate has
landed in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved
Lean names are `AoyagiLemma5Eq5PiecewiseSourceVector`,
`AoyagiLemma5Eq5SelectedSpanBranchValue`,
`aoyagiLemma5Eq5_branchValue_of_block`,
`aoyagiLemma5Eq5_selectedSpan_branchValue`, and
`aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector`.  They record
the five displayed Eq5 branch values as supplied data, classify selected-block
and selected-span points into those supplied branches, and derive the narrower
own-coordinate branch record from the full certificate.  This does not
construct equation `(5)`'s displayed vector, prove source-label legality,
terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5 order
count, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-piecewise-certificate-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-piecewise-certificate.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-piecewise-certificate-a5.md`.

Latest A5 update: the Lemma 5 equation `(5)` own-coordinate source-label bridge
has landed in `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The proved Lean names are
`aoyagiHtildeLowerIncrementPrefix_le_prefixSum_of_selectedWidth_le_pred`,
`aoyagiHtildeLowerNat_add_one_pos_any_of_sourceSelectedInequality`,
`aoyagiPrefixSum_sub_current_le_mul_pred_of_selectedWidth_le_pred`,
`aoyagiHtildeUpperNat_le_selectedWidth_of_selectedWidth_le_pred`,
`aoyagiHtildeUpperNat_le_selectedWidth_of_sourceSelectedInequality`,
`aoyagiLemma5Eq5_labelBounds_of_sourceSelectedInequality`,
`aoyagiLemma5Eq5_actualWidthLabel_of_widthCompatibility`, and
`aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel`.  They prove
`1<=Htilde'_p+1-alpha<=W_p` from Definition 3 selected-width hypotheses and
the supplied offset guard `1<=alpha<=excess(ell,a,p)`, then translate this to
`actualWidthLabel` under explicit source-layer range and actual-width
compatibility at `C.point p-1`.  A supplied Eq5 piecewise certificate also
gives `T(C.point p-1)=k-1`.  This does not construct equation `(5)`'s displayed
vector, prove arbitrary-point label legality across the whole block, terminal
`tilde t=0`, vector admissibility, chart sequence, Lemma 5 order count, normal
crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-source-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-source-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-source-label-a5.md`.

Latest A5 update: the Lemma 5 equation `(5)` source-label bridge now has an
arbitrary-own-block wrapper in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The proved Lean names are
`aoyagiLemma5Eq5_actualWidthLabel_at_of_widthCompatibility`,
`aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_block`,
`aoyagiLemma5Eq5_sourceIndex_pos_of_ownBlock`, and
`aoyagiLemma5Eq5_piecewise_ownCoordinate_actualWidthLabel_of_ownBlock_widthCompatibility`.
The
theorem takes arbitrary `S`, explicit range `1<=S<=L`, and actual-width
compatibility `n(S+1)=W_p`; with a supplied Eq5 piecewise certificate and
`C.block p S`, it proves `T(S)=k-1` and `actualWidthLabel L n S k`.  This does
not prove the width compatibility itself.  The source-shaped wrapper derives
`1<=S` from Eq5's `1<=alpha<p` guards and selected-cutpoint monotonicity, but
still keeps `S<=L` explicit.  It does not construct equation `(5)`'s displayed
vector, terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5
order count, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-block-source-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-block-source-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-block-source-label-a5.md`.

Latest A5 update: the Lemma 5 equation `(5)` source-label bridge now has a
source-range and width-bound refinement.  The selected-cutpoint helpers
`AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_terminalEndpoint_le`,
`AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_lastPoint_le`,
`AoyagiSelectedCutpoints.block_sourceIndex_le_of_terminalEndpoint_le`, and
`AoyagiSelectedCutpoints.block_sourceIndex_le_of_lastPoint_le` prove that
selected-block membership plus `C.point ell<=L+1` gives `S<=L`.  The Eq5
wrappers `aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound`,
`aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound`,
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound`,
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthCompatibility`,
and
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound`
prove the own-block value and actual label legality using the sufficient
width hypothesis `W_p<=n(S+1)`; equality `n(S+1)=W_p` remains only a special
case.  This does not prove the width bound from Definition 3, construct the
displayed vector, prove terminal `tilde t=0`, vector admissibility, chart
sequence, Lemma 5 order count, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-source-range-width-bound-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-source-range-width-bound.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-source-range-width-bound-a5.md`.

Latest A5 update: the Lemma 5 equation `(5)` width-bound hypothesis now has a
conditional block-width dominance bridge.  The selected-cutpoint helpers
`AoyagiSelectedCutpoints.block_sourceLayer_mem_Ico`,
`AoyagiSelectedCutpoints.block_sourceLayer_eq_left_or_between`,
`AoyagiSelectedCutpoints.point_ne_of_between_adjacent`,
`AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block`,
`AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min`,
`AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected`,
and
`AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt`
derive `W_p<=n(S+1)` from explicit block-local width dominance, left-endpoint
minimum data, or index-level off-selected-layer dominance.  The Eq5 wrappers
`aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_blockWidth`,
`aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_leftMin`,
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected`,
and
`aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected_lt`
combine this with the previous source-range wrapper.  This is not a
Definition 3 consequence: the source review records that Definition 3's
non-selected condition is value-level and does not control unselected layers
with duplicate selected width values.  It also does not construct the
displayed vector, prove terminal `tilde t=0`, vector admissibility, chart
sequence, Lemma 5 order count, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-block-width-dominance-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-block-width-dominance.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-block-width-dominance-a5.md`.

Latest A5 update: the duplicate-width obstruction behind the equation `(5)`
width-bound caveat is now Lean-proved as
`aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The closed witness
uses selected cutpoints `1,3,5,7`, selected widths `1,2,2,2`, actual widths
matching those values at the selected cutpoints, and an off-selected layer
`6` of actual width `1`.  It satisfies the selected-width sum, the strict
selected inequalities, and the value-level non-selected-width condition, but
fails the Eq5 bound `W_p<=n(S+1)` for `p=2`, `S=5`.  This theorem is a
guardrail for the existing conditional bridges, not a construction theorem.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-width-bound-counterexample-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-width-bound-counterexample.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-width-bound-counterexample-a5.md`.

Latest A5 update: Eq5 now has a finite count decomposition in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The proved names are
`aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator` and
`aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min`.  They prove
that the same-coordinate interval excess equals the Eq5 strict-offset
value-set count plus one rising-coordinate indicator, and that the lower
endpoint is not in the strict-offset set when `p<=a` and `p<=ell-a`.  This is
only order-count scaffolding; it does not realise the extra value by equations
`(3)` or `(4)`, construct source vectors, prove terminality, or prove Lemma 5.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-offset-excess-decomposition-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-offset-excess-decomposition.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-offset-excess-decomposition-a5.md`.

Latest A5 update: Eq3/Eq4 own-coordinate actual-label adapters are proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_widthCompatibility`
and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_sourceSelected_slack`.
They combine supplied-piecewise own-coordinate values with existing
actual-label bridges, giving `T(S)=k-1` and `actualWidthLabel L n S k` in one
conclusion.  The companion names
`aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint` and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint` derive
the upper source range from `C.point ell<=L+1`.  Eq3 still requires the
explicit slack; none of these theorems constructs the displayed vector or
proves terminality.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-own-coordinate-actual-label-adapters-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-own-coordinate-actual-label-adapters.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-own-coordinate-actual-label-adapters-a5.md`.

Latest A5 update: Eq5 interval/introduced-label wrappers are proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean` and
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt`,
`aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min`,
`aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min`,
`aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min`,
and
`aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound`.
The finite-set wrappers say that, in the rising region, inserting the lower
endpoint into the strict Eq5 offset-value set gives a subset of the
same-coordinate interval with cardinality equal to the interval excess and one
less than the full interval.  The source-label wrapper combines supplied Eq5
own-block interval membership, `T S=k-1`, and post-advance introduced-label
membership.  The actual-width lower bound remains explicit; no displayed
vector construction, terminality, admissibility, or order count is proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-interval-introduced-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-interval-introduced-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-interval-introduced-label-a5.md`.

Latest A5 update: Eq3/Eq4 own-coordinate introduced-label wrappers are proved
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint` and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint`.
They combine the existing last-point actual-label adapters with the generic
post-advance rule `introducedLabel_of_eq_stage_le`, giving `T S=k-1` and
`introducedLabel L n S k S k` at the own coordinate.  Actual-width
compatibility remains explicit, and Eq3 still requires the one-unit slack.
No displayed vector construction, terminality, admissibility, or order count
is proved.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-own-coordinate-introduced-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-own-coordinate-introduced-label.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-own-coordinate-introduced-label-a5.md`.

Latest A5 update: Eq5 now has the exact rising-region erase-upper finite-set
equality in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The names
are `aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt`,
`aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min`,
and
`aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min`.
They prove that, under `1<=p`, `p<=a`, and `p<=ell-a`, the lower endpoint
inserted into the strict Eq5 offset-value set is exactly the same-coordinate
interval value set with the upper endpoint erased.  The upper endpoint is
excluded because the interval gap is `p>=1` and strict Eq5 offsets have
`alpha>=1`, so reaching the upper endpoint would require `alpha=0`.  This is
finite count bookkeeping only, not a claim that equations `(3)` or `(4)`
realise the erased endpoint and not a displayed-vector, terminality,
admissibility, order-count, normal-crossing, or RLCT theorem.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-interval-erase-upper-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-interval-erase-upper.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-interval-erase-upper-a5.md`.

Latest A5 update: the Eq3/Eq4/Eq5 introduced-label wrappers now have
finite-domain adapters in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.
The names are
`aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`,
`aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint`,
and
`aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound`.
They keep the corresponding introduced-label hypotheses and convert
`introducedLabel L n S k S k` into
`Sigma.mk S k ∈ introducedLabelFinset L n S k` via
`mem_introducedLabelFinset.mpr`.  They do not assert terminal exponents,
least values, `LabelExponentCertificate`, displayed-vector construction,
terminality, admissibility, order count, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-introduced-label-finset-adapters-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-introduced-label-finset-adapters.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-introduced-label-finset-adapters-a5.md`.

Latest A5 update: the source-displayed interval-size profile from Aoyagi
Lemma 5 is now Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`.  The names are
`aoyagiLemma5IntervalSize_eq_succ_of_le_min`,
`aoyagiLemma5IntervalSize_eq_min_succ_of_min_le_of_le_max`,
`aoyagiLemma5IntervalSize_eq_falling_of_max_le`, and
`aoyagiLemma5IntervalSize_sourcePiecewise`.  They prove the rising, plateau,
and falling formulas for `aoyagiLemma5IntervalSize ell a j` using only the
closed excess formula `min(j,ell-j,a,ell-a)`.  This is finite interval
arithmetic, not displayed-vector construction, value realisation, terminality,
admissibility, order-count, normal-crossing, or RLCT data.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-interval-size-profile-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-interval-size-profile.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-interval-size-profile-a5.md`.

Latest A5 update: Eq5 now has a strict-offset finite-domain adapter in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The name is
`aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound`.
It combines the supplied own-coordinate offset membership theorem with the
existing interval/finite-domain introduced-label wrapper, proving for one
supplied branch that `T S` belongs to `aoyagiLemma5Eq5OffsetValueSet`, belongs
to the same-coordinate interval, equals `k-1`, and has
`Sigma.mk S k ∈ introducedLabelFinset L n S k`.  This is one-alpha supplied
API scaffolding only, not displayed-vector construction, terminality,
admissibility, order-count, normal-crossing, or RLCT data.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-offset-finset-adapter-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-offset-finset-adapter.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-offset-finset-adapter-a5.md`.

Latest A5 update: Eq4 now has a lower-endpoint wrapper for the Eq5
erase-upper finite-set equality in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The name is
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min`.
It uses the supplied Eq4 own-coordinate value theorem to rewrite
`T(C.point p-1)` to `Htilde_p`, then applies the existing Eq5 set equality
identifying `insert Htilde_p Eq5OffsetValueSet_p` with the same-coordinate
interval after erasing the upper endpoint.  It is conditional on supplied Eq4
piecewise data and rising-region hypotheses, and it does not construct
vectors, realise the erased upper endpoint, prove terminality, admissibility,
order count, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-lower-endpoint-eq5-erase-upper-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-lower-endpoint-eq5-erase-upper.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-lower-endpoint-eq5-erase-upper-a5.md`.

Latest A5 update: Eq5 strict offsets are now isolated as the same-coordinate
interval with both endpoints erased in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The name is
`aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`.  It erases
the lower endpoint from the existing lower-plus-offset erase-upper equality,
using the existing proof that the lower endpoint is not a strict Eq5 offset.
This is finite-set normalization only; it does not realise Eq3/Eq4 endpoints,
construct displayed vectors, prove terminality, admissibility, order count,
normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-offsets-erase-endpoints-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-offsets-erase-endpoints.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-offsets-erase-endpoints-a5.md`.

Latest A5 update: Eq3/Eq4 supplied own-coordinate branches now have
interval-membership plus finite-domain introduced-label adapters in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`
and
`aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint`.
They combine already-proved endpoint interval membership with the existing
`introducedLabelFinset` adapters.  Eq3's explicit slack and Eq4's repaired
guards remain explicit.  No terminal exponent, least-value, displayed-vector
construction, admissibility, order count, normal-crossing, or RLCT data is
proved.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-interval-finset-adapters-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-interval-finset-adapters.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-interval-finset-adapters-a5.md`.

Latest A5 update: Eq5 now has a one-step introduced-domain insert wrapper in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The name is
`aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_succ_eq_insert_of_lastPoint_widthBound`.
For one supplied Eq5 own-block branch whose label is `J+1`, it proves
`introducedLabelFinset L n S (J+1) =
insert (Sigma.mk S (J+1)) (introducedLabelFinset L n S J)`, using the existing
Eq5 actual-label wrapper and the generic finite-domain insert theorem.  It is
finite-domain bookkeeping only; no terminal exponent, least-value,
displayed-vector construction, admissibility, order count, normal-crossing, or
RLCT data is proved.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-domain-insert-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-domain-insert.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-domain-insert-a5.md`.

Latest A5 update: Eq5 now has the corresponding one-step finite-domain
cardinality wrapper.  The generic theorem
`introducedLabelFinset_card_succ_eq_succ` in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` proves that a one-step
current-layer advance increases `introducedLabelFinset` cardinality by one
when the new current-layer label is actual.  The source-facing Eq5 theorem
`aoyagiLemma5Eq5_ownBlock_introducedLabelFinset_card_succ_eq_succ_of_lastPoint_widthBound`
uses the existing Eq5 actual-label wrapper to apply this generic theorem to
one supplied branch label `J+1 = Htilde'_p+1-alpha`.  This is finite-domain
cardinality bookkeeping only; no terminal exponent, least-value,
displayed-vector construction, admissibility, order count, normal-crossing, or
RLCT data is proved.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-domain-card-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-domain-card.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-domain-card-a5.md`.

Latest A5 update: Eq5 now has a one-branch adapter from strict-offset
membership to membership in the same-coordinate interval with both endpoints
erased.  The theorem
`aoyagiLemma5Eq5_ownBlock_eraseEndpoints_mem_introducedLabelFinset_of_lastPoint_widthBound`
in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean` uses the existing
strict-offset finite-domain adapter and the finite-set equality
`aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min`.  It is
conditional on the rising-region guards and supplied Eq5 branch data.  It does
not package all Eq5 branches, realise endpoints by Eq3/Eq4, construct
displayed vectors, prove admissibility, order count, normal-crossing, or RLCT
data.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-interval-erase-endpoints-finset-adapter-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-interval-erase-endpoints-finset-adapter.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-interval-erase-endpoints-finset-adapter-a5.md`.

Latest A5 update: Eq3/Eq4 now have one-step introduced-domain insert and
cardinality wrappers for supplied endpoint branches in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq4_ownCoordinateFinset_succ_eq_insert_of_lastPoint`,
`aoyagiLemma5Eq4_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`,
`aoyagiLemma5Eq3_ownCoordinateFinset_succ_eq_insert_of_lastPoint`, and
`aoyagiLemma5Eq3_ownCoordinateFinset_card_succ_eq_succ_of_lastPoint`.  They
use the existing Eq3/Eq4 actual-label wrappers and the generic one-step
finite-domain insert/cardinality theorems.  Eq4's repaired guards and Eq3's
explicit slack remain in the hypotheses.  No displayed-vector construction,
admissibility, order count, normal-crossing, or RLCT data is proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-domain-insert-card-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-domain-insert-card.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-domain-insert-card-a5.md`.

Latest A5 update: Eq5 now has a source-facing Case 2 recurrence-weight update
wrapper in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The name is
`aoyagiLemma5Eq5_ownBlock_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_widthBound`.
It uses the existing Eq5 actual-label wrapper and the generic supplied
post-data recurrence theorem to prove `post.weight i = u * pre.weight i` for
all `i` with `J+1 <= i`, for one supplied Eq5 branch.  It is conditional on a
supplied `Case2SuppliedPostData` package and does not assert that a blow-up
chart produces the post-state.  No displayed-vector construction,
admissibility, order count, normal-crossing, or RLCT data is proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-case2-weight-update-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-case2-weight-update.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-case2-weight-update-a5.md`.

Latest A5 update: Eq3/Eq4 now have source-facing Case 2 recurrence-weight
update wrappers in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The
names are
`aoyagiLemma5Eq4_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`
and
`aoyagiLemma5Eq3_ownCoordinate_case2_weight_succ_current_eq_newVar_mul_of_lastPoint`.
They use the existing Eq3/Eq4 actual-label wrappers and the generic supplied
post-data recurrence theorem to prove `post.weight i = u * pre.weight i` for
all `i` with `J+1 <= i`, for one supplied endpoint branch.  Eq4's repaired
guards, Eq3's explicit slack, actual-width compatibility, and supplied
`Case2SuppliedPostData` remain explicit.  They do not assert that a chart
produces the post-state.  No displayed-vector construction, admissibility,
order count, normal-crossing, or RLCT data is proved.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-case2-weight-update-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-case2-weight-update.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-case2-weight-update-a5.md`.

Latest A5 update: Eq3/Eq4/Eq5 now have source-facing supplied
exponent-domain extension wrappers in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq4_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`,
`aoyagiLemma5Eq3_ownCoordinate_extendExponentDomain_succ_current_of_lastPoint`,
and
`aoyagiLemma5Eq5_ownBlock_extendExponentDomain_succ_current_of_lastPoint_widthBound`.
They use the existing source-label wrappers only to supply the new label's
`introducedLabel` field at state `(S,J+1)`.  The terminal-exponent equality
and least-value proof for the new label remain explicit hypotheses.  The
generic theorem
`IntroducedLabelExponentCertificates.extendDomain_succ_current` then extends
the all-introduced-label exponent-certificate family.  No terminal-exponent
formula, least-value calculation, displayed-vector construction,
admissibility, order count, normal-crossing, or RLCT data is proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-exponent-domain-extension-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-exponent-domain-extension.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-supplied-exponent-domain-extension-a5.md`.

Latest A5 update: the first same-coordinate interval now has supplied-shaped
finite-set coverage in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.
The name is
`aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat`.
It combines the existing Eq4/Eq5 erase-upper equality with a separately
supplied Eq3-shaped own-coordinate upper endpoint to prove that this upper
endpoint, the supplied Eq4 lower endpoint, and the strict Eq5 offset set equal
the full first interval.  The printed equation `(3)` excludes
`(S_2-1,Htilde'_1+1)`, so the upper endpoint is not claimed to be supplied by
the printed Eq3 branch.  This is first-interval finite-set bookkeeping only.
It does not construct displayed vectors, prove source-label legality, cover
all intervals, package all branches, prove order count, normal crossings, or
RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-first-interval-supplied-shaped-coverage-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-first-interval-supplied-shaped-coverage.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-first-interval-supplied-shaped-coverage-a5.md`.

Latest A5 update: one-interval coverage now has a p-general supplied-upper
finite-set wrapper in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.
The name is
`aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min`.
It combines the existing Eq4/Eq5 erase-upper equality with an explicitly
supplied upper endpoint equality to prove that the upper endpoint, supplied
Eq4 lower endpoint, and strict Eq5 offset set equal the full interval at
coordinate `p`.  This is not a printed Eq3 claim; the upper endpoint equality
is an input.  This is one-interval finite-set bookkeeping only.  It does not
construct displayed vectors, prove source-label legality, cover all intervals,
package all branches, prove order count, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-upper-eq4-interval-coverage-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-upper-eq4-interval-coverage.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-supplied-upper-eq4-interval-coverage-a5.md`.

Latest A5 update: the supplied-upper finite-set wrapper now has an Eq3-shaped
component instantiation in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.
The names are
`aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap` and
`aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat`.
The first theorem reads the supplied Eq3-shaped upper branch as a component
value on selected block `p`; the second combines it with the supplied Eq4 lower
endpoint and strict Eq5 offsets to fill one interval.  No source-label
legality, introduced-label status, all-interval coverage, all-branch packaging,
order count, normal crossings, or RLCT extraction is proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-shaped-component-interval-coverage-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-shaped-component-interval-coverage.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-shaped-component-interval-coverage-a5.md`.

Latest A5 update: the Eq3-shaped p-general component now has supplied-bound
source-label wrappers in `lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.
The names are
`aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds`,
and
`aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds`.
They package the component value as an actual source label and finite
introduced-label member only under supplied actual-width compatibility and
supplied label bounds.  They do not derive p-general Eq3 label legality from
Definition 3 and do not construct displayed vectors, prove all-interval/all-
branch coverage, order count, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-shaped-component-supplied-label-bounds-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-shaped-component-supplied-label-bounds.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-shaped-component-supplied-label-bounds-a5.md`.

Latest A5 update: the supplied-bound Eq3 component now has one-step
introduced-domain, recurrence-weight, and exponent-domain wrappers in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean`.  The names are
`aoyagiLemma5Eq3_componentFinset_succ_eq_insert_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_componentFinset_card_succ_eq_succ_of_lastPoint_labelBounds`,
`aoyagiLemma5Eq3_component_case2_weight_succ_current_eq_newVar_mul_of_lastPoint_labelBounds`,
and
`aoyagiLemma5Eq3_component_extendExponentDomain_succ_current_of_lastPoint_labelBounds`.
They use the supplied actual-label wrapper to specialize generic APIs.  The
exponent wrapper still supplies terminal-exponent equality and least-value data
explicitly.  No derivation of p-general Eq3 label bounds from Definition 3,
displayed-vector construction, chart production, all-interval/all-branch
coverage, order count, normal crossings, or RLCT extraction is proved.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-component-domain-recurrence-exponent-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-component-domain-recurrence-exponent.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-component-domain-recurrence-exponent-a5.md`.

Latest A5 update: the strict Eq5 offset-value set has a rising-region
cardinality specialization in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The theorem
`aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min` proves that under
`1<=p`, `p<=a`, and `p<=ell-a`, the set has cardinality `p-1`.  This is a
one-coordinate finite count theorem only; it does not construct Eq5 displayed
vectors, prove source-label legality, realise endpoints, aggregate all
coordinates, package all branches, or prove Lemma 5 order count.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-strict-offset-rising-count-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-strict-offset-rising-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq5-strict-offset-rising-count-a5.md`.

Latest A5 update: Eq4 lower plus Eq5 strict offsets now has a source-facing
cardinality wrapper in `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.
The theorem
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min`
proves that a supplied Eq4 lower own-coordinate value adds one value to the
strict Eq5 offset set in the rising region.  It is a one-coordinate finite
count theorem only; it does not prove source-label legality, displayed-vector
construction, upper endpoint realisation, all-coordinate/all-branch coverage,
or Lemma 5 order count.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-lower-plus-eq5-offset-count-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-lower-plus-eq5-offset-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-lower-plus-eq5-offset-count-a5.md`.

Latest A5 update: the supplied Eq3-shaped component plus Eq4 lower endpoint
coverage now has cardinality wrappers in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  The names are
`aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize`
and
`aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two`.
They prove one-coordinate interval-size cardinality and strict Eq5
offset-cardinality plus two under the rising-region guards.  They do not prove
source-label legality, displayed-vector construction, all-coordinate/all-branch
coverage, or Lemma 5 order count.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-interval-cardinality-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-interval-cardinality.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-interval-cardinality-a5.md`.

Latest A5 source reconstruction: the remaining source-backed Lemma 5
chart-family gap is recorded at
`threads/05-arithmetic-tail/reproduction-lemma5-source-chart-family-reconstruction-a5.md`.
It identifies the missing obligations before any order-count theorem can be
source-backed: legal labels, vectorwise chain bounds, Lemma 4 increment tests,
Case 1(2) chart sequence, terminal `tilde t=0`, and
nonduplication/coverage.  Status: source reconstruction draft; not a Lean
target yet.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-source-chart-family-reconstruction-a5.md`.

Latest A5 source obstruction: equations `(3)`, `(4)`, and `(5)` in Aoyagi
Lemma 5 have been checked against Lemma 4's witness requirements in
`threads/05-arithmetic-tail/reproduction-lemma5-printed-equations-lemma4-obstructions-a5.md`.
Equation `(3)` exceeds the upper chain at its special endpoint; equation `(4)`
has a special-line increment `W_(q+1)-1`, hence at most `M-2`; equation `(5)`
needs extra guards beyond the printed ones.  Lean now records the Eq5
conditional lower-bound obstruction:
`aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour` and
`aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour` in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  This is an obstruction
checkpoint, not a replacement proof or final theorem.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-printed-lower-bound-obstruction.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-printed-equations-lemma4-obstructions-a5.md`.

Latest A5 Lean increment obstruction: the finite supplied-chain increment
pieces behind the printed-equation obstruction are proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  Names:
`aoyagiLemma5Eq3_specialNextIncrement_eq_succ`,
`aoyagiLemma5Eq3_specialNextIncrement_not_twoValue`,
`aoyagiLemma5Eq4_specialIncrement_eq_selectedWidth_sub_one`,
`aoyagiLemma5Eq4_specialIncrement_lt_pred_of_sourceSelected`, and
`aoyagiLemma5Eq4_specialIncrement_not_twoValue_of_sourceSelected`.
These state only conditional finite consequences of supplied adjacent
`H`-values; no displayed-vector construction or corrected formula is proved.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-printed-increment-obstructions.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-printed-increment-obstructions-a5.md`.

Latest A5 supplied-boundary update: after checking that corrected Lemma 5
formulas are not recoverable from the PDF alone, the supplied chart-family
count boundary is Lean-proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  Names:
`AoyagiLemma5SuppliedNonbaseFamily`,
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily`,
`aoyagiLemma5SuppliedNonbaseFamily_branch_card_eq_interval_card_sub_one`,
`aoyagiLemma5SuppliedNonbaseFamily_count`,
`aoyagiLemma5SuppliedNonbaseFamily_biUnion_count`, and
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_twoValueCount`.
The nonbase family requires supplied base-value membership, injective coverage
of each interval with the base erased, and cross-coordinate disjointness for
the union count.  The admissible nonbase extension requires explicit Lemma 4
chain obligations for each branch.  This is not a source-backed construction
from printed equations `(3)`, `(4)`, or `(5)`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-chart-family-count-boundary-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-chart-family-count-boundary.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-supplied-chart-family-count-boundary-a5.md`.

Latest A5 full supplied-family update: the leading base contribution in the
supplied count is now represented by an explicit branch tag in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  Names:
`AoyagiLemma5SuppliedNonbaseFamily.fullBranches`,
`AoyagiLemma5SuppliedNonbaseFamily.none_mem_fullBranches`,
`AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_of_mem`,
`AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card`,
`AoyagiLemma5SuppliedAdmissibleFamily`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranches`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card`, and
`AoyagiLemma5SuppliedAdmissibleFamily.base_twoValueCount`.  The full branch
set is `{none} union union_j {some b : b in branches j}`; its count uses
`Option.some` injectivity, disjointness from `none`, and the inherited supplied
nonbase disjointness.  The full admissible structure adds only supplied base
Lemma 4 fields.  This is not a source-backed construction from printed
equations `(3)`, `(4)`, or `(5)`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-full-supplied-family-base-branch-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-full-supplied-family-base-branch.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-full-supplied-family-base-branch-a5.md`.

Latest A5 full-branch admissibility update: the supplied full family now has a
single branchwise Lemma 4 wrapper in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  Names:
`AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullH`, and
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_twoValueCount`.  The
membership theorem extracts the nonbase coordinate witness from a tagged
`some` branch; `fullH` dispatches between supplied `baseH` and inherited
nonbase `H`; and the count theorem applies the existing Lemma 4 bridge to
every tagged branch under explicit selected-width hypotheses.  This is not a
source-backed construction from printed equations `(3)`, `(4)`, or `(5)`.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-full-supplied-family-branchwise-admissibility-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-full-supplied-family-branchwise-admissibility.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-full-supplied-family-branchwise-admissibility-a5.md`.

Latest A5 supplied-family terminal chain update: branchwise terminal chain
zero is now packaged in `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.
For admissible supplied families, the new names
`AoyagiLemma5SuppliedAdmissibleNonbaseFamily.branch_terminalH_zero`,
`AoyagiLemma5SuppliedAdmissibleFamily.base_terminalH_zero`, and
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalH_zero` apply the
existing `Htilde` terminal squeeze under `a<=ell` and the selected-width sum.
For binary supplied families,
`AoyagiLemma5SuppliedBinaryNonbaseFamily.branch_terminalH_zero`,
`AoyagiLemma5SuppliedBinaryFamily.base_terminalH_zero`, and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalH_zero` dispatch to the
supplied `Hlast`/`baseHlast` fields.  This is chain-coordinate endpoint data,
not the source-coordinate terminal equality `T(C.point ell-1)=0` needed by the
terminal Eq5 finite-set wrapper.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-family-terminal-chain-zero-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-family-terminal-chain-zero.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-supplied-family-terminal-chain-zero-a5.md`.

Latest A5 Eq4 local lower-endpoint update: the Eq4 lower endpoint has a
source-legality-free wrapper in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`.  Names:
`aoyagiLemma5Eq4_piecewise_ownCoordinate_lowerEndpoint_of_le_min`,
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_piecewise`,
`aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_piecewise`,
`aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_piecewise`,
and
`aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat`.
The first theorem uses the supplied Eq4 piecewise certificate, `1<=p`, and
`p<=ell-a`; the certificate's repaired guard supplies `p+1<=a`.  The wrappers
then fill Eq5's lower endpoint deficit, and with a separately supplied upper
endpoint fill the same-coordinate interval.  They do not prove source-label
legality, Eq4 existence at `p=a`, terminal-collision compatibility when
`p+1=a`, or all-coordinate branch-family coverage.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-local-lower-endpoint-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-local-lower-endpoint.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-eq4-local-lower-endpoint-a5.md`.

Latest A5 terminal source-realisation bridge update: a new module
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean` connects supplied
branch-chain terminal zero to the terminal Eq5 finite-set wrapper under an
explicit source-realisation hypothesis.  Names:
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_Eq5Coverage`
and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_Eq5Coverage`.
Both require a tagged branch `x in fullBranches` and
`T(C.point ell-1)=fullH x (Fin.last ell)`.  They do not construct that source
equality, source labels, terminal minimizer exactness, or no-extra coverage.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-bridge-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-bridge.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-bridge-a5.md`.

Latest A5 free-count minimum update: the supplied full family now has a
branchwise Lemma 3 numerator consequence in
`lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  Names:
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount`
and
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCount_lemma3A_eq_min`.
The first theorem bundles the supplied family count with the per-tagged-branch
Lemma 4 two-value count.  The second theorem applies the existing Lemma 4
free-count bridge with total increment length `n+1`, so the free count over
the first `n` increments attains Aoyagi Lemma 3's isolated numerator minimum.
This does not identify the numerator with a source terminal exponent or
`lambda`, prove terminal `tilde t=0`, construct source labels or displayed
vectors, prove chart coverage, or prove pole order/RLCT data.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-full-supplied-family-free-count-minimum-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-full-supplied-family-free-count-minimum.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-full-supplied-family-free-count-minimum-a5.md`.

Latest A5 terminal-numerator bridge update: the supplied branch minimum now
connects to the generic terminal-exponent certificate API in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.  Names:
`aoyagiLemma4FreeHighCount`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin`, and
`IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator`.
The bridge assumes the introduced-label numerator has been supplied to equal
the Lemma 3 free-count expression for a tagged supplied Lemma 5 branch, and
then proves the corresponding `terminalExponent` equals the isolated Lemma 3
minimum numerator.  This keeps source-label realisation, terminal
`tilde t=0`, and terminal-exponent normalisation supplied; it does not prove
`lambda`, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-numerator-bridge-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-numerator-bridge.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-numerator-bridge-a5.md`.

Latest A5 supplied-terminal-candidate update: the terminal bridge file now
defines `AoyagiLemma5SuppliedTerminalCandidateFamily`.  Names:
`AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.fullBranches_card`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalLeastValue_zero`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalExponent_eq_minNumerator`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branch_terminalCandidateData`.
The structure supplies branch-to-label maps, introduced-label proofs,
terminal least-value-zero proofs, and numerator normalisation for every tagged
branch.  The theorems package those supplied fields with the existing branch
minimum theorem.  This is not label construction from equations `(3)`, `(4)`,
or `(5)`, not no-extra-minimizer data, and not a pole-order/RLCT theorem.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-supplied-terminal-candidate-family-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-supplied-terminal-candidate-family.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-supplied-terminal-candidate-family-a5.md`.

Latest A5 branch-label-image update: the terminal bridge file now defines
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel` and
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage`, using the
same dependent-pair label type as `introducedLabelFinset`.
`branchLabel_mem_introducedLabelFinset` and
`branchLabelImage_subset_introducedLabelFinset` place the supplied labels in
the existing finite introduced-label set.  Under an explicit injectivity
hypothesis on `fullBranches`,
`branchLabelImage_card_eq_fullBranches_card_of_injOn` proves the image has the
same cardinality as the tagged branch set, and `branchLabelImage_card`
combines that with the supplied Lemma 5 branch count to get
`a*(n+1-a)+1`.  `branchLabelImage_terminalCandidateData` transfers the
branchwise introduced-label, least-value-zero, and terminal-exponent data to
any label in the image.  This is not source-backed label injectivity,
no-extra-minimizer coverage, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-branch-label-image-count-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-branch-label-image-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-branch-label-image-count-a5.md`.

Latest A5 terminal-minimum-label update: the terminal bridge file now defines
`aoyagiLemma5MinNumerator` and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels`, the finite
introduced-label set with `leastValue=0` and terminal exponent equal to the
supplied Lemma 5 minimum numerator.  Names:
`mem_terminalMinimumLabels`,
`branchLabelImage_subset_terminalMinimumLabels`, and
`terminalMinimumLabels_card_of_noExtra`.  The image inclusion is proved from
the supplied branchwise terminal-candidate data.  The exact cardinality theorem
assumes the reverse no-extra containment and branch-label injectivity.  This is
not a source-backed no-extra-minimizer theorem, pole order, normal crossings,
or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-label-count-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-label-count.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-label-count-a5.md`.

Latest A5 exactness-package update: the terminal bridge now defines
`AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumLabelExactness`,
with fields for branch-label injectivity on `fullBranches` and no-extra
containment `terminalMinimumLabels subset branchLabelImage`.  The theorem
`terminalMinimumLabels_eq_branchLabelImage_of_exactness` derives the finite
equality, and `terminalMinimumLabels_card_of_exactness` derives the finite
exact-minimum label count from this package.  This is only a supplied finite
exactness wrapper, not source-backed exactness, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-label-exactness-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-label-exactness.md`.
Review artifact:
`threads/05-arithmetic-tail/review-lemma5-terminal-minimum-label-exactness-a5.md`.

Current A5 source frontier: a source audit of Aoyagi Lemma 5's upper-bound
paragraph records that Aoyagi asserts an upper count of lambda-vectors by
counted interval data, but a source-backed classifier has not yet been
reproduced and the paragraph does not yet prove Lean's no-extra containment
`terminalMinimumLabels subset branchLabelImage`.  Missing bridges:
label-to-vector, minimum-to-lambda, interval classifier, Case 1(2)
uniqueness/injection, and back-to-label.  Until these are reproduced or
explicitly supplied, terminal exactness stays a supplied boundary.
Audit:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-exactness-source-audit-a5.md`.
Boundary card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-exactness-source-frontier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-frontier-and-bijon-a5.md`.

Latest A5 bijection-API update: the terminal bridge exposes supplied
terminal-minimum exactness as a standard finite bijection.  Names:
`branchLabel_bijOn_terminalMinimumLabels_of_exactness`,
`terminalMinimumLabelExactness_of_branchLabel_bijOn`, and
`terminalMinimumLabels_card_of_branchLabel_bijOn`.  These prove exactness
implies `Set.BijOn branchLabel fullBranches terminalMinimumLabels`, a supplied
bijection implies the exactness fields, and a supplied bijection gives the
finite count.  This is not a source-backed bijection construction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-label-bijon-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-label-bijon.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-exactness-frontier-and-bijon-a5.md`.

Latest A5 classifier-interface update: the terminal bridge now names the
upper-bound/no-extra direction independently as supplied classifier data.
Names:
`UpperBoundClassifier`,
`terminalMinimumLabels_subset_branchLabelImage_of_upperBoundClassifier`,
`terminalMinimumLabels_card_le_branchLabelImage_card_of_upperBoundClassifier`,
`terminalMinimumLabels_card_le_of_upperBoundClassifier`, and
`terminalMinimumLabelExactness_of_upperBoundClassifier`.  The classifier
produces a supplied branch for every terminal-minimum label; Lean derives the
containment, the finite upper cardinal inequality without branch-label
injectivity, and exactness packaging when injectivity is supplied.  This is
not a source-backed classifier and does not discharge the label-to-vector,
minimum-to-lambda, interval classifier, Case 1(2) uniqueness, or back-to-label
bridges.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-interface-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-upper-bound-classifier-interface.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-upper-bound-classifier-interface-a5.md`.

Latest A5 counted-datum update: `Lemma5SuppliedFamily.lean` now contains a
label-free finite codomain for the Lemma 5 upper-bound interval count.  Names:
`AoyagiLemma5CountDatum`, `aoyagiLemma5CountDatumNonbaseSet`,
`aoyagiLemma5CountDatumSet`, `none_mem_aoyagiLemma5CountDatumSet`,
`some_mem_aoyagiLemma5CountDatumSet_iff`,
`aoyagiLemma5CountDatumNonbaseSet_card`, and
`aoyagiLemma5CountDatumSet_card`.  With supplied base-value membership in each
interior same-coordinate interval, Lean proves this codomain has cardinality
`a*(ell-a)+1`.  It does not prove a source classifier, Case 1(2) uniqueness,
back-to-label coverage, terminal-label exactness, pole order, normal
crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-set-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-set.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-set-a5.md`.

Latest A5 counted-datum-classifier update: `Lemma5SuppliedFamily.lean` now
also packages the source-facing upper-bound classifier as supplied finite
data.  Names:
`AoyagiLemma5CountDatumClassifier`,
`AoyagiLemma5CountDatumClassifier.image_subset_countDatumSet`, and
`AoyagiLemma5CountDatumClassifier.candidates_card_le`.  A finite candidate set
whose classifier maps into the counted datum set injectively has cardinality
at most `a*(ell-a)+1`.  The source candidate set, source classifier, Case 1(2)
nonduplication, and back-to-label map remain unproved boundaries.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-classifier-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-classifier-a5.md`.

Latest A5 counted-datum maps-to adapter update: `Lemma5SuppliedFamily.lean`
now also exposes `aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat` and
`aoyagiLemma5CountDatumSet_mem_of_HtildeBounds`.  At an interior coordinate,
interval membership plus non-base-value inequality, or explicit Htilde bounds
plus non-base-value inequality, gives membership of `some (j,H)` in the
counted-datum codomain.  This is only the maps-to/codomain-membership adapter;
it does not construct source branches, classifiers, injections, back-to-label
maps, terminal exactness, order counts, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-maps-to-adapters-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-maps-to-adapters.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-maps-to-adapters-a5.md`.

Latest A5 Eq5 counted-datum bridge update: `Lemma5Eq5CountDatumBridge.lean`
now contains
`aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard`
and
`aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom`.
For a supplied Eq5 piecewise vector, strict alpha-domain membership, nonfirst
block data, and a supplied non-base-value inequality, the branch value `T S`
belongs to the counted-datum codomain.  The two variants use either the
explicit post-`p` guard or terminal-room inequality.  This is only a maps-to
bridge; it does not construct Eq5 vectors, produce nonbase status, construct
classifiers, prove injections, back-to-label coverage, order counts, pole
order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-counted-datum-bridge-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-counted-datum-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-counted-datum-bridge-a5.md`.

Latest A5 Eq5 endpoint counted-datum bridge update:
`Lemma5Eq5CountDatumBridge.lean` now contains
`aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom` and
`aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom`.  For a
supplied Eq5 terminal-room endpoint chain, an interior selected coordinate,
and a supplied nonbase inequality, the chain value `H_j` and the source-facing
endpoint value `T(C.point j - 1)` belong to the counted-datum codomain.  This
uses the Eq5 binary-prefix-delta theorem and the existing terminal-binary
counted-datum maps-to theorem.  It is not Eq5 vector construction, endpoint
realisation, nonbase production, classifier construction, injection,
back-to-label coverage, order count, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-counted-datum-bridge.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-counted-datum-bridge-a5.md`.

Latest A5 Lemma 4 prefix-profile computation update:
`HtildeChainArithmetic.lean` now contains
`aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub` and
`aoyagiLemma4IncrementPrefix_eq_lowerHighCount_of_eq_lowerNat`.  These prove
the generic coordinate algebra for the Lemma 4 prefix normal form: upper
Htilde minus offset `r` gives `upperHighCount+r`, and lower Htilde gives
`lowerHighCount`.  This is a prerequisite-style computation for a later Eq5
endpoint-profile proof, not a binary-delta theorem, two-value increment
theorem, Eq5 construction, endpoint realisation, order count, pole order,
normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma4-prefix-profile-computations-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma4-prefix-profile-computations.md`.
Review:
`threads/05-arithmetic-tail/review-lemma4-prefix-profile-computations-a5.md`.

Latest A5 Eq5 endpoint-prefix profile update:
`Lemma5Eq5EndpointProfile.lean` now contains
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha`,
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP`,
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP`, and
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail`.  For a supplied Eq5
piecewise vector and supplied endpoint-chain correspondence, the endpoint
prefix values are respectively `b`, `alpha-1`, `alpha+b-p`, and `a`; the
alpha-to-`p` and post-`p` profiles also assume terminal-room.  This is
branchwise arithmetic only, not a binary-delta theorem, two-value increment
theorem, Eq5 construction, endpoint realisation, order count, pole order,
normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-prefix-profile-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-prefix-profile.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-prefix-profile-a5.md`.

Latest A5 Eq5 binary-prefix-delta update:
`Lemma5Eq5EndpointProfile.lean` now contains
`aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom` and
`aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom`.
For a supplied Eq5 piecewise vector, supplied endpoint-chain correspondence,
source endpoint, terminal endpoint, selected-width sum, and terminal room, the
successive Lemma 4 increment-prefix deltas are all `0` or `1`.  This is the
adjacent endpoint-profile calculation only, not Eq5 vector construction,
endpoint realisation, terminality, classifier data, order count, pole order,
normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-binary-prefix-delta-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-binary-prefix-delta.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-binary-prefix-delta-a5.md`.

Latest A5 Eq5 two-value-wrapper update:
`Lemma5Eq5EndpointProfile.lean` now contains
`aoyagiLemma5Eq5_endpointChain_F_twoValue_of_terminalRoom`,
`aoyagiLemma5Eq5_endpointChain_twoValueCount_of_terminalRoom`,
`aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefix_count_eq_of_terminalRoom`,
and
`aoyagiLemma5Eq5_endpointChain_HtildeChainBounds_of_terminalRoom`.  These are
thin adapters from the supplied Eq5 terminal-room binary-prefix deltas to the
existing Lemma 4 two-value, count, and Htilde-bound APIs.  They are not Eq5
vector construction, endpoint realisation, terminality, counted-datum
membership, classifier data, order count, pole order, normal crossings, or
RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-two-value-wrapper-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-two-value-wrapper.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-two-value-wrapper-a5.md`.

Latest A5 prefix-delta-chain-bound update: `HtildeChainArithmetic.lean` now
proves the algebraic translation from supplied prefix-delta bounds to displayed
chain bounds.  Names:
`aoyagiHtildeChainBounds_of_incrementPrefix_bounds` and
`aoyagiHtilde_interval_mem_of_incrementPrefix_bounds`.  These prove that
`min(a,j-(ell-a)) <= D_j <= min(j,a)` implies `Htilde <= H <= Htilde'`, and
then interval membership under `a<=ell`.  They do not prove the prefix-delta
bounds from binary increments or source vectors.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-prefix-delta-chain-bounds-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-prefix-delta-chain-bounds.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-prefix-delta-chain-bounds-a5.md`.

Latest A5 binary-prefix-delta-bound update: `HtildeChainArithmetic.lean` now
proves the elementary binary-prefix bounds and their Aoyagi wrapper.  Names:
`aoyagiIntegerPrefix_binaryDelta_bounds`,
`aoyagiLemma4IncrementPrefix_bounds_of_terminalH_binaryIncrementPrefixDelta`,
`aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta`, and
`aoyagiHtilde_interval_mem_of_terminalH_binaryIncrementPrefixDelta`.  Under
`a<=ell`, binary successive deltas, `D_0=0`, and `D_ell=a`, Lean proves
`min(a,j-(ell-a)) <= D_j <= min(j,a)`, then uses the terminal source
hypotheses for the Aoyagi increment prefix to derive displayed `Htilde` chain
bounds and interval membership.  This does not prove binary deltas from source
vectors or the Lemma 5 upper-bound classifier.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-binary-prefix-delta-bounds-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-binary-prefix-delta-bounds.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-binary-prefix-delta-bounds-a5.md`.

Latest A5 classifier source-probe update: PDF pp. 25-27 still do not prove
the full Lemma 5 upper-bound/no-extra classifier.  The interval count plus
Case 1(2)'s `J`-increase sentence does not supply a classifier, injection, or
back-to-label map.  The safe next source-facing statement is interval
`mapsTo` under explicit terminal/binary chain hypotheses.
Source probe:
`threads/05-arithmetic-tail/source-probe-lemma5-classifier-fields-a5.md`.

Latest A5 coordinate-coverage API probe: the next clean classifier-adjacent
Lean slice should stay in `Lemma5SuppliedFamily.lean`: construct
`AoyagiLemma5SuppliedNonbaseFamily` from coordinate-wise raw value coverage by
filtering out the supplied base value, then construct an
`AoyagiLemma5CountDatumClassifier` from a supplied branch-coordinate map and
injectivity of the tagged classifier.  Existing equation `(3)`/`(4)`/`(5)`
coverage is only one-coordinate/rising-region, so full-coordinate coverage
remains supplied.
API probe:
`threads/05-arithmetic-tail/api-probe-lemma5-coordinate-coverage-classifier-a5.md`.

Latest A5 binary supplied-family update: `Lemma5SuppliedFamily.lean` now
contains a narrower binary-prefix input form for the supplied admissible-family
boundary.  Names:
`AoyagiLemma5SuppliedBinaryNonbaseFamily`,
`AoyagiLemma5SuppliedBinaryNonbaseFamily.toAdmissibleNonbaseFamily`,
`AoyagiLemma5SuppliedBinaryFamily`,
`AoyagiLemma5SuppliedBinaryFamily.fullBranches`,
`AoyagiLemma5SuppliedBinaryFamily.fullH`,
`AoyagiLemma5SuppliedBinaryFamily.toAdmissibleFamily`, and
`AoyagiLemma5SuppliedBinaryFamily.fullBranches_card_and_fullBranch_twoValueCount`.
The conversion derives explicit `Htilde` bounds and two-value increment fields
from terminal binary prefix-delta data under `a<=ell` and the selected-width
sum.  It does not construct source vectors, prove source binary deltas, prove
the no-extra classifier, or touch pole order/normal crossings/RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-binary-supplied-family-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-binary-supplied-family.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-binary-supplied-family-a5.md`.

Latest A5 coordinate-coverage classifier update: `Lemma5SuppliedFamily.lean`
now contains the coordinate-coverage assembly recommended by the API probe.
Names:
`finset_image_filter_value_ne_eq_erase_image`,
`AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage`,
`AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord`, and
`AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord`.
The constructor filters a raw coordinate family by removing branches whose
value is the supplied base value, inheriting image coverage, injectivity, and
cross-coordinate disjointness.  The classifier bridge maps full branches into
the counted datum set and proves `mapsTo`; injectivity of the tagged classifier
is still an explicit supplied hypothesis.  This does not prove Aoyagi's
printed source family, Case 1(2) nonduplication, back-to-label coverage,
terminal-label exactness, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-coordinate-coverage-classifier-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-coordinate-coverage-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-coordinate-coverage-classifier-a5.md`.

Latest A5 counted-datum injection update: `Lemma5SuppliedFamily.lean` now
derives the tagged counted-datum injection from the supplied family fields.
Names:
`AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord_injOn`,
`AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord_of_branchCoord_eq`,
`AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumOfBranchCoord`,
`AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumClassifierOfBranchCoord`,
`AoyagiLemma5SuppliedBinaryFamily.countDatumOfBranchCoord`, and
`AoyagiLemma5SuppliedBinaryFamily.countDatumClassifierOfBranchCoord`.
The proof uses supplied branch-coordinate correctness, per-coordinate
injectivity of `value`, and equality of the tagged coordinate.  The binary
wrappers add no source content and use only the underlying nonbase family.
This still does not prove Aoyagi's printed branch construction, source
value-injectivity, branch-coordinate correctness, back-to-label
coverage, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-injection-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-injection.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-injection-a5.md`.

Latest A5 Eq5 non-rising coverage update: `Lemma5DisplayedVector.lean` now
proves the finite-set complement to the rising Eq5 offset result.  Names:
`aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet`,
`aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred`,
`aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred`,
`aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau`,
and
`aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_plateau`.
If `excess<=p-1`, the strict Eq5 offsets are exactly the same-coordinate
interval with the upper endpoint erased; a supplied upper endpoint fills the
interval.  In the plateau subcase `a<p<=ell-a`, a supplied Eq3-shaped
component gives that upper endpoint value.  This does not prove source-label
legality, terminality, chart coverage, an all-coordinate branch family, pole
order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-nonrising-coverage-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-nonrising-coverage.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-nonrising-coverage-a5.md`.

Latest A5 Eq5 endpoint-deficit update: `Lemma5DisplayedVector.lean` now
packages the rising/non-rising offset deficit as arithmetic and set
bookkeeping.  Names:
`aoyagiLemma5IntervalExcess_eq_self_iff_le_min`,
`aoyagiLemma5IntervalExcess_le_pred_of_not_le_min`,
`aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit`, and
`aoyagiLemma5Eq5_offsets_endpointDeficit_split`.  Eq5 always has an
upper-endpoint deficit and has an additional lower-endpoint deficit exactly in
the rising region.  This does not realise endpoints by source branches or
prove source-label legality, terminality, chart coverage, an all-coordinate
branch family, pole order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-endpoint-deficit-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-deficit.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-deficit-a5.md`.

Latest A5 supplied endpoint coverage update: `Lemma5DisplayedVector.lean` now
packages the endpoint-deficit split as supplied endpoint coverage.  Names:
`aoyagiLemma5_suppliedUpperLower_Eq5_offsets_eq_intervalValueSetNat_of_le_min`
and `aoyagiLemma5_suppliedEndpointCoverage_Eq5_offsets_split`.  A supplied
upper endpoint suffices outside the rising region; in the rising region a
supplied upper and supplied lower endpoint suffice.  This does not prove Eq3,
Eq4, or Eq5 legally supplies those endpoints, nor terminality, chart coverage,
all-coordinate branch-family coverage, pole order, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-supplied-endpoint-coverage-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-supplied-endpoint-coverage.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-supplied-endpoint-coverage-a5.md`.

Latest A5 Eq3 tail upper Eq5 coverage update:
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq3_piecewise_tail_upperEndpoint_of_boundary_lt` and
`aoyagiLemma5_suppliedEq3TailUpper_Eq5_offsets_eq_intervalValueSetNat_of_boundary_lt`.
For ordinary selected blocks strictly after Eq3's special boundary and before
the terminal endpoint, `ell-a+1 < p < ell`, the supplied Eq3 tail clause gives
the component value `Htilde'_p`; Eq5 non-rising coverage then fills the
same-coordinate interval.  This does not apply at `p=ell-a+1` or `p=ell`, and
it does not prove that this component is the vector's own source label, nor
Eq3 source-label legality, introduced-label status, terminality,
all-coordinate branch-family coverage, pole order, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-tail-upper-eq5-coverage-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-tail-upper-eq5-coverage.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-tail-upper-eq5-coverage-a5.md`.

Latest A5 Eq3 upper away-from-boundary update:
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_ne_boundary` and
`aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_nonrising_ne_boundary`.
For `1<=p`, `p<ell`, and `p!=ell-a+1`, the supplied Eq3 piecewise certificate
gives component value `Htilde'_p`; under the additional non-rising hypothesis,
Eq5 offsets plus that component fill the same-coordinate interval.  The result
packages the left ordinary Eq3 upper clause with the ordinary-tail clause.  It
excludes the Eq3 special boundary and terminal endpoint, and it does not prove
own-source-label status, source-label legality, introduced-label status,
all-coordinate endpoint realisation, injection, back-to-label coverage, pole
order, normal crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-upper-away-from-boundary-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-upper-away-from-boundary.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-upper-away-from-boundary-a5.md`.

Latest A5 Eq3 boundary Eq5 obstruction update:
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint`,
`aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets`,
`aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat`, and
`aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat_of_eq_boundary`.
At the special boundary `p=ell-a+1`, the supplied Eq3 value is
`Htilde'_p+1`, so it is outside the same-coordinate interval.  The Eq5 strict
offsets are contained in that interval, and inserting the boundary value into
those offsets cannot fill the interval.  This is a boundary obstruction, not an
endpoint-realisation theorem.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-boundary-eq5-obstruction-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-boundary-eq5-obstruction.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-boundary-eq5-obstruction-a5.md`.

Latest A5 Eq4 rising-boundary gap update:
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq4_no_piecewiseSourceVector_of_not_indexGuard`,
`aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a`, and
`aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint`.
At `p=a`, the Eq4 repaired guard would require `a+1<=a`, so no supplied
Eq4-piecewise source vector of this shape exists.  Under `a<=ell`, `1<=a`,
and `a<=ell-a`, Eq5 at the same coordinate is still in the rising
erased-endpoints case.  This is a gap record, not a replacement lower-endpoint
construction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-boundary-gap-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-rising-boundary-gap.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-rising-boundary-gap-a5.md`.

Latest A5 terminal Eq5 gap update:
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq5OffsetValueSet_eq_empty_of_terminal`,
`aoyagiHtildeIntervalValueSetNat_terminal_eq_singleton_zero_of_selectedSum`,
`aoyagiLemma5Eq5_terminal_offsets_ne_intervalValueSetNat_of_selectedSum`, and
`aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`, plus
the upper-endpoint form
`aoyagiLemma5_suppliedTerminalUpper_Eq5_offsets_eq_intervalValueSetNat`.
At `p=ell`, Eq5 strict offsets are empty.  Under the selected-width sum and
`a<=ell`, the terminal same-coordinate interval is `{0}`.  Eq5 offsets alone
therefore do not fill the terminal interval, while a separately supplied
terminal zero, or terminal upper endpoint, does.  This is supplied endpoint
bookkeeping, not terminal source construction or terminal-label exactness.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-eq5-gap-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-eq5-gap.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-eq5-gap-a5.md`.

Latest A5 counted-datum classifier-boundary update:
`Lemma5SuppliedFamily.lean` now has
`aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta`.  For
one interior coordinate, terminal binary prefix-delta chain data puts the
chain value in the same-coordinate interval, and a non-base-value hypothesis
puts the corresponding `some (j,H_j)` datum in the counted datum set.  This is
only a one-branch `mapsTo` theorem.
`Lemma5TerminalBridge.lean` now has
`AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumClassifier`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumClassifier`.
These package a supplied injective classifier from `terminalMinimumLabels` into
the counted datum set and derive the upper cardinality bound.  They do not
construct the classifier, prove branch-label exactness, prove source-label
legality, prove injection/back-to-label coverage from Aoyagi's printed
paragraph, or prove pole order/RLCT data.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-binary-counted-datum-maps-to-a5.md`
and
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-counted-datum-classifier-a5.md`.
Statement cards:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-binary-counted-datum-maps-to.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-minimum-counted-datum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-classifier-boundary-a5.md`.

Latest A5 upper-bound classifier equivalence update:
`Lemma5TerminalBridge.lean` now has
`AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_terminalMinimumLabels_subset_branchLabelImage`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_iff_terminalMinimumLabels_subset_branchLabelImage`.
These prove that the supplied `UpperBoundClassifier` is equivalent to the
no-extra inclusion `terminalMinimumLabels ⊆ branchLabelImage` by unpacking the
finite image definition.  This is not a source-backed classifier theorem.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-upper-bound-classifier-interface-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-upper-bound-classifier-interface.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-upper-bound-classifier-equivalence-a5.md`.

Latest A5 Eq3/Eq4 local interval cardinality update:
`Lemma5DisplayedVector.lean` now contains
`aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_intervalSize`
and
`aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_offsetCard_add_two`.
These prove the source-legality-free cardinality consequences of the existing
local Eq3/Eq4 rising-interval coverage equality.  They do not construct
displayed vectors, prove source-label legality, build classifier coverage,
prove the Lemma 5 order count, or touch pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq3-eq4-local-interval-cardinality-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq3-eq4-local-interval-cardinality.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq3-eq4-local-interval-cardinality-a5.md`.

Latest A5 counted-datum back-to-branch-label boundary update:
`Lemma5TerminalBridge.lean` now has
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchCountDatumOfCoord`,
`AoyagiLemma5SuppliedTerminalCandidateFamily.TerminalMinimumCountDatumBackToBranchLabel`,
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.upperBoundClassifier_of_countDatumBackToBranchLabel`.
These package a supplied bridge from the terminal-minimum counted-datum
classifier back to supplied branch labels, and derive the existing
`UpperBoundClassifier` from the supplied branch-label witness.  This is not a
source-backed proof of the classifier, branch-coordinate construction,
injection, back-to-label coverage, pole order, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-back-to-branch-label.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-back-to-branch-label-a5.md`.

Latest A5 terminal source-label update:
`Lemma5SourceLabel.lean` now has
`aoyagiLemma5_terminalSourceIndex_pos`,
`aoyagiLemma5_terminal_actualWidthLabel_of_lastPoint`, and
`aoyagiLemma5_terminal_intervalValue_mem_introducedLabelFinset_of_terminalZero`.
These prove terminal source-layer and `k=1` label legality under explicit
source-range and width-positivity hypotheses, and combine a supplied terminal
zero with the terminal interval singleton.  They do not construct the terminal
source branch, source-realisation equality, terminal-label exactness,
classifier coverage, injection, back-to-label coverage, pole order, normal
crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-label-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-label.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-label-a5.md`.

Latest A5 Eq5 post-`p` lower-obstruction update:
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq5_postP_belowLower_of_intervalExcess_lt_offset`.  It proves
that in the supplied equation `(5)` post-`p` range, if the printed subtraction
`alpha+b-p` exceeds the Htilde interval excess at `b`, then the branch value is
strictly below the lower Htilde chain.  This is an obstruction criterion for
supplied piecewise Eq5 data, not a source-vector construction, corrected Eq5
family, source-label legality theorem, chart-coverage theorem, classifier,
pole-order result, normal-crossing theorem, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-postp-lower-obstruction-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-postp-lower-obstruction.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-postp-lower-obstruction-a5.md`.

Latest A5 Eq4 rising-guard exhaustion update:
`Lemma5IntervalArithmetic.lean` now has
`aoyagiLemma5Eq4_risingGuardFailure_iff_eq_a` and
`aoyagiLemma5Eq4_selectedIndexGuardFailure_iff_eq_a`.  Under `p<=a`, failure
of the repaired Eq4 guard `p+1<=a`, equivalently failure of the raw selected
cutoff bound `p+(ell-a)+2<=ell+1` under `a<=ell`, is exactly the boundary
`p=a`.  `Lemma5DisplayedVector.lean` also has
`aoyagiLemma5Eq4_risingGuardFailure_eq_a_and_no_piecewiseSourceVector`, which
packages this with the supplied Eq4 certificate's guard-field obstruction.
This is guard arithmetic only, not a converse nonexistence theorem, Eq4
branch construction, endpoint coverage, pole order, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-guard-exhaustion-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-rising-guard-exhaustion.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-rising-guard-exhaustion-a5.md`.

Latest A5 counted-datum back-to-branch-label card-bound update:
`Lemma5TerminalBridge.lean` now has
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel`.
It derives the numeric upper bound on `terminalMinimumLabels` from supplied
counted-datum classifier data plus the supplied back-to-label bridge by
passing through the existing `UpperBoundClassifier`.  This is not a
source-backed classifier, branch-coordinate construction, back-to-label proof,
exact-cardinality theorem, pole-order theorem, normal-crossing theorem, or
RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-card-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-back-to-branch-label-card.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-back-to-branch-label-card-a5.md`.

Latest A5 terminal source-realisation iff zero update:
`Lemma5TerminalSourceBridge.lean` now has
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_realisation_iff_terminalZero`
and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_realisation_iff_terminalZero`.
They use branch-chain terminal zero to rewrite the terminal source-realisation
hypothesis as a supplied terminal source-zero hypothesis.  This is not a proof
of terminal source zero, terminal source-branch construction, terminal-label
exactness, classifier coverage, pole order, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-realisation-iff-zero-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-realisation-iff-zero.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-realisation-iff-zero-a5.md`.

Latest A5 counted-datum back-to-branch-label exactness update:
`Lemma5TerminalBridge.lean` now has
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_countDatumBackToBranchLabel`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_countDatumBackToBranchLabel`.
Together with supplied branch-label injectivity, the supplied counted-datum
back-to-label bridge gives `TerminalMinimumLabelExactness`; together with the
selected-width sum, this gives exact terminal-minimum label cardinality.  This
does not construct the classifier, branch-coordinate map, back-to-label bridge,
or injectivity from source and is not pole order, normal crossings, or RLCT
extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-counted-datum-back-to-branch-label-exactness.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-counted-datum-back-to-branch-label-exactness-a5.md`.

Latest A5 terminal source endpoint payload update:
`Lemma5TerminalSourceBridge.lean` now has
`aoyagiLemma5TerminalSourceEndpointPayload`,
`AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_terminalEndpointPayload`,
and
`AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_terminalEndpointPayload`.
These combine the existing terminal source-realisation bridge with terminal
source-label bookkeeping.  Under an explicit source-realisation equality,
terminal source range, and terminal width positivity, a supplied branch gives
terminal Eq5 finite-set coverage plus introduced-label membership for
`(C.point ell-1,1)`.  This is not source branch construction, not a proof of
the source-realisation equality, not terminal exactness, not classifier or
back-to-label coverage, and not pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-source-endpoint-payload-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-source-endpoint-payload.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-source-endpoint-payload-a5.md`.

Latest A5 Eq4 rising non-strict endpoint split update:
`Lemma5IntervalArithmetic.lean` now has
`aoyagiLemma5Eq4_risingNonStrictEndpoint_iff_predBoundary_or_eq_a` and
`aoyagiLemma5Eq4_boundaryIndex_not_lt_ell_iff_predBoundary_or_eq_a`.
`Lemma5DisplayedVector.lean` now has
`aoyagiLemma5Eq4_risingNonStrictEndpoint_predBoundary_or_no_piecewiseSourceVector`,
`aoyagiLemma5Eq4TerminalCollisionPayload`,
`aoyagiLemma5Eq4GuardFailurePayload`, and
`aoyagiLemma5Eq4_risingNonStrictEndpoint_split`.  Under rising hypotheses,
failure of the strict endpoint case `p+1<a` splits into terminal collision
`p+1=a` or repaired-guard failure `p=a`.  The terminal-collision branch is
conditional on supplied Eq4 piecewise data; the `p=a` branch records no
repaired Eq4 piecewise shape plus the Eq5 erased-endpoints deficit.  This is
endpoint bookkeeping only, not displayed-vector construction, source coverage,
terminal zero, classifier/injection/back-to-label coverage, pole order,
normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq4-rising-nonstrict-endpoint-split.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq4-rising-nonstrict-endpoint-split-a5.md`.

Latest A5 Eq5 own-block counted/introduced payload update:
`Lemma5Eq5CountDatumBridge.lean` now contains
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound`.
For one supplied Eq5 own-block branch, explicit source-label hypotheses and a
supplied nonbase inequality give both counted-datum membership for
`some (p,T S)` and introduced-label membership for `Sigma.mk S k`.  This is a
conditional one-branch payload only; it is not Eq5 vector construction,
nonbase production, classifier construction, injection, back-to-label
coverage, no-extra terminal-minimum coverage, order count, pole order, normal
crossings, or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-counted-introduced-payload.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-counted-introduced-payload-a5.md`.

Latest A5 Eq5 own-block block-width payload update:
`Lemma5Eq5CountDatumBridge.lean` now also contains
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_blockWidth`.
It replaces the raw selected-width bound in the own-block payload by a
block-local actual-width lower-bound hypothesis and `C.block p S`.  The
nonbase inequality, Eq5 data, and last-point source range remain explicit.
This is not Eq5 vector construction, classifier construction, back-to-label
coverage, Lemma 5 order count, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-block-width-payload-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-block-width-payload.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-block-width-payload-a5.md`.

Latest A5 Eq5 own-block width-source variants update:
`Lemma5Eq5CountDatumBridge.lean` now also contains
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_leftEndpointMin`,
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected`,
and
`aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_offSelected_lt`.
These replace the raw selected-width bound in the own-block payload by one of
the already-isolated source-shaped width dominance hypotheses:
left-endpoint/minimum, off-selected non-strict dominance, or off-selected
strict dominance.  The nonbase inequality, Eq5 data, and last-point source
range remain explicit.  This is not Eq5 vector construction, classifier
construction, back-to-label coverage, Lemma 5 order count, pole order, normal
crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-width-source-variants-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-width-source-variants.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-width-source-variants-a5.md`.

Latest A5 Eq5 own-block counted-datum classifier update:
`Lemma5Eq5CountDatumBridge.lean` now also contains
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound`,
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_blockWidth`,
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_leftEndpointMin`,
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected`,
and
`aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected_lt`.
These build an `AoyagiLemma5CountDatumClassifier` from a finite supplied
family of Eq5 own-block source-label payloads.  The `mapsTo` proof is
branchwise and uses the existing own-block counted-datum payload; the
classifier injectivity remains an explicit hypothesis.  This is not source
construction of the branch family, nonbase status, source-derived
nonduplication, terminal introduced-domain lifting, back-to-label coverage,
Lemma 5 order count, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-countdatum-classifier-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-countdatum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-countdatum-classifier-a5.md`.

Latest A5 Eq5 own-block common introduced-domain update:
`BlowupArithmetic.lean` now contains `introducedLabel_mono_state` and
`introducedLabelFinset_subset_of_state_le`; `Lemma5Eq5CountDatumBridge.lean`
now contains
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_widthBound`,
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_blockWidth`,
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_leftEndpointMin`,
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected`,
and
`aoyagiLemma5Eq5_ownBlock_commonIntroduced_of_lastPoint_offSelected_lt`.
The Eq5 wrappers use the existing own-block payload and then apply the
finite introduced-domain monotonicity subset to move `(S,k)` from local state
`(S,k)` into an explicitly supplied later/common state.  This is not terminal
state construction, terminal source realisation, source-derived classifier
data, Lemma 5 order count, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-ownblock-common-introduced-domain-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-ownblock-common-introduced-domain.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-ownblock-common-introduced-domain-a5.md`.

Latest A5 Eq5 terminal counted-datum classifier update:
new module `Lemma5Eq5TerminalClassifier.lean` contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumCountDatumClassifier_of_eq5OwnBlockCommon_widthBound`,
`..._blockWidth`, `..._leftEndpointMin`, `..._offSelected`, and
`..._offSelected_lt`.  These construct `TC.TerminalMinimumCountDatumClassifier`
from supplied Eq5 own-block common-domain payloads for labels already in
`TC.terminalMinimumLabels`, with classifier injectivity kept explicit.  This
feeds the existing terminal-minimum counted-datum upper-bound API but does not
construct Eq5 branches, prove all terminal labels have such payloads, build a
back-to-label map, prove `UpperBoundClassifier`, exactness, pole order,
normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-countdatum-classifier-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-countdatum-classifier.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-countdatum-classifier-a5.md`.

Latest A5 Eq5 terminal counted-datum cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5OwnBlockCommon_widthBound`,
`..._blockWidth`, `..._leftEndpointMin`, `..._offSelected`, and
`..._offSelected_lt`, plus the width-bound exactness wrappers
`terminalMinimumLabels_eq_branchLabelImage_of_eq5OwnBlockCommon_widthBound_cardSqueeze`,
`terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_cardSqueeze`,
`terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_cardSqueeze`,
and
`branchLabel_bijOn_terminalMinimumLabels_of_eq5OwnBlockCommon_widthBound_cardSqueeze`.
The upper-bound wrappers compose the supplied Eq5 terminal classifier with
the counted-datum cardinal theorem.  The exactness wrappers add supplied
branch-label injectivity and use the existing cardinal squeeze.  Counted-datum
injectivity remains distinct from branch-label injectivity.  This is not
source-derived Eq5 payload construction, source-derived injectivity, a
counted-datum-preserving back-to-label map, the printed Lemma 5 order count,
pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-countdatum-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-countdatum-cardinal-squeeze-a5.md`.

Latest A5 Eq5 branch-label injection update:
`Lemma5TerminalBridge.lean` now contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_fullBranches_of_some_injOn`;
`Lemma5Eq5TerminalClassifier.lean` now contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabel_injOn_of_eq5AlphaIndexed_nonbase`.
The first theorem lifts nonbase branch-label injectivity to the full
`Option`-tagged terminal branch set under explicit base/nonbase separation.
The second derives the nonbase injection for Eq5 alpha-indexed branches from
coordinatewise alpha injectivity, supplied selected-block membership of source
coordinates, and the displayed Eq5 label formula, using selected-cutpoint
block uniqueness for cross-coordinate disjointness.  This is not Eq5 branch
construction, alpha-domain coverage, source-derived injectivity,
back-to-label coverage, no-extra terminal-minimum coverage, order count, pole
order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-branch-label-injection-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-branch-label-injection.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-branch-label-injection-a5.md`.

Latest A5 Eq5 alpha-injection cardinal-squeeze update:
`Lemma5Eq5TerminalClassifier.lean` now also contains
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabelExactness_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze`
and
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_eq5OwnBlockCommon_widthBound_alphaIndexedBranch_cardSqueeze`.
These compose the Eq5 terminal counted-datum cardinal squeeze with explicit
Eq5 alpha-indexed branch-label injection data.  The opaque supplied
branch-label injectivity boundary is replaced by coordinatewise branch alpha
injectivity, branch block membership, branch label formula, and base/nonbase
separation.  Counted-datum injectivity and terminal-label Eq5 payloads remain
supplied.  This is not source-produced no-extra coverage, back-to-label
coverage, order count, pole order, normal crossings, or RLCT.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-terminal-alpha-injection-cardinal-squeeze-a5.md`.

Latest A5 Eq5 alpha endpoint value-image split update:
`Lemma5DisplayedVector.lean` now contains
`aoyagiLemma5Eq5_alphaIndexedBranch_suppliedEndpointCoverage_value_image_split`.
For one positive interior coordinate, supplied alpha-indexed Eq5 strict-offset
branches and supplied endpoint branch records give a disjunctive value-image
coverage theorem: upper endpoint plus Eq5 offsets fill the interval outside
the rising case; upper and lower endpoints plus Eq5 offsets fill it in the
rising case.  This is one-coordinate finite value-image bookkeeping only, not
branch construction, source-label legality, injectivity, base-value
membership, cross-coordinate disjointness, classifier construction,
no-extra terminal-minimum coverage, order count, pole order, normal crossings,
or RLCT extraction.
Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-alpha-endpoint-value-image-split.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-alpha-endpoint-value-image-split-a5.md`.

Latest A4 update: the Case 2 row-exhausted source-suffix payload has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_sourceSuffixTransportedPrefixBoundary_withFiniteCenterIdeal`,
`Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixTransportedPrefixPayload`,
and `SourceChartFrontierBoundaryPackages.rowExhaustedSourceSuffix`.  The slice
packages the existing row-exhausted transported-prefix source-suffix
entry-ideal equality with finite residual-center principalization.  It keeps
`sourceSuffixProduct`, transported rows, and explicit row-exhaustion
hypotheses; it does not require terminal-last, does not replace transported
rows by original rows, and does not assert `(S+1,0)` relabelled level/exponent
data.  It is not chart production, source-produced post-data, transition
invariance, Jacobian arithmetic, normal crossings, pole order, or RLCT
extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-source-suffix-payload-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-row-exhausted-source-suffix-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-row-exhausted-source-suffix-payload-a4.md`.

Latest A4 update: the Case 2 continuing weighted source-following payload has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal`,
`Case2DisplayedSuppliedChartFamilyBoundary.ContinuingWeightedSourceFollowingFrontierPayload`,
and `SourceChartFrontierBoundaryPackages.continuingWeighted`.  The slice
packages the existing paper-`C'` weighted lower-row handoff with
next-residual-center nonemptiness and finite residual-center
principalization under `J+2 <= prefixMinNat n (S+1)`.  It keeps the equality
lower-row only and keeps the successor lower-row diagonal explicit.  It is not
chart production, source-produced post-data, a full successor product,
transition invariance, Jacobian arithmetic, normal crossings, pole order, or
RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-source-following-payload-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-weighted-source-following-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-weighted-source-following-payload-a4.md`.

Latest A4 update: the Case 1(2) J-increment payload has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case1DisplayedRowStripJIncrementPayload`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge`,
`Case1DisplayedRowStripSuppliedTransitionBoundary.jIncrementPayload`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge`,
`Case1DisplayedRowStripSelectedOldPullbackBoundary.jIncrementPayload`,
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge`,
and
`Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.jIncrementPayload`.
This packages the finite consequences of Aoyagi PDF p. 18's Case 1(2)
continuation branch where `J` is increased by one: the non-strict next-state
bound `J+1 <= prefixMinNat n (S+1)`, actual-width validity and inserted
introduced-label membership/cardinality for `(S,J+1)`, and the post exponent
certificate domain.  The recurrence projection is deliberately from the
factored-old base state to the post-state,
`post.weight i = u * factoredBase.weight i` for `i >= J+1`; it is not a direct
comparison from the substituted source state, which already contains the old
selected factor at level `J+J1`.  This is finite supplied-boundary bookkeeping
only.  It does not construct the chart or post-state, prove nonempty residual
block after the increment, chart coverage, regularity, Jacobians, a transition
invariant, Lemma 5 classifier/no-extra/back-to-label data, pole order, normal
crossings, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-j-increment-payload-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-j-increment-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case1-j-increment-payload-a4.md`.

Latest A4 update: the Case 2 displayed J-increment payload has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean names are
`Case2DisplayedJIncrementPayload`,
`Case2DisplayedSuppliedChartFamilyBoundary.post_weight_eq_new_mul_pre_weight_of_ge`,
and `Case2DisplayedSuppliedChartFamilyBoundary.jIncrementPayload`.  This
packages the finite consequences of Aoyagi PDF p. 21's displayed Case 2
continuation branch where `J` is increased by one: the non-strict next-state
bound `J+1 <= prefixMinNat n (S+1)`, corrected new-label validity for
`(S,J+1)`, inserted introduced-label membership/cardinality, corrected
new-label numerator identities, post exponent certificates, and the displayed
recurrence-weight update `post.weight i = u * pre.weight i` for `i >= J+1`.
The exponent side uses the corrected Case 2 package already isolated in Lean;
it does not turn Aoyagi's printed Case 2 vector mismatch into a source theorem.
This is finite supplied-boundary bookkeeping only.  It does not construct the
chart or post-state, prove a nonempty residual block after the increment,
successor chart-family construction, a full next `C'^(S+1)`, transition
invariance, Jacobian arithmetic, normal crossings, pole order, or RLCT
extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-j-increment-payload-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-j-increment-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-j-increment-payload-a4.md`.

Source-frontier audit after the A5 alpha-injection cardinal squeeze:
a broad new reproduction of the local Case 2 `C'=Q^-1*C` calculation is not
needed.  Existing A4 artifacts already define the paper transported factor,
prove its top-row correction and unchanged lower tail, specialize the
weighted lower-row product to paper `C'`, and package
`SuppliedTerminalCprimeBridge`.  The missing A4 row is chart/source production
of the full successor object or successor following-product data from the
displayed chart across continuing and terminal branches; the current terminal
bridges deliberately stop at supplied row equations.  Audit:
`threads/04-blow-up-certificate/source-frontier-audit-case2-paper-cprime-a4.md`.

Latest A4 update: the Case 2 continuing weighted following-product slice has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData`.
It right-multiplies the existing paper-`C'` weighted lower-row handoff by a
supplied following product `F`, preserving the same witness and corrected
post-data projections.  This is lower-row equality congruence only: `F`
remains supplied, the pivot row is absent, the successor lower-row diagonal is
explicit, and there is no next-center nonemptiness, source-produced successor
`C'^(S+1)`, chart production, transition invariant, normal crossings, pole
order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-weighted-following-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-weighted-following-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-weighted-following-product-a4.md`.

Latest A4 update: the Case 2 source successor following-factor slice has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are `case2DisplayedSourceSuccessorFollowingFactor`,
`case2DisplayedSourceSuccessorFollowingFactor_pivotRow`,
`case2DisplayedSourceSuccessorFollowingFactor_of_ne`,
`case2DisplayedSourceSuccessorFollowingFactor_oldRow`,
`case2SourceFollowingFactor_successorFollowingFactor_succ`,
`case2DisplayedSourceSuccessorFollowingFactor_eq_original_of_width_next_eq`,
`case2DisplayedSourceTerminalOriginalRows_successorFollowingFactor`, and
`case2DisplayedSourceTerminalCprimeCandidate_eq_originalRows_successorFollowingFactor`.
This source-order object replaces only row `J+1` of `C` by the top row of
`Q^-1 C`.  It is formula-level data only: it proves row restrictions,
unchanged post-pivot same-stage following restriction, actual-width collapse
to the original `C`, and transported terminal-row presentation, but no chart
production, source-produced recurrence/exponent post-data, old-top/suffix
production, transition invariant, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-successor-following-factor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-successor-following-factor.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-successor-following-factor-a4.md`.

Latest A4 update: the Case 2 successor following weighted handoff slice has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withSuccFollowingFactorAndCorrectedData`
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_mul_F_withSuccFollowingFactorAndCorrectedData`.
They restate the existing weighted lower-row paper-`C'` handoff using the
formula-level successor following factor `Csucc`; the only mathematical input
is that the `(S,J+1)` following restriction ignores row `J+1`.  This is not
next-center nonemptiness, source production of `F`, old-top/suffix production,
full successor `C'^(S+1)`, chart production, transition invariance, normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-successor-following-weighted-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-successor-following-weighted-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-successor-following-weighted-handoff-a4.md`.

Latest A4 update: the Case 2 successor following frontier payload slice has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
names are `ContinuingWeightedSuccFollowingFrontierPayload` and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal`.
The theorem adds the `hnext` nonempty-next-center guard and current-center
principalization facts to the successor-following lower-row handoff.  It is
theorem-only, with no new `SourceChartFrontierBoundaryPackages` field.  This
is not source/chart production of `Csucc`, old-top/suffix production, full
successor `C'^(S+1)`, transition invariance, normal crossings, pole order, or
RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-successor-following-frontier-payload-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-successor-following-frontier-payload.md`.
Review:
`threads/04-blow-up-certificate/review-case2-successor-following-frontier-payload-a4.md`.

Latest A4 update: the Case 2 source-residual/successor-following product slice
has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved
Lean name is
`Case2DisplayedSuppliedChartFamilyBoundary.case2DisplayedPaperDppp_mul_Cprime_postPivot_eq_sourceResidualBlock_successorFollowingFactor`.
It combines the earlier source-residual/source-following product with the
successor-following restriction equality, giving the bare lower-row product in
source-pair notation.  The weighted source-chart variant remains deferred
until a downstream theorem needs it.  This is not chart production, full
successor `C'^(S+1)`, transition invariance, normal crossings, pole order, or
RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-residual-successor-following-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-residual-successor-following-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-residual-successor-following-product-a4.md`.

Latest A4 update: the Case 2 actual-width successor terminal-row slice has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_actualWidth_terminalOriginalRowsSuccFollowingSuppliedSuffixBoundary`.
It restates the actual-width supplied-`F` terminal boundary with
`case2DisplayedSourceTerminalOriginalRows (case2DisplayedSourceSuccessorFollowingFactor ...)`
on the right.  This uses exactly actual next-width exhaustion
`n(S+1)=J+1`, under which `Csucc=C`; it is not row-exhaustion or broad stopped
frontier data.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-actual-width-successor-terminal-rows-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-actual-width-successor-terminal-rows.md`.
Review:
`threads/04-blow-up-certificate/review-case2-actual-width-successor-terminal-rows-a4.md`.

Latest A4 update: the Case 2 row-exhausted successor-prefix row-presentation
slice has landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The
proved Lean names are
`case2DisplayedSourceTerminalCprimePrefixCandidate_eq_originalRows_successorFollowingFactor`
and
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChart_rowExhausted_sourceSuffixSuccFollowingPrefixBoundary_withFiniteCenterIdeal`.
They rewrite the row-exhausted source-suffix terminal prefix through original
rows of `case2DisplayedSourceSuccessorFollowingFactor`.  This uses
`prefixMinNat n S=J+1`, not actual next-width exhaustion; row `J+1` remains
the transported top row of `Q^-1 C`, now packaged as row `J+1` of `Csucc`.
The source suffix and current-center principalization facts remain explicit.
No frontier-package field was added.  This is not chart/source production of
`Csucc`, source-suffix production, actual-width original-row collapse,
`(S+1,0)` relabelled data, full successor chart production, transition
invariance, normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-row-exhausted-successor-prefix-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-row-exhausted-successor-prefix.md`.
Review:
`threads/04-blow-up-certificate/review-case2-row-exhausted-successor-prefix-a4.md`.

Latest A4 update: the Case 2 continuing old-top/source-suffix stack slice has
landed in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.  The proved Lean
name is
`Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`.
It lifts the supplied paper `Q/P` identity through unchanged old top rows,
then right-multiplies by the raw source suffix `sourceSuffixProduct`.  This is
not the lower-row arbitrary-`F` wrapper: the theorem keeps the old top rows and
transported pivot row in paper `C'=Q^-1 C`.  It remains a supplied-boundary
pivot-first stack identity, not source production of a source-ordered
successor `C'^(S+1)`, source production of the suffix, transition invariance,
normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-oldtop-source-suffix-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-oldtop-source-suffix-stack-a4.md`.

Latest A4 update: the Case 2 source-current row reindex slice has landed in
`lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`, inside the
`Case2DisplayedSuppliedChartFamilyBoundary` namespace.  The proved Lean names are
`case2SourceCurrentRowIndex`, `case2SourceOldTopPaperCprimeRowEquiv`,
`case2SourceCurrentFollowingBlock`, `case2SourceSuccessorFollowingBlock`,
`case2SourceCurrentFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`, and
`case2SourceSuccessorFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`.
They reindex source rows `1..n(S+1)` as old-top rows, the displayed pivot row,
and post-pivot rows.  The old source following block reindexes to
`[oldTop; displayedSourceFollowingFactor]`, and the formula-level successor
following block reindexes to `[oldTop; paperCprime]`.  This is finite
source-order bookkeeping only, not chart production of `Csucc`, source
production of `C'^(S+1)`, suffix production, recurrence/exponent post-data,
transition invariance, Jacobian arithmetic, normal crossings, pole order,
termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-current-row-reindex-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-row-reindex.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-row-reindex-a4.md`.

Latest A4 Case 2 source-current stack update:
`BlowupArithmetic.lean` now contains, inside the
`Case2DisplayedSuppliedChartFamilyBoundary` namespace,
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData`.
This is a row-presentation wrapper around
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`.
It rewrites the old following stack as
`case2SourceCurrentFollowingBlock.submatrix e id` and the transported stack as
`case2SourceSuccessorFollowingBlock.submatrix e id`, where `e` is the finite
source-row equivalence from old-top/pivot/post-pivot rows to
`1..n(S+1)`.  The theorem preserves the earlier next-center nonemptiness,
corrected post exponent data, post level/gap data, and finite current-center
principalization facts.  It does not produce `Csucc`, source-produce
`C'^(S+1)`, produce the source suffix, prove transition invariance, normal
crossings, pole order, termination, or RLCT.
Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-stack-a4.md`.

Latest A4 Case 2 old-top/source-suffix paper-`C'` stack chart-family-free
directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`.
The theorem has the same finite old-top/source-suffix paper-`C'` stack
conclusion as
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withCorrectedPostData`,
but it has no `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` inputs.  The old API is retained as a
compatibility wrapper and ignores its chart-family argument.  The direct proof
uses the corrected new-label certificate, concrete `case2Succ` recurrence
post-data, corrected exponent post-data, the finite pre-reindex displayed
`Q/P` identity, old-top lifting, and multiplication by the supplied raw
source suffix.  This is not source production of `Csucc` or `C'^(S+1)`,
suffix production, successor chart-family construction, coverage, transition
regularity, analytic Jacobian/volume-form theorem, normal crossings, pole
order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-oldtop-source-suffix-paper-cprime-stack-without-chart-family-a4.md`.

Latest A4 Case 2 paper-`C'` lower-row chart-family-free directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_paperCprimeWeightedLowerRows_withoutChartFamily` and
`sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withoutChartFamily`.
They have the same finite lower-row conclusions as
`sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData` and
`sourceChartMap_paperCprimeWeightedLowerRows_mul_followingProduct_withCorrectedPostData`,
but no `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` inputs.  The old APIs are retained as
compatibility wrappers and ignore their chart-family arguments.  The proof
uses the corrected new-label certificate, concrete `case2Succ` recurrence
post-data, corrected exponent post-data, the finite displayed source `Q/P`
identity, lower-row projection, the weighted `D''' * C'` lower-row projection,
and the paper-`C'` lower-tail identity.  This is not pivot-row equality,
source production of `Csucc` or `C'^(S+1)`, suffix production, successor
chart-family construction, coverage, transition regularity, analytic
Jacobian/volume-form theorem, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-paper-cprime-lower-rows-without-chart-family-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-paper-cprime-lower-rows-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-paper-cprime-lower-rows-without-chart-family-a4.md`.

Latest A4 Case 2 source-current stack chart-family-free directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withoutChartFamily`.
It has the same finite source-current row stack conclusion as
`sourceChartMap_continuingOldTopSourceSuffixSuccFollowingBlock_withCorrectedPostData`,
but no `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` inputs.  The old API is retained as a
compatibility wrapper and ignores its chart-family argument.  The proof uses
`sourceChartMap_continuingOldTopSourceSuffixPaperCprimeStack_withoutChartFamily`
and the two source-current row reindex lemmas
`case2SourceCurrentFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv` and
`case2SourceSuccessorFollowingBlock_submatrix_oldTopPaperCprimeRowEquiv`.
This is not chart production of the successor following block, source
production of `Csucc` or `C'^(S+1)`, suffix production, successor chart-family
construction, coverage, transition regularity, coordinate-derived corrected
post-data, analytic Jacobian/volume-form theorem, normal crossings, pole
order, termination, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-without-chart-family-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-stack-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-stack-without-chart-family-a4.md`.

Latest A4 Case 2 branchwise successor-production boundary:
`threads/04-blow-up-certificate/reproduction-case2-branchwise-successor-production-boundary-a4.md`
records a reproduction-first contract rather than a Lean theorem.  It anchors
in Aoyagi PDF pp. 19-22 and separates three future source-production branches:
continuing `J+2 <= prefixMinNat n (S+1)`, actual-width stopped
`n(S+1)=J+1`, and row-exhausted stopped `prefixMinNat n S=J+1`.  It records
that all branches keep the standing displayed-pivot hypotheses, that the
continuing payload is the stronger nonempty-next-center refinement of
Aoyagi's printed non-strict guard, and that stopped branches are not asserted
exclusive.  It records the finite data already proved in Lean (`Q/P` algebra,
`Q^-1 C` row formulas, lower-row products, source-current stack presentation,
actual-width original-row collapse, row-exhausted transported-prefix
presentations, and current-center principalization) and keeps source
production of full `C'^(S+1)`, successor chart-family construction, coverage,
transition regularity, suffix/following-product production, coordinate
derivation of corrected post-data, Jacobian arithmetic, normal crossings,
pole order, termination, and RLCT deferred.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-branchwise-successor-production-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-case2-branchwise-successor-production-boundary-a4.md`.

Latest A4 Case 2 source-production obligation interface:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation`.  This
is a supplied `Prop` structure, not a theorem.  It packages the branchwise
successor-production obligations after the displayed Case 2 source chart:
formula equality for supplied `Csucc`, continuing weighted
successor-following frontier, actual-width stopped source-suffix frontier with
original terminal rows and relabelled certificates, and row-exhausted
source-suffix frontier with transported terminal rows.  The formerly present
continuing supplied next chart-family field has since been removed as
vacuous.  No inhabitant is constructed from the current displayed boundary.
It is not source production of `C'^(S+1)`, suffix production, coverage,
transition regularity, coordinate post-data derivation, Jacobian arithmetic,
normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-a4.md`.

Latest A4 Case 2 continuing successor-following handoff:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.continuingWeightedSuccFollowingFrontierPayload_of_sourceFollowing`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceChartFrontierBoundaryPackages.continuingWeightedSuccFollowing`.
These theorems convert the existing continuing weighted source-following
payload to canonical formula-level successor-following notation, and project
the same conversion from a frontier package under its existing continuing
guard.  The proof uses only the finite restriction identity
`case2SourceFollowingFactor_successorFollowingFactor_succ`; it is not
arbitrary supplied-`Csucc` source production without a supplied equality to
`case2DisplayedSourceSuccessorFollowingFactor`, and it does not construct
`C'^(S+1)`, suffixes, charts, transitions, normal crossings, pole order, or
RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-successor-following-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-successor-following-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-successor-following-handoff-a4.md`.

Latest A4 Case 2 source-production obligation row-exhausted Csucc projection:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.rowExhausted_Cterm_eq_originalRows_Csucc`.
Given a supplied `SourceProductionObligation` and the row-exhausted branch
hypothesis, it rewrites the supplied terminal matrix `Cterm` as original
terminal rows of the supplied successor factor `Csucc`.  The proof uses only
`rowExhausted_Cterm_eq`, the existing transported-row/original-successor-row
identity, and `Csucc_eq_formula`.  It is not construction of the obligation,
`Csucc`, `C'^(S+1)`, suffixes, charts, transitions, normal crossings, pole
order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-row-exhausted-csucc-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-row-exhausted-csucc.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-row-exhausted-csucc-a4.md`.

Latest A4 Case 2 source-production obligation Csucc projections:
`BlowupArithmetic.lean` now also contains
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_Csucc_tail_eq_original`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.actualWidth_Cterm_eq_originalRows_Csucc`.
Given a supplied `SourceProductionObligation`, the first rewrites the supplied
`Csucc` next same-stage tail to the old source-following tail by
`Csucc_eq_formula` and the existing successor-following restriction theorem.
Given actual-width exhaustion, the second rewrites `Cterm` as original rows of
the supplied `Csucc` by `actualWidth_Cterm_eq`, the actual-width collapse of
the canonical successor factor, and `Csucc_eq_formula`.  These are not
construction of the obligation, `Csucc`, `C'^(S+1)`, suffixes, charts,
transitions, normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-csucc-projections-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-csucc-projections.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-csucc-projections-a4.md`.

Latest A4 Case 2 source-production obligation canonical formula constructor:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`.
It constructs a `SourceProductionObligation` with `Csucc` chosen as the
formula-level successor following factor and `Cterm` chosen as transported
terminal rows.  This removes the need to choose arbitrary `Csucc/Cterm` in
this canonical constructor but does not construct a next chart-family,
source-produce successor chart data, produce suffixes, prove
coverage/transition regularity, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-canonical-formula-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-canonical-formula.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-canonical-formula-a4.md`.

Latest A4 Case 2 true-predicate next boundary:
`BlowupArithmetic.lean` now contains
`SelectedEntryChartFamilyBoundary.exists_trivial`,
`Case2ResidualBlockChartFamilyBoundary.exists_trivial`,
and
`Case2ResidualBlockChartFamilyBoundary.continuingSuccessorBoundary_exists_truePredicates`.
The first two choose `True` predicates for chart and transition regularity.
The continuing-successor helper has the exact shape of the previous supplied
field before that field was removed.  This is a precision theorem about the
weakness of the old API, not a source-backed chart-production theorem.  Source
audit of Aoyagi pp. 19-22 found only the assertion that the induction
continues after the `Q/P` algebra, not construction of the next chart family,
transition regularity, coverage, successor `C'^(S+1)`, or suffix production.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-trivial-next-chart-family-boundary-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-trivial-next-chart-family-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-case2-true-predicate-next-boundary-a4.md`.

Latest A4 Case 2 source-production obligation field removal:
`BlowupArithmetic.lean` now removes the vacuous
`continuing_suppliedNextChartFamily` field from
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation`.
The main canonical constructor is
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_formulaSuccessor_transportTerminalRows`.
The older supplied-next-boundary and true-predicate-next-boundary constructor
names were removed from the current Lean API rather than retained as
ignored-argument wrappers.  This is API hardening only: no successor source
production, suffix production, meaningful chart coverage or transition
regularity, coordinate post-data derivation, normal crossings, pole order,
termination, or RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-remove-vacuous-next-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-remove-vacuous-next-boundary-a4.md`.

Latest A4 Case 2 obligation row-exhausted Cterm frontier:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.RowExhaustedSourceSuffixSuppliedCtermPrefixPayload`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.rowExhausted_frontier_suppliedCtermPrefix`.
The projection consumes a supplied `SourceProductionObligation` and the
row-exhausted branch hypothesis, rewriting the row-exhausted source-suffix
frontier's terminal prefix from transported rows to
`Cterm.submatrix ...` using the obligation's supplied terminal-row equality.
This is finite payload rewriting only; it does not construct the obligation,
`Cterm`, `Csucc`, `C'^(S+1)`, suffixes, charts, coverage, transition
regularity, coordinate post-data, normal crossings, pole order, termination,
or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-row-exhausted-cterm-frontier-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-row-exhausted-cterm-frontier.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-row-exhausted-cterm-frontier-a4.md`.

Latest A4 Case 2 obligation continuing Csucc stack:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_Csucc_currentFollowingBlock_eq_formula`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc`.
The first theorem rewrites the current source-row block of the supplied
successor factor `Csucc` to the formula-level successor block using the
obligation's `Csucc_eq_formula`.  The second consumes a supplied obligation
and the continuing guard `J+2 <= prefixMinNat n (S+1)` to restate the
old-top/source-suffix stack payload with
`case2SourceCurrentFollowingBlock n S Csucc` on the successor side.  This is
finite payload rewriting only; it does not construct the obligation, `Csucc`,
`C'^(S+1)`, suffixes, charts, coverage, transition regularity, coordinate
post-data, normal crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-continuing-csucc-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-continuing-csucc-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-continuing-csucc-stack-a4.md`.

Latest A4 Case 2 obligation actual-width Cterm frontier:
`BlowupArithmetic.lean` now contains
`Case2DisplayedSuppliedChartFamilyBoundary.ActualWidthSourceSuffixSuppliedCtermPayload`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.actualWidth_frontier_suppliedCterm`.
The projection consumes a supplied `SourceProductionObligation` and the
actual-width stopped branch hypothesis `n(S+1)=J+1`, rewriting the
actual-width source-suffix frontier's terminal factor from original rows of
old `C` to the supplied terminal matrix `Cterm`.  The source suffix, finite
center, relabelled level, and relabelled exponent payloads are unchanged.
This is finite payload rewriting only; it does not construct the obligation,
`Cterm`, `Csucc`, `C'^(S+1)`, suffixes, charts, coverage, transition
regularity, coordinate post-data, normal crossings, pole order, termination,
or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-production-obligation-actual-width-cterm-frontier-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-production-obligation-actual-width-cterm-frontier.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-production-obligation-actual-width-cterm-frontier-a4.md`.

Latest A4 Case 2 next-state source-product reindex:
`BlowupArithmetic.lean` now contains
`case2SourceOldTopSuccResidualRowEquiv`,
`case2SourceOldTopSuccResidualColEquiv`,
`case2DisplayedSuccessorFollowingFactor_reindex_nextSource`,
`case2DisplayedWeightedDppp_reindex_nextSource`,
`case2DisplayedPivotFirstRHS_reindex_nextSourceProduct`, and
`case2DisplayedPivotFirstRHS_reindex_nextSourceProduct_mul`.
These prove finite row/column/product reindexing from the displayed
pivot-first Case 2 right-hand side to the next same-stage source-product
shape.  The product side keeps the formula-level successor following factor
explicit and rewrites the lower block as the post-pivot source residual block
times the successor following tail.  This is not construction of `Csucc`,
source production of full `C'^(S+1)`, suffix production, successor chart
construction, coverage/transition regularity, coordinate post-data,
normal crossings, pole order, termination, RLCT, or repair of the printed
Case 2 vector mismatch.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-next-state-source-product-reindex-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-next-state-source-product-reindex.md`.
Review:
`threads/04-blow-up-certificate/review-case2-next-state-source-product-reindex-a4.md`.

Latest A4 Case 2 selected-entry chart-family data:
`BlowupArithmetic.lean` now contains `SelectedEntryChartFamilyData`,
`SelectedEntryChartFamilyData.standard`, the pivot/off-pivot/divisibility and
finite-center principalization projections, the Case 2 specialization
`Case2ResidualBlockSelectedEntryChartFamilyData`, displayed-pivot adapters,
and `sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData`.  These
package the finite selected-entry chart coordinate formula, identify Aoyagi's
displayed top-left Case 2 pivot chart with `case2DisplayedSourceChartMap`,
and compose the displayed source-chart `Q/P` identity with the next
same-stage source-product reindex while returning corrected concrete post-data
projections.  This is not chart coverage, transition regularity, all-pivot
chart construction, source production of full `C'^(S+1)`, suffix production,
coordinate derivation of corrected post-data, Jacobian arithmetic, normal
crossings, pole order, termination, RLCT, or repair of the printed Case 2
vector mismatch.  The source caveat is explicit: Aoyagi's printed
`b'_i = u b_i` line and later outside `u diag(b')` line are not simultaneously
literal, so Lean follows the corrected post-weight convention.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-chart-family-data-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-chart-family-data.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-chart-family-data-a4.md`.

Latest A4 Case 2 direct reindexed next-source product:
`BlowupArithmetic.lean` now contains
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData`.
The theorem removes the supplied chart-family boundary from the finite
reindexed next-source-product theorem.  It uses the low-level finite `Q/P`
identity with concrete `case2Succ` post-data, derives `pre.case2Gap` from the
old level/least-value bridge and integer least-value gap, uses
`Case2CorrectedExponentPostData.updateSelected` for the corrected exponent
post-data, lifts the lower-row identity through old top rows, and applies
`case2DisplayedPivotFirstRHS_reindex_nextSourceProduct`.  The older theorem
`sourceChartMap_reindexedNextSourceProduct_withCorrectedPostData` is retained
as a compatibility wrapper that delegates to the direct theorem.  This is not
source production of `Csucc`, successor chart production, suffix production,
coverage/transition regularity, analytic Jacobian data, normal crossings,
pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-reindexed-next-source-product-direct-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-reindexed-next-source-product-direct.md`.
Review:
`threads/04-blow-up-certificate/review-case2-reindexed-next-source-product-direct-a4.md`.

Latest A4 Case 2 selected-entry center square and formal Jacobian:
`BlowupArithmetic.lean` now contains `selectedEntryCenterSq`,
`selectedEntryCenterSq_selectedEntryChartMap`,
`selectedEntryPivotFirstJacobian`, `selectedEntryPivotFirstJacobian_det`,
`SelectedEntryChartFamilyData.centerSq_chartMap`,
`case2DisplayedSourceChartMap_centerSq`,
`case2DisplayedSourceChartMap_pivotFirstJacobian_det`, and
`case2DisplayedSourceChartMap_pivotFirstJacobian_exponent_eq_centerCard_sub_one`.
These prove the finite square-sum pullback for a selected-entry chart and the
formal pivot-first determinant `det [1 0; y uI] = u^(non-pivot count)`, then
specialize those facts to Aoyagi's displayed Case 2 residual-block pivot.
This is useful A0-facing local algebra, but it is not an A0 chart
certificate: the normalized square-sum factor is only a unit candidate, and
no analytic nonvanishing, differentiable Jacobian theorem, chart coverage,
transition regularity, pole order, or RLCT extraction is proved.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-sq-jacobian-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-center-sq-jacobian.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-center-sq-jacobian-a4.md`.

Latest A4 Case 2 continuing reindexed source-chart certificate:
`BlowupArithmetic.lean` now contains
`Case2DisplayedReindexedNextSourceProductEq`,
`Case2DisplayedContinuingReindexedSourceChartCertificate`, and
`sourceChartMap_continuingReindexedSourceChartCertificate`.  These package the
displayed continuing source-chart formula, finite center
membership/divisibility/principalization, the corrected post-weight convention,
next-center nonemptiness under `J+2 <= prefixMinNat n (S+1)`, the reindexed
next same-stage source-product equality, corrected exponent/level/gap
post-data, and the corrected new-numerator center-cardinality equality.  This
is A4-local data, not an A0 normal-crossing chart certificate: no loss or
Jacobian-prior monomial identities, unit factors, analytic coverage,
successor transition regularity, source production of `Csucc`, suffix
production, pole order, or RLCT extraction are proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-reindexed-source-chart-certificate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-reindexed-source-chart-certificate.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-reindexed-source-chart-certificate-a4.md`.

Latest A4 Case 2 selected-entry center unit factor:
`BlowupArithmetic.lean` now contains `selectedEntryCenterSq_nonneg`,
`selectedEntryCenterSqUnitFactor`,
`selectedEntryCenterSqUnitFactor_pos`,
`selectedEntryCenterSqUnitFactor_ne_zero`,
`selectedEntryCenterSqUnitFactor_isUnit`,
`case2DisplayedSourceChartMap_centerSqUnitFactor_pos`,
`case2DisplayedSourceChartMap_centerSqUnitFactor_ne_zero`, and
`case2DisplayedSourceChartMap_centerSqUnitFactor_isUnit`.  These prove the
normalized finite selected-entry square-sum factor is positive/nonzero under
ordered commutative semiring hypotheses and is a unit over an ordered field.  The
displayed Case 2 wrappers specialize this to the erased residual-block center
after choosing the displayed pivot.  This is pointwise finite algebra only:
no arbitrary-field or complex-field statement, analytic unit neighbourhood,
`P`/`Q` unit control, total loss unit, chart coverage, normal-crossing
certificate, pole order, or RLCT extraction is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-center-unit-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-center-unit.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-center-unit-a4.md`.

Latest A4 Case 2 continuing reindexed source-chart unit certificate:
`BlowupArithmetic.lean` now contains
`Case2DisplayedContinuingReindexedSourceChartUnitCertificate` and
`sourceChartMap_continuingReindexedSourceChartUnitCertificate`.  These package
the existing displayed continuing reindexed source-chart certificate together
with the positivity, nonzero, and `IsUnit` witnesses for the normalized
selected-entry center-square factor on the erased residual-block center.  This
is an A4-local ordered-field refinement only: no analytic neighbourhood unit,
`P`/`Q` unit control, total loss unit, chart coverage, transition regularity,
Jacobian/volume theorem, A0 normal-crossing certificate, pole order, or RLCT
extraction is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-reindexed-source-chart-unit-certificate.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-reindexed-source-chart-unit-certificate-a4.md`.

Latest A4 Case 2 continuing center-square/formal-Jacobian certificate:
`BlowupArithmetic.lean` now contains `case2DisplayedPaperQ_isUnit`,
`case2DisplayedPaperQ_det_isUnit`, `case2DisplayedPaperQinv_isUnit`,
`case2DisplayedPaperQinv_det_isUnit`,
`Case2DisplayedContinuingReindexedSourceChartCenterSqFormalJacobianCertificate`,
`sourceChartMap_continuingReindexedSourceChartCenterSqFormalJacobianCertificate`,
and
`Case2DisplayedContinuingReindexedSourceChartCertificate.exists_reindexedNextSourceProduct_with_PQ_det_units`.
These package the displayed continuing Case 2 local certificate with the
finite center-square identity, pointwise ordered-field unit factor, formal
pivot-first determinant exponent, the equality that the corrected new
numerator is the formal determinant exponent plus one, and finite
determinant-unit witnesses for displayed `Q/Q^-1` and the supplied `P`
row-operation.  This remains finite algebra only: no analytic chart
neighbourhood, chart coverage, transition regularity, analytic `P/Q` unit
control, differentiable Jacobian or volume theorem, A0 normal-crossing chart
certificate, pole order, or RLCT extraction is proved.  The p. 21 apparent
extra-`u` display is recorded as a source caveat, not formalised as a literal
product theorem.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-center-sq-formal-jacobian-certificate.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-center-sq-formal-jacobian-certificate-a4.md`.

Latest A4 Case 2 continuing certificate chart-family-free directification:
`BlowupArithmetic.lean` now contains
`sourceChartMap_continuingReindexedSourceChartCertificate_withoutChartFamily`,
`sourceChartMap_continuingReindexedSourceChartUnitCertificate_withoutChartFamily`,
and
`sourceChartMap_continuingCenterSqFormalJacobianCertificate_withoutChartFamily`.
The old constructors
`sourceChartMap_continuingReindexedSourceChartCertificate`,
`sourceChartMap_continuingReindexedSourceChartUnitCertificate`, and
`sourceChartMap_continuingReindexedSourceChartCenterSqFormalJacobianCertificate`
remain compatibility wrappers and ignore the old chart-family argument.  The
direct constructors use the chart-family-free reindexed next-source-product
theorem plus finite selected-entry/unit/formal-Jacobian facts; no
`ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` input remains on the direct path.
This is still only local finite Case 2 certificate packaging: no source
production of `Csucc`, successor chart or suffix production, coverage,
transition regularity, analytic Jacobian/volume-form theorem, normal
crossings, pole order, or RLCT extraction is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-continuing-certificate-without-chart-family-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-continuing-certificate-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-continuing-certificate-without-chart-family-a4.md`.

Latest A4/A0 Case 2 exponent-coordinate bridge:
`NormalCrossingInterface.lean` now contains
`AoyagiNormalCrossingExponentData.mem_activePairs_of_lossExp_eq_one` and
`AoyagiNormalCrossingExponentData.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq`.
`Case2FiniteExponentBridge.lean` contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge`,
`Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two`,
`Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair`, and
`Case2DisplayedContinuingA0ExponentCoordinateBridge.ratioAt_eq_centerCard_div_two`.
These prove that a supplied coordinate of a supplied A0 exponent datum is
active and has ratio `card(case2ResidualBlockPivotEntries n S J)/2`, assuming
the coordinate's loss exponent is `1` and its Jacobian/prior exponent is the
displayed Case 2 formal pivot exponent.  This is not construction of the
exponent datum or coordinate, not a global finite minimum/order theorem, not
chart production, not an analytic Jacobian/volume theorem, and not pole order
or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-a0-exponent-coordinate-bridge-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-a0-case2-exponent-coordinate-bridge.md`.
Review:
`threads/04-blow-up-certificate/review-case2-a0-exponent-coordinate-bridge-a4.md`.

Latest A4/A0 Case 2 exponent-minimum bridge:
`Case2FiniteExponentBridge.lean` now contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.exponentMinimum_eq_centerCard_div_two_of_forall_le`.
This theorem consumes the supplied Case 2/A0 coordinate bridge and an explicit
global active-ratio lower bound to prove
`D.exponentMinimum = card(case2ResidualBlockPivotEntries n S J)/2`.  It does
not prove the lower bound, construct `D` or `p`, prove an order count, produce
charts, prove analytic Jacobian/volume data, pole order, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-a0-exponent-minimum-bridge-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-a0-case2-exponent-minimum-bridge.md`.
Review:
`threads/04-blow-up-certificate/review-case2-a0-exponent-minimum-bridge-a4.md`.

Latest A4/A0 selected-entry finite normal-crossing microcertificate:
`SelectedEntryNormalCrossing.lean` now contains
`selectedEntryCenterSqFormalJacobianChartCertificate`,
`case2DisplayedCenterSqFormalJacobianChartCertificate`, and
`case2DisplayedCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`.
This constructs a one-chart `AoyagiNormalCrossingChartCertificate` for the
finite selected-entry center square-sum and formal pivot-first determinant.
The parameter is a finite-center value function, the chart residuals are
indexed by `center.erase pivot`, and the unique coordinate has `lossExp = 1`
and formal Jacobian/prior exponent `card(center.erase pivot)`.  The Case 2
displayed pivot specializes this to `case2ResidualBlockPivotEntries n S J`.
For the microcertificate's own one-coordinate exponent data, the existing
Case 2/A0 coordinate bridge is constructed rather than supplied.  This is not
global A0 chart production, chart coverage, source production, analytic
Jacobian/volume-form data, active-ratio lower bounds, pole order, or RLCT
extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-selected-entry-normal-crossing-microcertificate-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-normal-crossing-microcertificate.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-normal-crossing-microcertificate-a4.md`
passed after polish.

Latest A4 selected-entry local finite exponent minimum/order:
`SelectedEntryNormalCrossing.lean` now proves local finite exponent
consequences for the microcertificate's own one-coordinate exponent data:
the unique ratio is `center.card / 2`, the finite exponent minimum is
`center.card / 2`, every chart has minimum-coordinate count at most `1`, and
the finite exponent order is `1`.  The Case 2 specialization gives ratio and
minimum `card(case2ResidualBlockPivotEntries n S J) / 2` and order `1`.
This is not the global A0 minimum, not a global A0 chart-count/order theorem,
not chart production, not pole order, and not RLCT extraction.
Artifacts:
`threads/04-blow-up-certificate/reproduction-selected-entry-local-exponent-min-order-a4.md`
and
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-local-exponent-min-order.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-local-exponent-min-order-a4.md`
passed.

Latest A6 Case 2 finite-formula wrapper:
`Case2Theorem2FiniteExponentBridge.lean` now contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData`.
This theorem consumes the supplied Case 2/A0 coordinate bridge, an explicit
global active-ratio lower bound, a supplied equality from the Case 2
center-cardinality ratio to Theorem 2's displayed lambda formula, and a
supplied order equality to build
`AoyagiTheorem2FiniteExponentFormulaHypothesis`.  It does not prove those
supplied obligations, selected-width provenance, chart production, analytic
extraction, pole order, or RLCT.
Reproduction:
`threads/06-dln-translation/reproduction-case2-theorem2-finite-formula-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-case2-theorem2-finite-formula-bridge.md`.
Review:
`threads/06-dln-translation/review-case2-theorem2-finite-formula-bridge-a6.md`.

Latest A6 Case 2 ratio-count finite-formula wrapper:
`Case2Theorem2FiniteExponentBridge.lean` now also contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
This theorem replaces the raw supplied order equality by a supplied chart
whose `countInChartAtRatio` at the Case 2 ratio equals
`data.theorem2OrderFormula` and a supplied all-chart upper bound at that
ratio.  It does not prove those chart-count facts, the active-ratio lower
bound, chart production, analytic extraction, pole order, or RLCT.
Reproduction:
`threads/06-dln-translation/reproduction-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-case2-theorem2-ratio-count-finite-formula-bridge.md`.
Review:
`threads/06-dln-translation/review-case2-theorem2-ratio-count-finite-formula-bridge-a6.md`.

Latest A6 Case 2 chart-final wrapper:
`Case2Theorem2ChartFinalBridge.lean` now contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_centerCard_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
This theorem carries the supplied Case 2 finite ratio-count formula bridge
into `AoyagiTheorem2SuppliedChartFinalBoundary` after selected-width
provenance and chart-level extraction are supplied.  It is a small API handoff
only: no chart production, chart coverage, finite count proof, analytic
extraction theorem, pole order, or RLCT is proved.
Reproduction:
`threads/06-dln-translation/reproduction-case2-theorem2-chart-final-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-case2-theorem2-chart-final-bridge.md`.
Review:
`threads/06-dln-translation/review-case2-theorem2-chart-final-bridge-a6.md`.

Latest A4 Case 2 branchwise source-production re-audit:
`threads/04-blow-up-certificate/audit-case2-branchwise-successor-production-recheck-a4.md`
records three independent xhigh branch checks after crash recovery.  The
continuing, actual-width stopped, and row-exhausted stopped checks all found
that Aoyagi PDF pp. 19-22 prove local displayed `Q/P` algebra and
formula-level transported following rows, but not successor/source production.
The existing supplied-obligation consumers in `BlowupArithmetic.lean` remain
the safe Lean boundary.  No new Lean theorem is introduced by this audit.

Latest A4/A0 chart-certificate coordinate adapter:
`Case2FiniteExponentBridge.lean` now contains
`Case2DisplayedContinuingA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`.
It consumes supplied exponent equalities on a supplied
`AoyagiNormalCrossingChartCertificate Cnc` and constructs the existing
Case 2/A0 coordinate bridge for `Cnc.exponentData`.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-certificate-coordinate-adapter-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-certificate-coordinate-adapter.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-certificate-coordinate-adapter-a4.md`.
This is a projection adapter only: no chart certificate, coordinate
production, coverage, active-ratio lower bound, chart count, normal-crossing
production, pole order, or RLCT is proved.

Latest A6 Definition 3 source-data provenance wrappers:
`Definition3Bridge.lean` now contains
`AoyagiDefinition3SourceData.selected_strict_selectedReducedWidths`,
`AoyagiDefinition3SourceData.selectedWidth_le_pred_of_ceilData`,
`AoyagiDefinition3SourceData.htildeLowerNat_add_one_labelBounds_of_ceilData`,
`AoyagiDefinition3SourceData.lemma5Eq4_localData_of_ceilData`,
`AoyagiDefinition3SourceData.lemma5Eq5_labelBounds_of_ceilData`,
`AoyagiDefinition3SourceData.lemma5Eq3_localData_of_ceilData_and_slack`,
and
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_rankWidth`.
These consume supplied Definition 3 source data, a supplied ceiling datum, and
for the final aggregator an explicit source-range rank-width hypothesis.  They
do not construct selected cutpoints, prove rank-width hypotheses, prove Lemma
5 coverage/no-extra exactness, produce normal-crossing charts, prove pole
order, or extract an RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-data-local-wrappers-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-data-local-wrappers.md`.
Review:
`threads/06-dln-translation/review-definition3-source-data-local-wrappers-a6.md`.

Latest A6 Definition 3 source-data final-boundary handoff:
`Theorem2FinalAssembly.lean` now contains
`AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth`
and
`AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth`.
These use the supplied Definition 3 source data and explicit source-range
rank-width hypothesis to existentially produce the selected reduced-width
family and ceiling datum, then fill the selected-width provenance field of the
final-boundary structures.  The A0 extraction hypothesis and finite exponent
formula hypothesis for the produced data remain supplied.  They do not
construct selected cutpoints, prove rank-width hypotheses, prove
active-ratio/chart-count facts, produce charts, prove pole order, or extract
an RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-data-final-boundary-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-data-final-boundary.md`.
Review:
`threads/06-dln-translation/review-definition3-source-data-final-boundary-a6.md`.

Latest A4/A0 Case 1 exponent-coordinate bridge:
`Case1FiniteExponentBridge.lean` now contains
`Case1SelectedEntryExponentCoordinateBridge`,
`Case1SelectedEntryA0ExponentCoordinateBridge`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge.of_coord_exponents`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge.of_chartCertificate_coord_exponents`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_nonpivotCount_add_one_div_two`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge.exponentMinimum_eq_nonpivotCount_add_one_div_two_of_forall_le`,
`case1SelectedOldCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`,
and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localExponentCoordinateBridge`.
These consume supplied Case 1 selected-entry exponent equalities on a supplied
coordinate and prove active-pair, ratio, and conditional finite-minimum
bookkeeping.  The selected-old wrapper carries
`Case1SelectedOldUnitSuppliedChartFamilyBoundary` so the finite `Unit` token
does not stand alone as source provenance.  No A0 data or coordinate is
constructed, and no chart production, global lower bound, chart count, pole
order, or RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-a0-exponent-coordinate-bridge-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-a0-case1-exponent-coordinate-bridge.md`.
Review:
`threads/04-blow-up-certificate/review-case1-a0-exponent-coordinate-bridge-a4.md`.

Latest A6 Case 1 finite-formula and chart-final wrappers:
`Case1Theorem2FiniteExponentBridge.lean` now contains
`Case1SelectedEntryA0ExponentCoordinateBridge.theorem2CandidateRatio`,
`Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData`,
`Case1SelectedEntryA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2CandidateRatio`,
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData`,
and
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2FiniteExponentFormulaHypothesis_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
`Case1Theorem2ChartFinalBridge.lean` now contains
`Case1SelectedOldUnitA0ExponentCoordinateBridge.theorem2SuppliedChartFinalBoundary_of_forall_le_of_candidateRatio_eq_fromCeilData_of_countInChartAtRatio_eq_of_forall_le`.
These are supplied-obligation consumers only: they do not prove active-ratio
lower bounds, candidate-ratio/Theorem 2 lambda equality, chart-count facts,
selected-width provenance, chart production, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-case1-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/reproduction-case1-theorem2-chart-final-bridge-a6.md`.
Statement cards:
`threads/06-dln-translation/statement-card-a6-case1-theorem2-finite-formula-bridge.md`
and
`threads/06-dln-translation/statement-card-a6-case1-theorem2-chart-final-bridge.md`.
Reviews:
`threads/06-dln-translation/review-case1-theorem2-finite-formula-bridge-a6.md`
and
`threads/06-dln-translation/review-case1-theorem2-chart-final-bridge-a6.md`.

Latest A4/A0 source-chart selected-entry microcertificate adapter:
`SelectedEntryNormalCrossing.lean` now contains
`case2DisplayedCenterSqFormalJacobianChartCertificate.sourceChartPoint`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.chartMap_sourceChartPoint_eq`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.loss_sourceChartPoint_eq_centerSq`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.lossUnit_sourceChartPoint_eq`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPrior_sourceChartPoint_eq_det`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.loss_monomial_sourceChartPoint`,
and
`case2DisplayedCenterSqFormalJacobianChartCertificate.jacobianPrior_monomial_sourceChartPoint`.
These evaluate the local selected-entry microcertificate at the displayed
continuing Case 2 source chart point; they are not chart coverage, source
production, analytic Jacobian control, total loss control, global A0 normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-chart-selected-entry-microcertificate-adapter.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-chart-selected-entry-microcertificate-adapter-a4.md`.

Latest A4/A0 Case 1 source-chart selected-entry microcertificate adapter:
`SelectedEntryNormalCrossing.lean` now contains generic source-point lemmas
under `selectedEntryCenterSqFormalJacobianChartCertificate` and Case 1
specializations under
`case1SelectedOldCenterSqFormalJacobianChartCertificate` and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate`.  These
evaluate finite selected-entry source chart points inside the local
one-chart microcertificates and identify chart maps, finite losses, loss
units, formal determinant values, and monomial identities.  They are not
source production of the hidden old selected label, chart coverage,
transition regularity, analytic Jacobian control, total loss control, global
A0 normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-source-chart-selected-entry-microcertificate-adapter.md`.
Review:
`threads/04-blow-up-certificate/review-case1-source-chart-selected-entry-microcertificate-adapter-a4.md`.

Latest A4 Case 2 source-chart frontier package without chart-family input:
`BlowupArithmetic.lean` now contains
`sourceChartMap_postPivotNextSameStageProduct_withSourceFollowingFactorAndCorrectedPostData_withoutChartFamily`,
`sourceChartMap_continuingWeightedSourceFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`,
`sourceChartMap_continuingWeightedSuccFollowingPayload_withFiniteCenterIdeal_withoutChartFamily`,
and `sourceChartMap_frontierBoundaryPackages_withoutChartFamily`.
These construct the source-chart frontier implication package without
external `ChartRegular`, `TransitionRegular`, or
`Case2ResidualBlockChartFamilyBoundary` arguments.  Continuing fields are
proved from the finite displayed pivot identities, corrected selected-label
post-data, and finite center ideal `(u)`.  Stopped fields retain the previous
branch-implication APIs; the new package discharges their legacy abstract
chart-family boundary internally via
`Case2ResidualBlockChartFamilyBoundary.exists_trivial`.  The in-file consumer
`SourceProductionObligation.of_formulaSuccessor_transportTerminalRows` now
calls the chart-family-free package.  This does not produce source successor
data, suffix data, charts, transitions, coordinate-produced corrected
post-data, normal crossings, pole order, termination, or RLCT data; the
row-exhausted stopped branch remains transported-prefix rows, not original
rows.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-frontier-boundary-packages-without-chart-family-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-frontier-boundary-packages-without-chart-family.md`.
Review:
`threads/04-blow-up-certificate/review-case2-frontier-boundary-packages-without-chart-family-a4.md`.

Latest A4/A0 selected-entry local ratio chart count:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one`,
`case2DisplayedCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`,
`case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one`,
`case1SelectedOldCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`,
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one`,
and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.exponentData_minCountInChart_eq_one`.
These prove only the local one-chart `countInChartAtRatio = 1` and
`minCountInChart = 1` facts for the selected-entry microcertificates.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-ratio-chart-count-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-ratio-chart-count.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-ratio-chart-count-a4.md`.

Latest A4/A0 Case 2 local chart-certificate contribution:
`SelectedEntryNormalCrossing.lean` now proves
`case2DisplayedCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`.
The theorem bundles the generic Case 2 source bridge for the local
microcertificate's own exponent data, the source-bridge ratio
`card(case2ResidualBlockPivotEntries n S J) / 2`, local finite minimum,
local ratio-count `1`, local minimum-count `1`, and local finite order `1`.
It does not construct global A0 data, chart coverage, active-ratio lower
bounds, chart counts for the full normal-crossing family, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-local-chart-certificate-contribution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-local-chart-certificate-contribution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-local-chart-certificate-contribution-a4.md`.

Latest A4/A0 Case 1 local chart-certificate contributions:
`Case1FiniteExponentBridge.lean` now proves
`case1SelectedOldCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`
and
`case1DisplayedRowStripCenterSqFormalJacobianChartCertificate.localChartCertificateContribution_summary`.
Each theorem bundles the generic Case 1 selected-entry bridge for the local
microcertificate's own exponent data, local ratio
`(1 + J1 * (n(S+1)-J)) / 2`, local finite minimum, local ratio-count `1`,
local minimum-count `1`, and local finite order `1`.  They do not construct
global A0 data, selected-old source labels, chart coverage, active-ratio lower
bounds, chart counts for the full normal-crossing family, pole order, `theta`,
or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-local-chart-certificate-contribution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-local-chart-certificate-contribution.md`.
Review:
`threads/04-blow-up-certificate/review-case1-local-chart-certificate-contribution-a4.md`.

Latest A4/A0 selected-entry multi-chart certificate:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossExp_chart_zero`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_centerCard_div_two`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_centerCard_div_two_eq_one`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one`,
and
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one`.
The finite chart family is indexed by a supplied equivalence
`Fin center.card ≃ center`; chart `c` is the existing one-pivot selected-entry
certificate at the selected pivot.  Its finite exponent data has ratio
`center.card / 2`, chartwise ratio count `1`, finite minimum
`center.card / 2`, and finite order `1`.  It does not assert analytic atlas
coverage, transition regularity, analytic Jacobian/volume-form control, source
production, global active-ratio lower bounds, pole order, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-multi-chart-certificate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-multi-chart-certificate.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-multi-chart-certificate-a4.md`.

Latest A4/A0 selected-entry multi-chart source-point adapter:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartPoint`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartPoint_eq`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_centerSq`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_det`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint`,
and
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint`.
Each chart `c` delegates to the existing one-pivot source-point calculation
for pivot `chartEquiv c`.  This is finite presentation only and does not
assert atlas coverage, transition regularity, analytic Jacobian/volume-form
control, source production, global A0 normal-crossing data, pole order, or
RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-multi-chart-source-point-adapter-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-multi-chart-source-point-adapter.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-multi-chart-source-point-adapter-a4.md`.

Latest A4/A0 Case 1/Case 2 selected-entry multi-chart specializations:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate` and
Case 2 finite exponent consequences
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero_eq_selectedCoordinateCount_div_two`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero_eq_displayedFormalPivotExp`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_selectedCoordinateCount_div_two`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_selectedCoordinateCount_div_two_eq_one`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localChartFamilyCertificateContribution_summary`.
It also proves `case1CenterSqFormalJacobianChartFamilyCertificate` and Case 1
finite exponent consequences
`case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_ratioAt_chart_zero_eq_nonpivotCount_add_one_div_two`,
`case1CenterSqFormalJacobianChartFamilyCertificate.jacobianPriorExp_chart_zero_eq_nonpivotCount`,
`case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentMinimum_eq_nonpivotCount_add_one_div_two`,
`case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_countInChartAtRatio_nonpivotCount_add_one_div_two_eq_one`,
`case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_minCountInChart_eq_one`,
and
`case1CenterSqFormalJacobianChartFamilyCertificate.exponentData_exponentOrder_eq_one`; the Case 1 bridge and summary
`case1CenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart`
and
`case1CenterSqFormalJacobianChartFamilyCertificate.localChartFamilyCertificateContribution_summary`
live in `Case1FiniteExponentBridge.lean`.  The finite ratios/minima are
rewritten to `((prefixMinNat n S - J) * (n(S+1)-J)) / 2` in Case 2 and
`(1 + J1 * (n(S+1)-J)) / 2` in Case 1, with chartwise ratio count `1`,
minimum-coordinate count `1`, and order `1`.  The Case 2 arbitrary-chart
bridge is exponent-array only and uses equality of erased-center cardinalities
with the displayed pivot; it is not arbitrary-pivot source production.  This
checkpoint does not prove chart coverage, transition regularity, analytic
Jacobian data, global A0 lower bounds, pole order, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-multi-chart-specializations-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-case2-selected-entry-multi-chart-specializations.md`.
Review:
`threads/04-blow-up-certificate/review-case1-case2-selected-entry-multi-chart-specializations-a4.md`.

Latest A4 selected-entry finite chart coverage:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartCertificate.exists_oneChartPoint_chartMap_eq_value_of_pivot_ne_zero`,
`selectedEntryCenterSqFormalJacobianChartCertificate.exists_oneChartPoint_chartMap_eq_value_of_forall_eq_zero`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value_of_chart_pivot_ne_zero`,
and
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
These are finite inverse/coverage statements for the selected-entry chart
maps: nonzero pivot values are inverted by division by the pivot coordinate,
the zero value is covered by the zero source point, and the all-pivot family
covers every finite center value by choosing a nonzero coordinate as pivot
when one exists.  This does not assert analytic atlas coverage, transition
regularity, arbitrary-pivot Aoyagi source-coordinate formulas, source
production, analytic Jacobian/volume-form control, normal-crossing
certificate production, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-finite-chart-coverage-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-finite-chart-coverage.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-finite-chart-coverage-a4.md`.

Latest A4 Case 1/Case 2 selected-entry finite coverage:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`
and
`case1CenterSqFormalJacobianChartFamilyCertificate.exists_chartPoint_chartMap_eq_value`.
These specialize the generic finite selected-entry coverage theorem to the
two Aoyagi finite centers used by the all-pivot certificate wrappers.  They
are finite chart-map coverage statements only, not arbitrary-pivot source
production, analytic atlas coverage, transition regularity, source production
of successors, analytic Jacobian/volume-form control, normal-crossing
certificate production, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-finite-coverage-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case1-case2-selected-entry-finite-coverage.md`.
Review:
`threads/04-blow-up-certificate/review-case1-case2-selected-entry-finite-coverage-a4.md`.

Latest A4/A0 Case 2 selected-entry extraction handoff:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lambda_and_poleOrder_eq_selectedCoordinateCount_div_two_and_one_of_extractionHypothesis`.
It consumes an explicit chart-level `ExtractionHypothesis` for the concrete
Case 2 residual-block all-pivot finite selected-entry certificate and rewrites
the reported `lambda` to
`(((prefixMinNat n S - J) * (n(S+1)-J)) : Q) / 2`, with local finite
`poleOrder = 1`.  This is a handoff from supplied extraction to already
proved finite minimum/order arithmetic only.  It does not construct the
extraction hypothesis, analytic chart coverage, transition regularity,
arbitrary-pivot source production, global A0 data, Aoyagi Theorem 2 order
data, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-selected-entry-extraction-handoff-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-selected-entry-extraction-handoff.md`.
Review:
`threads/04-blow-up-certificate/review-case2-selected-entry-extraction-handoff-a4.md`.

Latest A4/A0 Case 2 all-pivot source-selected monomial/principalization adapter:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.centerIdeal_sourceSelectedChartMap_eq_span_singleton`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartPoint_eq_sourceSelectedCenterSq`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.lossUnit_sourceChartPoint_eq_sourceSelectedUnitFactor`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_sourceChartPoint_eq_sourceSelectedDet`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_monomial_sourceChartPoint_sourceSelected`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.jacobianPrior_monomial_sourceChartPoint_sourceSelected`.
These transport the generic selected-entry center-ideal principalization,
finite loss monomial identity, normalized center-square unit, formal
pivot-first determinant, and Jacobian/prior monomial identity to the
source-selected Case 2 chart map for each chart-selected residual-block pivot.
This is finite source-selected selected-entry algebra only, not arbitrary-pivot
source production, analytic chart coverage, transition regularity, analytic
Jacobian/volume control, global normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-all-pivot-source-selected-monomial-principalization-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-all-pivot-source-selected-monomial-principalization.md`.
Review:
`threads/04-blow-up-certificate/review-case2-all-pivot-source-selected-monomial-principalization-a4.md`.

Latest A4/A0 Case 2 chart-index source-selected boundary/QP bridge:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBoundary_of_chart_case2Succ_updateSelected`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedQP_sourceChartMap_of_chart_case2Succ_updateSelected`.
The first theorem instantiates the existing source-selected supplied-boundary
constructor at the pivot selected by the all-pivot finite chart index; the
second theorem applies the existing source-selected `Q/P` source-chart-map
projection to that boundary.  This is a finite chart-index adapter only.  It
does not prove arbitrary-pivot source production, analytic chart coverage,
transition regularity, chart-produced post-data, analytic Jacobian/volume-form
control, global normal crossings, pole order, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-source-selected-boundary-qp-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-source-selected-boundary-qp.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-source-selected-boundary-qp-a4.md`.

Latest A4 Case 2 source-selected finite chart production:
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.exists_sourceSelectedChartMap_eq_value`.
The generic theorem returns finite selected-entry coverage witnesses in the
source-point normal form `(c,u,residual)`, and the Case 2 theorem states the
result using `case2SourceSelectedChartMapOfMem` for the chart-selected pivot.
This is finite residual-center source-coordinate production only.  It does
not prove analytic atlas coverage, transition regularity, successor/suffix
production, global normal crossings, pole order, or RLCT extraction.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-finite-chart-production-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-finite-chart-production.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-finite-chart-production-a4.md`.

Latest A4 Case 2 source-selected finite transition:
`BlowupArithmetic.lean` now proves the generic finite overlap identity
`selectedEntryChartMap_transition_eq_of_target_normalized_ne_zero`.
Case 2 wrappers are
`case2SourceSelectedChartMapOfMem_transition_eq_of_target_normalized_ne_zero`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_transition_chartMap_eq_of_target_normalized_ne_zero`.
These theorems transform source normalized coordinates `x_i` to target
normalized coordinates `y_i = x_i/x_q` with selected variable
`u_q = u*x_q`, assuming `x_q != 0`.  The denominator is normalized, not the
finite center value `u*x_q`.  This is finite selected-entry chart-map algebra
only; it does not prove analytic transition regularity, chart coverage, Q/P
reduced-block transition, successor/suffix production, global normal
crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-finite-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-finite-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-finite-transition-a4.md`.

Latest A4 Case 2 source-selected Schur complement:
`BlowupArithmetic.lean` now proves
`pivotFirstSchurComplement_apply`,
`selectedEntryNormalizedMap_schurComplement_transition_mul_sq`, and
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_apply`.
These record the elementary Case 2 pp. 20-21 finite Schur-coordinate
calculation: the lower-right block after the selected-pivot `Q` operation is
entrywise `D_ij - x_i*y_j`, and on a selected-entry overlap the
denominator-cleared target Schur coordinate satisfies
`x_ab^2*z_ij = x_ab*x_ij - x_ib*x_aj` under `x_ab != 0`.  This is finite
matrix/field algebra only and does not prove chart coverage, analytic
transition regularity, successor/following-factor production, Jacobians,
normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-selected-schur-complement-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-selected-schur-complement.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-selected-schur-complement-a4.md`.

Latest A4 Case 2 chart-index Schur transition:
`BlowupArithmetic.lean` now proves
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq`,
and `SelectedEntryNormalCrossing.lean` proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelected_schurComplement_transition_mul_sq`.
These are finite supplied-pivot and chart-indexed wrappers for the
denominator-cleared target Schur coordinate identity under `x_ab != 0`.
The chart-indexed form obtains both pivot memberships from
`finsetSubtypeChartEquiv`; its off-pivot row/column indices are ambient `ℕ`
complements, so a residual-subtype consumer still needs a separate adapter.
This is not chart coverage, analytic transition regularity,
successor/following-factor production, Jacobians, normal crossings, pole
order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-schur-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-schur-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-schur-transition-a4.md`.

Latest A4 Case 2 residual-subtype Schur transition:
`BlowupArithmetic.lean` now proves
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq`.
This is the residual-row/residual-column subtype adapter for the
denominator-cleared source-selected Schur-overlap identity.  It matches the
lower-right block indexing of the source-selected `Q/P` theorem by converting
subtype complements back to ambient off-target complements and invoking
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_mul_sq`.
It is finite bookkeeping only: no successor/following-factor production,
analytic transition regularity, chart coverage, Jacobians, normal crossings,
pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-residual-subtype-schur-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-residual-subtype-schur-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-residual-subtype-schur-transition-a4.md`.

Latest A4 selected-entry transition point:
`SelectedEntryNormalCrossing.lean` now proves the generic and Case 2
finite transition-point constructors
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.chartMap_sourceChartTransitionPoint_eq_of_target_normalized_ne_zero`.
They construct the target selected-entry chart point with selected variable
`u*x_q` and residual coordinates `x_e/x_q`, and prove finite chart-map
equality under `x_q != 0`.  This is not analytic atlas coverage, transition
regularity, source production of successor/following-factor data, normal
crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-point-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-point.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-point-a4.md`.

Latest A4 chart-index residual-subtype Schur transition:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_mul_sq`.
For source and target chart indices of the Case 2 all-pivot selected-entry
certificate, it states the denominator-cleared Schur formula for the target
lower-right `Q/P` block indexed by residual-row and residual-column subtype
complements:
`x_ab^2*z_ij = x_ab*x_ij - x_ib*x_aj`, with source labels read as `i.1.1`
and `j.1.1`.  This is not analytic transition regularity, chart coverage,
source-displayed all-pivot atlas, successor/following-factor production,
normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-chart-index-residual-subtype-schur-transition-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-chart-index-residual-subtype-schur-transition.md`.
Review:
`threads/04-blow-up-certificate/review-case2-chart-index-residual-subtype-schur-transition-a4.md`.

Latest A4 selected-entry transition inverse:
`BlowupArithmetic.lean` now proves
`selectedEntryNormalizedMap_transition_eq_div_of_target_normalized_ne_zero`.
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_self`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_inverse_of_target_normalized_ne_zero`.
The inverse is a chart-point identity under normalized denominator `x_q != 0`,
not equality of arbitrary raw residual functions.  This is not analytic
transition regularity, chart coverage, source-displayed all-pivot atlas,
successor/following-factor production, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-inverse-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-inverse.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-inverse-a4.md`.

Latest A4 selected-entry transition cocycle:
`BlowupArithmetic.lean` now proves
`selectedEntryNormalizedMap_transition_target_ne_zero_of_source_ne_zero` and
`selectedEntryNormalizedMap_transition_transition_eq_div_of_ne_zero`.
`SelectedEntryNormalCrossing.lean` now proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_cocycle_of_target_normalized_ne_zero`.
For source, middle, and target pivots `p,q,r`, the nonzero hypotheses are the
source normalized coordinates `x_q != 0` and `x_r != 0`.  The two-step
transition has middle-to-target denominator `x_r/x_q` and agrees with the
direct source-to-target chart point.  The equality is chart-point level, not
ambient residual-function equality.  This remains finite selected-entry
coordinate algebra only: no analytic transition regularity, chart coverage,
source-displayed all-pivot atlas, successor/following-factor production,
normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-cocycle-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-cocycle.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-cocycle-a4.md`.

Latest A4 selected-entry Schur transition cocycle:
`BlowupArithmetic.lean` now proves
`selectedEntryNormalizedMap_schurComplement_transition_cocycle`,
`case2SourceSelectedNormalizedMapOfMem_schurComplement_transition_cocycle`,
and
`case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_cocycle`.
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_cocycle`.
These state route-independence of the finite target lower-right Schur entry on
normalized selected-entry triple overlaps, with a Case 2 chart-indexed
residual-subtype wrapper for the target `Q/P` block.  This remains finite
coordinate algebra only: no analytic transition regularity, chart coverage,
source-displayed all-pivot atlas, successor/following-factor production,
normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-schur-transition-cocycle-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-schur-transition-cocycle.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-schur-transition-cocycle-a4.md`.

Latest A5 base-value interval-membership cleanup:
`Lemma5SuppliedFamily.lean` now proves
`aoyagiLemma5BaseValue_mem_intervalValueSetNat_of_baseChainBounds`.  It turns
explicit base-chain bounds
`aoyagiHtildeLowerChain ell a M m <= baseH <= aoyagiHtildeUpperChain ell a M m`
plus the supplied interior-coordinate equality
`baseH(aoyagiLemma5InteriorCoord ell j hj) = baseValue j` into the recurring
membership
`baseValue j ∈ aoyagiHtildeIntervalValueSetNat ell a M m j`.
This is finite interval bookkeeping only.  It does not construct the base
chain from Aoyagi's printed Eq3/Eq4/Eq5, prove source-label legality,
no-extra coverage, injectivity, back-to-label coverage, terminal exactness,
pole order, normal crossings, or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-base-value-interval-membership-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-base-value-interval-membership.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-base-value-interval-membership-a5.md`.

Latest A5 terminal binary first-nonbase selector:
`Lemma5SuppliedFamily.lean` now defines
`aoyagiLemma5InteriorNonbaseCoordSet` and
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase`, and proves
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_mem_of_terminalH_binaryIncrementPrefixDelta`.
The selector scans `Icc 1 (ell-1)` for the least coordinate where the supplied
terminal chain differs from `baseValue`; if the scan is empty it returns
`none`.  Under terminal binary-prefix-delta hypotheses, the selected datum
belongs to `aoyagiLemma5CountDatumSet`.  This is a finite maps-to adapter, not
classifier/injection/no-extra exactness and not pole-order, normal-crossing,
or RLCT extraction.  Reproduction:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-binary-first-nonbase-selector-a5.md`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-terminal-binary-first-nonbase-selector.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-terminal-binary-first-nonbase-selector-a5.md`.

Latest A4 Case 2 transition-generated Q/P package:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero`.
For source chart data and target chart with normalized target coordinate
`d != 0`, it sets `targetU = u*d` and `targetResidual r = x_r/d`, then records
chart-map equality, the existing supplied target-pivot source-selected `Q/P`
identity, and the denominator-cleared residual-subtype lower-right Schur
formula for those same target data.  This is finite coordinate algebra only:
no analytic transition regularity, chart coverage, source-displayed all-pivot
atlas, chart-produced post-data, successor/following-factor production,
normal crossings, pole order, RLCT extraction, or printed-vector repair.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-qp-package-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-qp-package.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-qp-package-a4.md`.

Latest A4 Case 2 transition-generated displayed frontier:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.displayedChartIndex`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finsetSubtypeChartEquiv_displayedChartIndex`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_frontierBoundaryPackages_of_displayed_normalized_ne_zero`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingCertificate_of_displayed_normalized_ne_zero`.
These theorems transition arbitrary all-pivot source chart data to displayed
top-left data on the normalized displayed-coordinate overlap, keep finite
chart-map equality to the original source chart point, and instantiate the
existing displayed frontier/continuing packages at the generated data.  This
is finite selected-entry/source-frontier algebra only: no analytic transition
regularity, chart coverage, source-displayed all-pivot atlas, source-produced
successor or suffix data, normal crossings, pole order, or RLCT.  The
separate transition-generated substitution-block rewrite remains open.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-displayed-frontier-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-displayed-frontier.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-displayed-frontier-a4.md`.

Latest A4 Case 2 transition-generated substitution-block rewrite:
`BlowupArithmetic.lean` now proves
`case2SourceSelectedSubstitutionBlockOfMem_transition_eq_of_target_normalized_ne_zero`,
and `SelectedEntryNormalCrossing.lean` proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero`.
These theorems state the finite residual-block matrix equality
`Sub_q(u*d,x/d) = Sub_p(u,x)` for transition-generated selected-entry target
data on the normalized target-coordinate overlap.  This is finite
selected-entry substitution-block algebra only: no normalized-block equality,
target Schur-complement rewrite, analytic transition regularity, chart
coverage, source production, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-substitution-block-rewrite-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-substitution-block-rewrite.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-substitution-block-rewrite-a4.md`.

Latest A4 Case 2 transition-generated `Q/P` source-substitution package:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero`.
It combines the transition-generated target-pivot `Q/P` identity with the
substitution-block rewrite so that the left substituted residual block is
`Sub_p(u,x)` rather than `Sub_q(u*d,x/d)`.  The normalized block, Schur block,
successor weights, and transported following factor remain target-pivot data.
This is finite coordinate algebra only: no source production, analytic
transition regularity, chart coverage, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-qp-source-substitution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-qp-source-substitution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-qp-source-substitution-a4.md`.

Latest A4 Case 2 displayed `Q/P` source-substitution continuing handoff:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_QP_sourceSubstitution_frontierBoundaryPackages_of_displayed_normalized_ne_zero`
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_QP_sourceSubstitution_continuingCertificate_of_displayed_normalized_ne_zero`,
with the notation adapter
`case2DisplayedSourceSubstitutionBlock_eq_sourceSelectedSubstitutionBlockOfMem_displayed`.
These specialize the target-pivot `Q/P` source-substitution package to the
displayed chart `(J+1,J+1)` and bundle it with displayed frontier/continuing
finite data.  The reindexed next-source product with the source-side
substitution block remains the next target, not a proved theorem here.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-generated-displayed-qp-source-substitution-continuing-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-generated-displayed-qp-source-substitution-continuing.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-generated-displayed-qp-source-substitution-continuing-a4.md`.

Latest A4 Case 2 displayed reindexed product source-substitution:
`BlowupArithmetic.lean` now proves the generic supplied-block wrapper
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq`
for `Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlock`, and
`SelectedEntryNormalCrossing.lean` proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_sourceSubstitution_of_displayed_normalized_ne_zero`.
The theorem uses the displayed overlap denominator
`d = x_(J+1,J+1) != 0`, applies the displayed reindexed next-source product
to `targetU = u*d` and `targetResidual q = x_q/d`, and rewrites only the
left substitution block to the original source selected-entry substitution
block.  The post state, post-pivot residual block, and successor following
factor remain displayed transition-generated data.  This is finite
bookkeeping only: no source production, analytic transition regularity, chart
coverage, normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-reindexed-product-source-substitution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-reindexed-product-source-substitution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-displayed-reindexed-product-source-substitution-a4.md`.

Latest A4 selected-entry transition microcertificate evaluation:
`SelectedEntryNormalCrossing.lean` now proves transition-point evaluation
adapters for the finite selected-entry microcertificate:
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartTransitionPoint_eq_centerSq_of_target_normalized_ne_zero`,
`lossUnit_sourceChartTransitionPoint_eq`,
`jacobianPrior_sourceChartTransitionPoint_eq_det`,
`loss_monomial_sourceChartTransitionPoint_of_target_normalized_ne_zero`,
`jacobianPrior_monomial_sourceChartTransitionPoint`, and the Case 2
source-selected wrappers
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.loss_sourceChartTransitionPoint_eq_sourceSelectedCenterSq_of_target_normalized_ne_zero`,
`lossUnit_sourceChartTransitionPoint_eq_sourceSelectedUnitFactor`,
`jacobianPrior_sourceChartTransitionPoint_eq_sourceSelectedDet`,
`loss_monomial_sourceChartTransitionPoint_sourceSelected_of_target_normalized_ne_zero`,
and
`jacobianPrior_monomial_sourceChartTransitionPoint_sourceSelected`.
The source-facing loss statement uses the normalized target-coordinate
nonzero hypothesis and chart-map equality; the target unit and formal
determinant remain target-pivot data.  This is finite chart-certificate
algebra only: no analytic transition regularity, chart coverage, source
production, global normal crossings, pole order, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-transition-microcertificate-evaluation-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-transition-microcertificate-evaluation.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-transition-microcertificate-evaluation-a4.md`.

Latest A4 Case 2 supplied-successor reindexed product:
`BlowupArithmetic.lean` now adds
`Case2DisplayedReindexedNextSourceProductEqWithSubstitutionBlockAndCsucc`,
`sourceChartMap_reindexedNextSourceProduct_fromCase2SuccCorrectedPostData_of_substitutionBlock_eq_of_Csucc_eq`,
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.reindexedNextSourceProduct_of_substitutionBlock_eq`.
Given a supplied substitution-block equality and a supplied equality
`Csucc = case2DisplayedSourceSuccessorFollowingFactor ... C`, the displayed
reindexed product is restated with `Csucc` on the right-hand side.  This is a
finite congruence consumer only, not source production of `Csucc`, suffix
production, successor chart construction, transition regularity, normal
crossings, pole order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-supplied-successor-reindexed-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-supplied-successor-reindexed-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-supplied-successor-reindexed-product-a4.md`.

Latest A4 Case 2 transition supplied-successor reindexed product:
`SelectedEntryNormalCrossing.lean` now adds
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero`.
On the displayed normalized overlap, the theorem consumes explicit target data
`targetU = u*d`, `targetResidual q = x_q/d`, and a
`SourceProductionObligation` for those data.  It combines chart-map equality,
the displayed substitution-block transition rewrite to `Sub_p(u,x)`, and the
supplied-`Csucc` reindexed product consumer.  This is finite bookkeeping only:
no construction of the obligation or `Csucc`, no suffix/source production,
successor chart construction, transition regularity, normal crossings, pole
order, or RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-supplied-successor-reindexed-product-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-supplied-successor-reindexed-product.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-supplied-successor-reindexed-product-a4.md`.

Latest A4 Case 2 source-current stack substitution block:
`BlowupArithmetic.lean` now proves
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.continuing_sourceCurrentStack_suppliedCsucc_of_substitutionBlock_eq`.
It consumes a supplied equality from the displayed source substitution block
to a matrix `B` and rewrites the existing supplied-`Csucc` source-current
stack theorem with `B` in the lower-left block.  This is finite congruence
only: it does not construct `SourceProductionObligation`, construct or
source-produce `Csucc`, produce suffixes, construct successor charts, prove
transition regularity, chart coverage, normal crossings, pole order, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-source-current-stack-substitution-block-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-source-current-stack-substitution-block.md`.
Review:
`threads/04-blow-up-certificate/review-case2-source-current-stack-substitution-block-a4.md`.

Latest A4 Case 2 transition source-current stack supplied successor:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero`.
On the displayed normalized overlap, it consumes explicit target data, the
continuing guard, and a `SourceProductionObligation` for those target data.
It packages chart-map equality, rewrites only the displayed target
substitution block to the source selected block, and returns the full
supplied-`Csucc` source-current stack package.  The theorem keeps target
post-pivot and center/principalization outputs target-displayed.  It does not
construct the obligation, `Csucc`, `Cterm`, suffixes, successor charts,
transition regularity, chart coverage, normal crossings, pole order,
termination, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-source-current-stack-supplied-successor-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-source-current-stack-supplied-successor.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-source-current-stack-supplied-successor-a4.md`.

Latest A4 Case 2 displayed transition microcertificate contribution:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero`.
The theorem consumes a displayed normalized-coordinate nonzero hypothesis,
constructs the displayed continuing finite center-square/formal-Jacobian
certificate for transition-generated displayed data, and bundles finite
loss/unit/formal-determinant monomial identities with the all-pivot wrapper's
local ratio/minimum/count/order summary.  This is finite selected-entry
chart-certificate plumbing only; Aoyagi prints the displayed chart, while the
all-pivot source chart is our finite wrapper.  It is not source production,
analytic transition regularity, coverage, normal crossings, pole order, or
RLCT extraction.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-displayed-transition-microcertificate-contribution-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-displayed-transition-microcertificate-contribution.md`.
Review:
`threads/04-blow-up-certificate/review-case2-displayed-transition-microcertificate-contribution-a4.md`.

Latest A4 Case 2 constructed source following factor with old top rows:
`BlowupArithmetic.lean` now proves a finite source-coordinate constructor
with arbitrary old-top rows `Cold` and arbitrary displayed residual-column
data `Csrc`.  The constructor recovers both projections, transports generic
residual data to `Q^-1*Csrc`, and in the special case `Csrc=Q*Cprime`
recovers the free chart coordinate `Cprime`.  The row-reindexing wrappers
identify the constructed current source block as `[Cold; Q*Cprime]` and the
formula-level successor block as `[Cold; Cprime]`.  This is a bounded
constructed-coordinate slice only: no `SourceProductionObligation`,
successor chart family, suffix production, recurrence/exponent post-data,
transition regularity, coverage, normal crossings, pole order, termination,
or RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-source-following-factor-with-old-top-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-source-following-factor-with-old-top.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-source-following-factor-with-old-top-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` source-current stack:
`BlowupArithmetic.lean` now proves
`sourceChartMap_continuingOldTopSourceSuffixConstructedWithOldTopFromCprimeStack_withoutChartFamily`.
It specializes the upstream continuing source-current stack theorem to the
constructed source following factor with arbitrary old-top rows and free
displayed `Cprime`.  The current stack contains the reconstructed old residual
block `case2DisplayedPaperConstructedFollowingFactor ... Cprime`; the
successor stack contains `Cprime`.  The suffix is supplied, and the row
operation witness remains existential.  This proves no source production,
suffix production, chart coverage, transition regularity, normal crossings,
pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-source-current-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-source-current-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-source-current-stack-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` terminal rows:
`BlowupArithmetic.lean` now proves
`case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_oldRow`,
`case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_pivotRow`,
`case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_submatrix_terminalRowEquiv`,
`case2DisplayedSourceTerminalCprimeCandidate_constructedWithOldTopFromCprime_submatrix_terminalRowEquiv`,
`SuppliedTerminalCprimeBridge.of_constructedWithOldTopFromCprime`, and
`case2DisplayedSourceTerminalProductReindexedCandidate_constructedWithOldTopFromCprime_eq_weight_mul_terminalStack_mul`.
The result specializes terminal transported rows for the constructed
old-top/free-`Cprime` source following factor to
`[Cold; case2DisplayedFreeCprimeTop ... Cprime]`, and consumes the explicit
terminal matrix in the stopped source-row product candidate.  This is finite
terminal-row and product-form bookkeeping only: no source-produced
`C'^(S+1)`, terminal chart data, suffix production, transition regularity,
coverage, normal crossings, pole order, termination, or RLCT is proved.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-terminal-rows-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-terminal-rows.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-terminal-rows-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` terminal prefix:
`BlowupArithmetic.lean` now proves
`case2DisplayedSourceTerminalCprimePrefixCandidate_constructedWithOldTopFromCprime_eq_terminalStackPrefix`
and
`case2DisplayedSourceTerminalProductPrefixCandidate_constructedWithOldTopFromCprime_eq_weight_mul_terminalStackPrefix_mul`.
These are finite consumers of the explicit constructed source-row terminal
matrix `[Cold; top(Cprime)]` under the stopped-prefix row equivalence.  No
actual-width original-row collapse, source production, terminal chart
construction, suffix production, transition regularity, coverage, normal
crossings, pole order, termination, or RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-terminal-prefix-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-terminal-prefix.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-terminal-prefix-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` terminal-prefix source suffix:
`BlowupArithmetic.lean` now proves
`exists_sourceOldTopSourceSuffix_entryIdeal_eq_constructedOldTopFromCprimeTerminalPrefixProduct_of_not_next_cont`.
This is the stopped terminal-prefix source-suffix entry-ideal consumer
specialized to the constructed old-top/free-`Cprime` source following factor.
The source side uses `[Cold; Q*Cprime]`; the terminal side uses the double
reindexing of `[Cold; top(Cprime)]` and the supplied raw
`sourceSuffixProduct`.  It proves no actual-width original-row collapse,
source production, suffix construction, chart construction, transition
regularity, coverage, normal crossings, pole order, termination, or RLCT.
Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-terminal-prefix-source-suffix-a4.md`.

Latest A4 Case 2 constructed old-top `Cprime` source-production obligation:
`BlowupArithmetic.lean` now proves
`case2DisplayedSourceTerminalTransportedRows_constructedWithOldTopFromCprime_eq_terminalStack`
and
`Case2DisplayedSuppliedChartFamilyBoundary.SourceProductionObligation.of_constructedWithOldTopFromCprime_terminalStack`.
It transports the canonical formula-level source-production obligation to the
explicit source-row reindexing of `[Cold; top(Cprime)]` for the constructed
old-top/free-`Cprime` source following factor.  This is a finite obligation
package only: no source production, suffix construction, chart construction,
transition regularity, coverage, normal crossings, pole order, termination, or
RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-constructed-oldtop-cprime-source-production-obligation-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-constructed-oldtop-cprime-source-production-obligation.md`.
Review:
`threads/04-blow-up-certificate/review-case2-constructed-oldtop-cprime-source-production-obligation-a4.md`.

Latest A4 Case 2 transition constructed old-top `Cprime` source-current stack:
`SelectedEntryNormalCrossing.lean` now proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_continuingSourceCurrentStack_constructedWithOldTopFromCprime_sourceSubstitution_of_displayed_normalized_ne_zero`.
On the displayed normalized overlap, it constructs the
`SourceProductionObligation` for arbitrary old-top rows `Cold`, free displayed
`Cprime`, and supplied suffix matrices `Ctail`, then consumes the existing
supplied-`Csucc` transition stack theorem.  It keeps the current following
factor as the constructed `[Cold; Q*Cprime]` data, keeps the successor as the
formula-level `case2DisplayedSourceSuccessorFollowingFactor ... C`, and keeps
the constructed obligation's terminal matrix as the source-row reindexing of
`[Cold; top(Cprime)]`.  This is not source production, suffix construction,
chart construction, transition regularity, coverage, normal crossings, pole
order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-case2-transition-constructed-oldtop-cprime-source-current-stack-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-case2-transition-constructed-oldtop-cprime-source-current-stack.md`.
Review:
`threads/04-blow-up-certificate/review-case2-transition-constructed-oldtop-cprime-source-current-stack-a4.md`.

Latest A4 selected-entry analytic atlas boundary:
`SelectedEntryNormalCrossing.lean` now defines
`SelectedEntryAnalyticAtlasBoundary` and the projection
`SelectedEntryAnalyticAtlasBoundary.exponentData`.  The structure carries a
supplied `AoyagiNormalCrossingChartCertificate` and separate supplied fields
for coverage, chart regularity, transition regularity, unit regularity,
analytic Jacobian compatibility, source production, and branch termination.
This is a boundary interface only; no constructor from finite selected-entry
certificates, trivial chart-family boundaries, or `SourceProductionObligation`
is provided, and no coverage, regularity, normal-crossing, termination, pole
order, or RLCT theorem is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-boundary-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-boundary.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-boundary-a4.md`.

Latest A4 selected-entry analytic atlas final socket:
`SelectedEntryAnalyticAtlasFinalBridge.lean` proves
`SelectedEntryAnalyticAtlasBoundary.theorem2SuppliedChartFinalBoundary_of_selectedWidths_eq_reduced_of_extractionHypothesis_of_finiteExponentFormula`.
It fills `AoyagiTheorem2SuppliedChartFinalBoundary B.chartCertificate ...`
from selected-width provenance, explicit chart-level extraction, and an
explicit finite Theorem 2 exponent formula over `B.exponentData`.  This is a
projection/adapter only; no analytic atlas, extraction theorem, finite formula,
source production, pole order, termination, or RLCT is proved.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-final-socket-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-final-socket.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-final-socket-a4.md`.

Latest A4 selected-entry coordinate postdata:
`SelectedEntryNormalCrossing.lean` proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq`,
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq`,
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartPoint_eq_sourceSelected`,
and
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.coord_sourceChartTransitionPoint_eq_sourceSelected`.
The source-point coordinate is `u`; the transition-generated target-point
coordinate is `u` times the source chart's normalized target entry.  Aoyagi's
source support is the displayed top-left Case 2 chart on PDF pp. 19-22; the
all-pivot statement is Lean's finite selected-entry generalization.  This is
coordinate postdata only, not an overlap theorem without denominator
nonvanishing, and not chart coverage, transition regularity, source
production, analytic Jacobian control, normal crossings, pole order,
termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-coordinate-postdata-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-coordinate-postdata.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-coordinate-postdata-a4.md`.

Latest A4 selected-entry source-point coverage with coordinate:
`SelectedEntryNormalCrossing.lean` proves
`selectedEntryCenterSqFormalJacobianChartFamilyCertificate.exists_sourceChartPoint_chartMap_eq_value_and_coord_zero_eq`.
For a generic finite selected-entry all-pivot family, every finite center
value has a source-chart witness whose chart map is that value and whose
unique coordinate `(0 : Fin 1)` is the selected variable `u`.  The theorem is
a generic finite package; the Case 1 wrapper was not added because it is a
thin specialization with no direct consumer yet.  This is not analytic atlas
coverage, transition regularity, source production, Jacobian control, normal
crossings, pole order, termination, or RLCT.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-source-point-coverage-coordinate-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-source-point-coverage-coordinate.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-source-point-coverage-coordinate-a4.md`.

Latest A6/A2 source-range rank-width bridge:
`Definition3RankWidthBridge.lean` proves
`paperTotalMap_rank_le_layer_finrank`,
`paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth`, and
`AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_sourceRankStratum`.
It uses the through-subspace theorem for the reversed chain to bound the total
product rank by each layer finrank, rewrites through the explicit convention
`H(k+1)=finrank K (W k)`, and feeds the result into the existing Definition 3
source-data ceiling constructor.  It proves no selected-cutpoint existence,
Definition 3 source-data existence, exact-rank openness, finite exponent
formula, normal crossings, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-range-rank-width-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-range-rank-width.md`.
Review:
`threads/06-dln-translation/review-definition3-source-range-rank-width-a6.md`.

Latest A6 source-rank final handoff:
`Theorem2SourceRankFinalBridge.lean` proves
`AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum`
and
`AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum`.
`Theorem2SourceRankEq5Bridge.lean` proves
`AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`
and
`AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload`.
These wrappers specialize `L=N`, use the A2 source-rank stratum and dimension
convention to produce the source-range rank-width hypothesis, and call the
existing final/Eq5 `_of_rankWidth` wrappers.  They prove no selected-cutpoint
existence, Definition 3 source-data existence, exact-rank openness, Eq5
family construction, Lemma 5 exactness, finite formula, chart production,
normal crossings, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-rank-final-handoff-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-rank-final-handoff.md`.
Review:
`threads/06-dln-translation/review-definition3-source-rank-final-handoff-a6.md`.

Latest A6 Definition 3 selected/nonselected redundancy:
`Definition3Bridge.lean` proves
`aoyagiDefinition3_selected_lt_of_selectedStrict_nonselectedLe` and
`AoyagiDefinition3SourceData.of_selectedStrict_nonselectedLe_rankWidth`.
The first is the elementary integer implication from strict selected and
nonselected upper inequalities plus selected nonnegativity; the second uses
source-range rank-width to derive that nonnegativity at selected cutpoints and
therefore constructs `AoyagiDefinition3SourceData` without a separately
supplied `selected_lt_nonselected` field.  It still supplies selected
cutpoints, cutpoint bounds, rank-width, strict selected inequalities, and
nonselected upper inequalities.  It proves no selected-cutpoint existence,
Definition 3 source-data existence from arbitrary dimensions, Lemma 5 family
realisation, chart production, normal crossings, pole order, or RLCT.
Reproduction:
`threads/06-dln-translation/reproduction-definition3-selected-lt-from-nonselected-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-selected-lt-from-nonselected.md`.
Review:
`threads/06-dln-translation/review-definition3-selected-lt-from-nonselected-a6.md`.

Latest A6 Definition 3 Eq5 `hsource` bridge:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.selected_strict_of_eq_selectedReducedWidths`.
`Lemma5Eq5TerminalOrderDefinition3Bridge.lean` proves
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_eq_theorem2OrderFormula_of_eq5EndpointFamily_branchCoordVal_blockWidth_cardSqueeze_of_definition3SourceData`.
The first theorem rewrites Definition 3 source data's strict selected-width
field along `m = aoyagiSelectedReducedWidths H r C`; the second passes that
derived inequality to the existing Eq5 endpoint-family block-width
cardinal-squeeze theorem.  The Eq5 actual-width/block hypothesis, endpoint
payloads, injectivity, branch synchronisation, and terminal data remain
explicit.  It proves no selected-cutpoint existence, Definition 3 source-data
existence, Eq5 construction, Lemma 5 exactness, chart production, normal
crossings, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-eq5-hsource-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-eq5-hsource-bridge.md`.
Review:
`threads/06-dln-translation/review-definition3-eq5-hsource-bridge-a6.md`.

Latest A6 Definition 3 Eq5 `hlast` bridge:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.lastPoint_le`.  The Definition 3-specific Eq5
terminal-order wrapper in `Lemma5Eq5TerminalOrderDefinition3Bridge.lean` now
uses that theorem instead of taking `hlast : C.point (N+1) <= L+1` as an
extra input.  Generic Eq5 APIs still keep `hlast` explicit.  It proves no
selected-cutpoint existence, Definition 3 source-data existence, Eq5
construction, Lemma 5 exactness, chart production, normal crossings, pole
order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-eq5-hlast-bridge-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-eq5-hlast-bridge.md`.
Review:
`threads/06-dln-translation/review-definition3-eq5-hlast-bridge-a6.md`.

Latest A6 Definition 3 arbitrary source-data obstruction:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.not_exists_widths_one_two_hundred`.  For the
fixed profile `L=2`, `r=0`, `H(1)=1`, `H(2)=2`, `H(3)=100`, no `ell,C`
satisfy `AoyagiDefinition3SourceData 2 ell H 0 C`.  The proof uses only the
printed Definition 3 inequalities: strict cutpoints force `ell=1` or `ell=2`;
`ell=1` makes the printed nonselected coefficient `ell-1` vanish, and
`ell=2` fails the selected strict inequality at width `100`.  This is a
diagnostic guardrail against arbitrary selected-cutpoint/source-data
existence, not a corrected Definition 3, classification theorem, Eq5
construction, Lemma 5 exactness, chart result, pole-order result, or RLCT.
Reproduction:
`threads/06-dln-translation/reproduction-definition3-source-data-obstruction-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-source-data-obstruction.md`.
Review:
`threads/06-dln-translation/review-definition3-source-data-obstruction-a6.md`.

Latest A6 Definition 3 `ell=1` nonselected obstruction:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one_rankWidth`.
For `S : AoyagiDefinition3SourceData L 1 H r C`, source-range rank-width
nonnegativity forces every source-range reduced-width value to lie in the
selected value set.  This records the general `ell=1` obstruction behind the
`1,2,100` diagnostic and remains only a necessary condition for supplied
source data.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-ell-one-nonselected-obstruction-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-ell-one-nonselected-obstruction.md`.
Review:
`threads/06-dln-translation/review-definition3-ell-one-nonselected-obstruction-a6.md`.

Latest A6 Definition 3 `ell=1` automatic ceiling and `L=2`
repeated-positive formula package:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3SourceData.exists_ell_one_selectedPair_theorem2Formula_of_cover_rankWidth`
and
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_rankWidth`.
For an exposed `ell=1` selected pair, Lean constructs Definition 3 ceiling data
directly with `ceilWidth=u+v` and `aParam=1`, then proves order `1`, pair sum
`u*v`, and finite lambda `regularTerm+u*v/2`.  The repeated-positive theorem
consumes positive widths, a repeated-equality disjunction, and source-range
rank-width; it chooses an `ell=1` selected pair by cases and returns it
existentially.  Reproductions:
`threads/06-dln-translation/reproduction-definition3-ell-one-automatic-ceil-formula-a6.md`
and
`threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-positive-formula-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-repeated-positive-formula.md`.
Review:
`threads/06-dln-translation/review-definition3-l-eq-two-repeated-positive-formula-a6.md`.
The older
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated_remainder_rankWidth`
remains compatibility only.  Nonclaims: no unique/canonical selected pair, no
source-rank wrapper, no final socket, no Eq5 payloads, no chart production, no
pole-order theorem, and no RLCT theorem.

Latest A6 Definition 3 `L=2` triangle parity formula package:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth`
and
`AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth`.
For total selected width `T=w1+w2+w3`, the odd branch supplies
`T=2*(T/2)+1`, hence `ceilWidth=T/2+1`, `aParam=1`, order `2`; the even branch
uses `T=2*(T/2-1)+2`, hence `ceilWidth=T/2`, `aParam=2`, order `1`.  Both
theorems retain the all-source cutpoint/source-data construction,
selected-width provenance, selected pair sum, and finite Theorem 2 lambda
formula.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-l-eq-two-triangle-parity-formula-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-triangle-parity-formula.md`.
Review:
`threads/06-dln-translation/review-definition3-l-eq-two-triangle-parity-formula-a6.md`.
Nonclaims: no `L>2` classification, no combined repeated/triangle theorem, no
source-rank wrapper, no final socket, no Eq5 payloads, no chart production, no
pole-order theorem, and no RLCT theorem.

Latest A6 Definition 3 equal-width source data:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.exists_consecutive_of_constant_reducedWidth_pos`.
If all source-range reduced widths are the same positive integer `w`, then the
consecutive cutpoints `C.cut j = j.val+1` give
`AoyagiDefinition3SourceData L L H r C`.  This formalizes Aoyagi's
equal-width example `ell=L`; it is not arbitrary selected-cutpoint existence,
not a correction of Definition 3, not Eq5 construction, not Lemma 5 exactness,
and not chart production, normal crossings, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-equal-width-source-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-source-data.md`.
Review:
`threads/06-dln-translation/review-definition3-equal-width-source-data-a6.md`.

Latest A6 Definition 3 equal-width ceiling data:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.sourceRangeRankWidth_of_constant_reducedWidth`
and
`AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_constant_reducedWidth_pos`.
The helper derives source-range rank-width from constant Nat-valued
integer reduced width.  The package theorem then produces consecutive
cutpoints, equal-width source data, selected reduced widths, a Definition 3
ceiling datum, Nat-width rewrites, nonnegativity, strict selected inequalities,
selected-width upper bounds, and `m j = w`.  This is equal-width plumbing only,
not arbitrary source-data existence, Eq5 construction, finite formula proof,
chart production, pole order, or RLCT.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-equal-width-ceil-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-ceil-data.md`.
Review:
`threads/06-dln-translation/review-definition3-equal-width-ceil-data-a6.md`.

Latest A6 Definition 3 positive-remainder ceiling data:
`Definition3Bridge.lean` now proves
`AoyagiDefinition3CeilData.ofSelectedSumPositiveRemainder`.  A supplied
decomposition

```text
sum_j m_j = ell * ceilPred + a,        0 < a <= ell
```

constructs an `AoyagiDefinition3CeilData` with
`ceilWidth = ceilPred + 1` and `aParam = a`.  This is the finite arithmetic
primitive behind the equal-width explicit constructor, but no source-facing
wrapper is added in this slice.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-positive-remainder-ceil-data-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-positive-remainder-ceil-data.md`.
Review:
`threads/06-dln-translation/review-definition3-positive-remainder-ceil-data-a6.md`.

Latest A6 Definition 3 `L=2` repeated-width classification:
`Definition3Bridge.lean` now proves the rank-width-free `ell=1` necessary
condition
`AoyagiDefinition3SourceData.reducedWidth_mem_selectedValueSet_of_ell_eq_one`,
the `ell=1` cover constructor
`AoyagiDefinition3SourceData.of_ell_eq_one_selectedValueSet_covers`, the
positive repeated `ell=1` constructor, and the full
`AoyagiDefinition3SourceData.exists_sourceData_iff_repeatedPositive_or_triangle_of_L_eq_two`.
This closes the finite `L=2` source-data classification: existence is
equivalent to repeated-positive widths or the all-source triangle
inequalities.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-l-eq-two-repeated-width-classification-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-l-eq-two-repeated-width-classification.md`.
Review:
`threads/06-dln-translation/review-definition3-l-eq-two-repeated-width-classification-a6.md`.

Latest A4 selected-entry analytic atlas Case 2 source final socket:
`SelectedEntryAnalyticAtlasCase2FinalBridge.lean` proves
`SelectedEntryAnalyticAtlasBoundary.theorem2SuppliedChartFinalBoundary_of_case2DisplayedA0SourceProduction`.
It also defines the data/predicate pair
`SelectedEntryCase2DisplayedA0SourceProductionData` and
`SelectedEntryCase2DisplayedA0SourceProduction`.  The theorem requires a
displayed continuing Case 2 source-chart center-square/formal-Jacobian
certificate and A0 exponent-coordinate bridge in `B.source_production`, then
keeps selected-width provenance, chart extraction, center-card/lambda equality,
active-ratio lower bound, chart-count equality, and chart-count upper bound as
explicit hypotheses.  It returns the supplied chart-final Theorem 2 boundary
for `B.chartCertificate`.  Reproduction:
`threads/04-blow-up-certificate/reproduction-selected-entry-analytic-atlas-case2-source-final-socket-a4.md`.
Statement card:
`threads/04-blow-up-certificate/statement-card-a4-selected-entry-analytic-atlas-case2-source-final-socket.md`.
Review:
`threads/04-blow-up-certificate/review-selected-entry-analytic-atlas-case2-source-final-socket-a4.md`.

Latest A2 chart-local suffix-state field continuity:
`ChartTopology.lean` proves
`continuousAt_chartLocalSuffixState_step_fields` and
`continuousAt_chartLocalSuffixState_suffixState_fields`.  These theorems
extend the existing `B` continuity API to fieldwise continuity of `L`, `B`,
`Ctop`, and `D`, while carrying the basepoint `IsUnit Ctop.det` invariant
needed for the inverse in the `L` update.  The suffix theorem uses the
existing recursive determinant-chart hypotheses and returns the fieldwise
continuity package for every `i <= j`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-chart-local-suffix-state-field-continuity.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-chart-local-suffix-state-field-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-chart-local-suffix-state-field-continuity.md`.

Latest A2 product-reduction triangular coordinate chart:
`ProductReduction.lean` now proves the one-step p. 13 triangular
coordinate-change package:
`ProductReductionStepRawCoordinates`,
`ProductReductionStepChartCoordinates`,
`ProductReductionStepRawCoordinates.detChart`,
`ProductReductionStepChartCoordinates.detChart`,
`ProductReductionStepRawCoordinates.toChart`,
`ProductReductionStepChartCoordinates.toRaw`,
`ProductReductionStepRawCoordinates.detChart_toChart`,
`ProductReductionStepChartCoordinates.detChart_toRaw`,
`productReductionStepCoordinate_left_inverse`, and
`productReductionStepCoordinate_right_inverse`.  This packages the formulas
`Ctop=C1*A1`, `F2=-(A1⁻¹*A2)`,
`F3=F3old-D*A3*(C1*A1)⁻¹`, and `C=A4-A3*A1⁻¹*A2`, with inverse formulas that
retain passive `D`, `A1`, and `A3` and never invert `D`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-reduction-triangular-coordinate-chart.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-reduction-triangular-coordinate-chart.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-reduction-triangular-coordinate-chart.md`.
Nonclaims: no analytic coordinate-chart construction, exact-rank/source-rank
openness, block-difference wrapper, regular-suspension construction,
analytic germ transport, coverage, Jacobian compatibility, normal crossings,
pole order, or RLCT extraction.

Latest A2 product-reduction step product-difference wrapper:
`ProductReduction.lean` now proves
`productReductionStepCoordinate_triangularBlockProduct` and
`productReductionStepCoordinate_productDifference`.  The first theorem turns
the prior triangular product hypothesis
`[I 0; F3old I] T = [C1 0; 0 D] [A1 A2; A3 A4]` into the next diagonal
product using `x.toChart`; the second applies
`triangularBlockProductDifference_fromBlocks_indexed` to get the signed block
with lower-right correction `D*C - F3*F2`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-reduction-step-product-difference-wrapper.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-reduction-step-product-difference-wrapper.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-reduction-step-product-difference-wrapper.md`.
Nonclaims: no suffix-state adapter, no analytic coordinate-chart construction,
no ideal transport, no normal crossings, pole order, or RLCT extraction.

Latest A2 suffix-state step coordinate adapter:
`ProductReduction.lean` now proves the `ChartLocalSuffixState` adapter:
`stepRawCoordinates`, `stepRawCoordinates_detChart`,
`stepRawCoordinates_toChart_Ctop`, `stepRawCoordinates_toChart_F2`,
`stepRawCoordinates_toChart_C`, `stepRawCoordinates_toChart_D_mul_C`,
`stepRawCoordinates_toChart_F3_of_L_eq_lowerUnitriangular`,
`stepRawCoordinates_priorProduct`,
`stepRawCoordinates_triangularBlockProduct`, and
`stepRawCoordinates_productDifference`.  This connects
`S.BlockDiagonal P hpj` plus a lower-unitriangular witness for `S.L` to the
p. 13 coordinate/product-difference wrappers.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-suffix-state-step-coordinate-adapter.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-suffix-state-step-coordinate-adapter.md`.
Review:
`threads/03-block-product-reduction/review-a2-suffix-state-step-coordinate-adapter.md`.
Nonclaims: this arbitrary-state adapter does not itself choose the actual
recursive `suffixState`; that specialization is recorded in the next A2 slice.
No analytic chart, ideal transport, normal crossings, pole order, or RLCT
extraction is proved here.

Latest A2 suffix-state step coordinate specialization:
`ProductReduction.lean` now proves
`ChartLocalSuffixState.suffixState_stepRawCoordinates_triangularBlockProduct`
and
`ChartLocalSuffixState.suffixState_stepRawCoordinates_productDifference`.
They specialize the arbitrary suffix-state adapter to the actual recursive
`suffixState E j p.succ hpj`, choose the lower-unitriangular witness for `S.L`
from `suffixState_L_eq_lowerUnitriangular`, and produce the p. 13 triangular
product and signed product-difference identities for
`P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj)`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-suffix-state-step-coordinate-specialization.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-suffix-state-step-coordinate-specialization.md`.
Review:
`threads/03-block-product-reduction/review-a2-suffix-state-step-coordinate-specialization.md`.
Nonclaims: no derivation of `S.BlockDiagonal` from global chart hypotheses,
no analytic chart, no ideal transport, no normal crossings, pole order, or
RLCT extraction.

Latest A2 regular-suspension coordinate map source data:
`RegularSuspensionCoordinates.lean` now defines the Pi-valued coordinate maps
`paperEndpointFixedBaseRegularBlockCoordinateMap`,
`paperEndpointFixedBaseResidualBlockCoordinateMap`, and
`paperEndpointFixedBaseProductDifferenceCoordinateMap`, collecting the existing
p. 13 scalar coordinate fields from the fixed-base suffix state.  It also
proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.regularBlockCoordinateMap_centered_continuousAt`,
`PaperEndpointFixedBaseRegularCoordinateSourceData.residualBlockCoordinateMap_centered_continuousAt`,
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.productDifferenceCoordinateMap_centered_continuousAt`.
Each theorem says the map is zero at the base point and continuous there.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-regular-suspension-coordinate-map-source-data.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-regular-suspension-coordinate-map-source-data.md`.
Review:
`threads/03-block-product-reduction/review-a2-regular-suspension-coordinate-map-source-data.md`.
Nonclaims: product-topology coordinate-family packaging only; no analytic
chart, local inverse, source-rank openness, analytic ideal transport,
coverage, Jacobian compatibility, normal crossings, pole order, or RLCT.

Latest A2 cleaned coordinate square-sum:
`RegularSuspensionCoordinates.lean` now proves the finite square-sum split for
the cleaned p. 13 coordinate family.  Lean names are
`aoyagiCoordinateSquareSum`, `aoyagiCoordinateSquareSum_sumElim`,
`AoyagiProductDifferenceCoordinateIndex.coordinateSquareSum_eq_regular_add_residual`,
`paperEndpointFixedBaseProductDifferenceCoordinateMap_eq_sumElim`, and
`paperEndpointFixedBaseProductDifferenceCoordinateMap_squareSum_eq_regular_add_residual`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-cleaned-coordinate-square-sum.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-cleaned-coordinate-square-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-cleaned-coordinate-square-sum.md`.
Nonclaims: no equality with the literal signed/corrected p. 13 Frobenius
loss, no analytic generator transport, no local loss comparability, no chart
construction, no Jacobian compatibility, no normal crossings, pole order, or
RLCT.

Latest A2 literal product-difference square-sum:
`RegularSuspensionCoordinates.lean` now defines
`AoyagiProductDifferenceCoordinateIndex.literalValue`,
`literalValue_regular`, `literalValue_residual`, and
`literalCoordinateSquareSum_eq_regular_add_correctedResidual`.  This is the
finite square-sum expansion of the literal p. 13 block
`fromBlocks X (-F2) (-F3) (D - F3*F2)`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-literal-product-difference-square-sum.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-literal-product-difference-square-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-literal-product-difference-square-sum.md`.
Nonclaims: no comparison with cleaned loss, no analytic transport, no local
loss comparability, no chart construction, no Jacobian compatibility, no
normal crossings, pole order, or RLCT.

Latest A2 one-step determinant-chart coordinate equivalence:
`ChartTopology.lean` now proves
`productReductionStepCoordinate_detChart_homeomorph` between the raw and chart
determinant-chart subtypes for the p. 13 one-step coordinate change.  It also
adds product-topology instances and subtype continuity lemmas for
`toChart`/`toRaw`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Review:
`threads/03-block-product-reduction/review-a2-one-step-determinant-chart-coordinate-equivalence.md`.
Nonclaims: no analytic regularity, analytic Jacobian determinant calculation,
source-rank openness, source coverage, ideal-germ transport,
regular-suspension certificate, normal crossings, pole order, or RLCT.

Latest A2 signed-box residual/density comparison:
`MonomialChartIntegrability.lean` proves the signed-box absolute-value
finite-side theorem from supplied a.e. loss/density bounds.  Lean names:
`ae_forall_abs_pos_measure_pi_restrict_Ioo_neg`,
`integrableOn_abs_rpow_Ioo_neg_pos`,
`lintegral_ofReal_abs_rpow_restrict_Ioo_neg_lt_top`,
`lintegral_ofReal_fintype_abs_rpow_signedBox_lt_top`,
`lintegral_ofReal_fintype_abs_monomialFactor_signedBox_lt_top`,
`lintegral_ofReal_le_const_mul_fintype_abs_rpow_signedBox_lt_top`,
`lintegral_ofReal_le_const_mul_fintype_abs_monomialFactor_signedBox_lt_top`,
`loss_rpow_neg_mul_density_le_const_mul_abs_monomialFactor_of_abs_pos`, and
`lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-signed-box-residual-density-comparison.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-signed-box-residual-density-comparison.md`.
Review:
`threads/03-block-product-reduction/review-a2-signed-box-residual-density-comparison.md`.
Nonclaims: no proof of Aoyagi actual chart-side bounds, no analytic
density/Jacobian transport, no chart coverage, no endpoint/divergent-side or
threshold equality theorem, no normal crossings, pole order, or RLCT.

Latest A2 residual positive-set measurability handoff:
`RegularSuspensionCoordinates.lean` proves generic finite square-sum
measurability and the p.13 residual positive-set measurability theorem
`PaperEndpointFixedBaseRegularCoordinateSourceData.measurableSet_residualSquareSum_pos_of_measurable`
from a globally measurable residual coordinate map.  `RegularSuspensionLocalMeasure.lean`
adds
`PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_residual`,
which removes the explicit `hpos_meas` input from the weighted signed-box
residual source-measure constructor under that measurability assumption.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-positive-set-measurability-handoff.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-positive-set-measurability-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-positive-set-measurability-handoff.md`.
Nonclaims: no proof of residual-coordinate measurability from the suffix-state
recursion, no residual positivity/integrability without the signed-box
pushforward and monomial bounds, no chart construction, no density/Jacobian
transport, no original-loss comparison, no normal crossings, pole order, or
RLCT.

Latest A2 residual-coordinate map measurability:
`ChartTopology.lean` proves
`measurable_matrix_inv_real`,
`measurable_chartLocalSuffixState_transformedEdge_real`,
`measurable_chartLocalSuffixState_step_fields_real`, and
`measurable_chartLocalSuffixState_suffixState_fields_real`.
`RegularSuspensionCoordinates.lean` proves
`measurable_paperEndpointFixedBaseResidualBlockCoordinateMap_of_measurable_edgeMatrix`.
`RegularSuspensionLocalMeasure.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_of_measure_map_signedBox_withDensity_monomialLower_of_measurable_edgeMatrix`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-coordinate-map-measurability.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-coordinate-map-measurability.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-coordinate-map-measurability.md`
(xhigh review passed).
Nonclaims: no raw `Measurable Cedge` theorem for arbitrary non-normed
continuous-linear-map spaces, no source-rank openness, no analytic p.13 chart,
no pushforward, density/Jacobian transport, original-loss comparison, residual
positivity/integrability by itself, normal crossings, pole order, or RLCT.

Latest A2 p.13 half loss lower bound:
`RegularSuspensionCoordinates.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source`,
`PaperEndpointFixedBaseRegularCoordinateSourceData.const_mul_literal_squareSum_eventually_le_loss_to_half_regular_add_residual_squareSum_nhdsWithin_source`,
and
`exists_paperEndpointFixedBaseRegularCoordinateSourceData_literal_regular_add_residual_squareSum_eventually_half_le_nhdsWithin_source_of_rank_eq`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-p13-half-loss-lower-bound.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-p13-half-loss-lower-bound.md`.
Review:
`threads/03-block-product-reduction/review-a2-p13-half-and-signed-box-model-adapter.md`.
Nonclaims: no original DLN loss comparison, no analytic p.13 chart,
no density/Jacobian transport, no regular-suspension theorem, no normal
crossings, pole order, or RLCT.

Latest A2 signed-box model-loss adapter:
`MonomialChartIntegrability.lean` proves
`lintegral_ofReal_loss_rpow_neg_mul_density_signedBox_lt_top_of_modelLoss_le_const_mul_loss`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-signed-box-model-loss-adapter.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-signed-box-model-loss-adapter.md`.
Review:
`threads/03-block-product-reduction/review-a2-p13-half-and-signed-box-model-adapter.md`.
Nonclaims: no model-loss construction, no p.13 source-filter to signed-box
a.e. handoff, no density/Jacobian transport, no chart coverage, no normal
crossings, pole order, or RLCT.

Latest A2 regular-square bounded-density wrapper:
`RegularSuspensionSquareSumIntegrability.lean` proves
`lintegral_ofReal_loss_rpow_neg_mul_density_coordinateSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top`
and
`lintegral_ofReal_loss_rpow_neg_mul_density_residualBlockSquareSum_add_norm_sq_indicator_ball_prod_lt_top_of_residual_power_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-regular-square-bounded-density-wrapper.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-regular-square-bounded-density-wrapper.md`.
Review:
`threads/03-block-product-reduction/review-a2-regular-square-bounded-density-wrapper.md`.
Nonclaims: no p.13 chart construction, no original loss comparison,
no density/Jacobian transport, no residual-base integrability proof,
no threshold equality, no normal crossings, pole order, or RLCT.

Latest A2 p.13 regular-coordinate bounded-density adapter:
`RegularSuspensionSquareSumIntegrability.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.regularCoordinateEuclidean_finrank_eq_regularVariableCount`
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residual_power_lt_top`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Review:
`threads/03-block-product-reduction/review-a2-p13-regular-coordinate-bounded-density-adapter.md`.
Nonclaims: no source-filter to product-measure a.e. handoff, no p.13 analytic
chart construction, no original DLN loss comparison, no density/Jacobian
transport, no residual-base integrability proof, no threshold equality, no
normal crossings, pole order, or RLCT.

Latest A2 local measure handoff:
`LocalMeasureHandoff.lean` proves
`exists_open_ae_restrict_inter_of_eventually_nhdsWithin` and
`exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-measure-handoff.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-measure-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-measure-handoff.md`.
Nonclaims: no p.13 product chart, no source-coordinate/product-coordinate
identification, no loss comparison, no density/Jacobian transport, no
integrability theorem, no normal crossing, pole order, or RLCT extraction.

Latest A2 regular-suspension local measure handoff:
`RegularSuspensionLocalMeasure.lean` proves restricted-source and
first-projection product a.e. forms of the fixed-base p.13 half lower bound
and supplied-base-loss lower bound.  It also proves the uniform-in-fiber
product-hypothesis handoff for p.13 regular-coordinate loss/density bounds,
and a finite-integral bridge that consumes explicit source-stratum residual
positivity and residual negative-power integrability hypotheses before
invoking the p.13 finite-side adapter.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-regular-suspension-local-measure.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-regular-suspension-local-measure.md`.
Review:
`threads/03-block-product-reduction/review-a2-regular-suspension-local-measure.md`
and
`threads/03-block-product-reduction/review-a2-regular-suspension-uniform-product-handoff.md`;
finite-integral bridge reviewed in
`threads/03-block-product-reduction/review-a2-regular-suspension-local-finite-integral-bridge.md`.
Nonclaims: no measurable-source-stratum proof, no p.13 product chart, no
source/product coordinate identification, no product-fiber regular-square
lower bound proof, no original DLN loss comparison, no density/Jacobian
transport, no proof of residual positivity or residual-base integrability, no
normal crossing, pole order, or RLCT extraction.

Latest A2 signed-box residual source finite-integral bridge:
`RegularSuspensionLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix`.
It composes the measurable-edge weighted signed-box residual-source
constructor with the p.13 local finite-integral theorem, replacing the explicit
residual positivity and residual negative-power integrability inputs by the
signed-box residual source data.  Source-stratum measurability, signed-box
chart a.e.-measurability, source-density a.e.-measurability, weighted
pushforward, residual monomial lower bound, source-density a.e. nonnegativity,
source-density monomial upper bound, `0 < t`, and local regular-fiber
loss/density bounds remain explicit.  Review:
`threads/03-block-product-reduction/review-a2-signed-box-residual-source-finite-integral-bridge.md`.
Nonclaims: no p.13 chart construction, no pushforward proof, no
density/Jacobian transport, no original-loss comparison, no normal crossings,
pole order, or RLCT extraction.

Latest A2 signed-box residual continuous-density finite-integral bridge:
`RegularSuspensionLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_continuousAt_pos_density`.
It composes the measurable-edge weighted signed-box residual-source
constructor with the positive-continuous-density p.13 local finite-integral
theorem.  This replaces the explicit residual source hypotheses and the
explicit local product-density nonnegativity/boundedness hypotheses by
signed-box residual data plus `ContinuousAt density (x₀,0)` and
`0 < density (x₀,0)`.  The weighted pushforward, source-density hypotheses,
residual lower bound, source-stratum measurability, and regular-fiber loss
lower bound remain explicit.  Review:
`threads/03-block-product-reduction/review-a2-signed-box-residual-continuous-density-finite-integral-bridge.md`.
Nonclaims: no p.13 chart construction, no pushforward proof, no
density/Jacobian transport, no original-loss comparison, no normal crossings,
pole order, or RLCT extraction.

Latest A2 continuous-edge signed-box continuous-density finite-integral bridge:
`RegularSuspensionLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_continuousAt_pos_density`.
It derives source-stratum measurability and fixed-basis endpoint edge-matrix
measurability from global `Continuous Cedge` and then delegates to the
signed-box continuous-density bridge.  Review:
`threads/03-block-product-reduction/review-a2-continuous-edge-signed-box-continuous-density-finite-integral-bridge.md`.
Nonclaims: no source-rank openness, no result from only
`ContinuousAt Cedge x₀`, no raw `Measurable Cedge` API, no p.13 chart
construction, no pushforward proof, no density/Jacobian transport, no
original-loss comparison, no normal crossings, pole order, or RLCT extraction.

Latest A6 Definition 3 all-source strict rank-width:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.sourceRangeRankWidth_of_all_selected_strict` and
`AoyagiDefinition3SourceData.exists_consecutive_selectedReducedWidthCeilData_of_all_selected_strict`.
The first theorem derives source-range rank-width from the all-source strict
selected inequalities by summing over the complement of a fixed source index.
The second theorem uses that derived rank-width to call the existing
`_rankWidth` all-source selected ceiling-data package.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-all-source-strict-rank-width-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-all-source-strict-rank-width.md`.
Review:
`threads/06-dln-translation/review-definition3-all-source-strict-rank-width-a6.md`.

Latest A6 Definition 3 `ell=1` source-data formula:
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.exists_ell_one_theorem2Formula_of_sourceData_rankWidth_general`.
The theorem starts from supplied `AoyagiDefinition3SourceData L 1 H r C` and
source-range rank-width, derives selected positivity and value-set cover from
`S`, and delegates to the existing arbitrary-`L` selected-pair formula
package.  Reproduction:
`threads/06-dln-translation/reproduction-definition3-ell-one-source-data-formula-a6.md`.
Statement card:
`threads/06-dln-translation/statement-card-a6-definition3-ell-one-source-data-formula.md`.
Review:
`threads/06-dln-translation/review-definition3-ell-one-source-data-formula-a6.md`.

Latest A2 endpoint loss comparison:
`EndpointLossComparison.lean` proves
`chainMapMatrixFrobeniusLoss_eq_toMatrix_sub_squareSum`,
`exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_chainMapFrobeniusLoss`,
and
`exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple`.
The result compares the fixed adapted endpoint Frobenius loss with the
original square-Frobenius `lossDLN` only for tuples of the form
`chainMapMatrixTuple b E`, with target matrix the base endpoint map expressed
in the same original endpoint bases.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-endpoint-loss-comparison.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-endpoint-loss-comparison.md`.
Review:
`threads/03-block-product-reduction/review-a2-endpoint-loss-comparison.md`.
Nonclaims: no arbitrary-tuple comparison, no statistical/KL/covariance loss,
no chart construction, no density/Jacobian transport, no normal crossings,
pole order, or RLCT extraction.

Latest A2 product-family suffix-field construction:
`ProductReduction.lean` proves
`ChartLocalSuffixState.step_finalF3_fromBlocks`,
`ChartLocalSuffixState.step_middleResidualFactor_fromBlocks`,
`ChartLocalSuffixState.step_leftEndpointF2Ctop_fromBlocks`,
`ChartLocalSuffixState.step_singleEdgeF2F3Ctop_fromBlocks`,
`ChartLocalSuffixState.suffixState_tail_fields_of_productFamily_transformedEdges`,
`ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_one`, and
`ChartLocalSuffixState.suffixState_productFamily_fields_fromBlocks_succSucc`.
These are the one-step and global finite matrix facts for the intended p.13
product-family transformed edge shapes.  `RegularSuspensionCoordinates.lean`
proves
`paperEndpointFixedBaseRegularBlockF2F3SquareSum_eq_suffixState_B_lowerLeftBlock`,
exposing the fixed-base `F2/F3` square-sum as the suffix fields `-S.B` and
`lowerLeftBlock S.L`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-family-suffix-field-construction.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-family-suffix-field-construction.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-family-suffix-field-construction.md`.
Nonclaims: no constructed fixed-base edge family, no proof that a concrete
`CedgeProd` realizes the transformed-edge shapes, no analytic product chart,
no source coverage, no signed-box pushforward, no density/Jacobian transport,
no normal crossings, pole order, or RLCT extraction.

Latest A2 residual-block and source-dependent product-family continuity:
`ChartTopology.lean`, `FixedBasepointChart.lean`, and
`RegularSuspensionCoordinates.lean` now prove the local continuity stack:

```text
continuousAt_chartLocalSuffixState_residualBlock
continuousAt_chartLocalSuffixState_residualProduct
continuous_matrix_toContinuousLinearMap
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuous
paperEndpointFixedBaseContinuousReverseEdgeFamilyOfMatrices_continuousAt
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
```

Under `ContinuousAt CedgeBase x₀` and explicit recursive determinant-chart
hypotheses for the fixed-base matrix family at `x₀`, the constructed
source-dependent p.13 product-coordinate edge family is continuous at
`(x₀,u₀)`.  Under the self-base hypothesis `CedgeBase x₀ = reverseEdge B`,
those recursive chart hypotheses are supplied automatically.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-residual-block-continuity-support.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-residual-block-continuity-support.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-block-continuity-support.md`.
Nonclaims: no automatic recursive chart neighborhood, no product chart, no
source coverage, no signed-box pushforward, no density/Jacobian transport, no
normal crossings, pole order, or RLCT extraction.

Latest A2 source-dependent product-family small-ball coordinate identities:
`RegularSuspensionCoordinates.lean` proves
`exists_pos_radius_le_regular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily_nhdsWithin_source`.
Given a positive `Rmax`, it chooses `0 < R <= Rmax` so `Ctop(u)` has determinant
a unit for every `u in ball(0,R)`, and packages the constructed product
family's regular/residual coordinate identities as eventual on the base
source-rank stratum.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-source-dependent-product-family-small-ball-coordinate-identities.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-source-dependent-product-family-small-ball-coordinate-identities.md`.
Review:
`threads/03-block-product-reduction/review-a2-source-dependent-product-family-small-ball-coordinate-identities.md`.
Nonclaims: no product-family continuity, no product-reduction certificate, no
triangular multiplier bound, no product chart, no source coverage, no
density/Jacobian transport, no normal crossings, pole order, or RLCT
extraction.

Latest A2 product-coordinate source-rank membership:
`ProductReduction.lean` proves
`ChartLocalSuffixState.rank_productCoordinateRightEndpointMatrix`,
`ChartLocalSuffixState.rank_productCoordinateMiddleMatrix`, and
`ChartLocalSuffixState.rank_productCoordinateLeftEndpointMatrix`.
`RegularSuspensionCoordinates.lean` proves
`paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum`
and
`exists_pos_radius_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum_nhdsWithin_source`.
The pointwise theorem combines the block-rank identities with the residual
rank formulas from a base product-reduction certificate, proving source-rank
image membership for the explicit p.13 product-coordinate family.  The local
theorem supplies a small regular-coordinate ball where `det Ctop` is a unit
and uses eventual base product-reduction certificates near the self-base
chain.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-coordinate-source-rank-membership.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-coordinate-source-rank-membership.md`.
Nonclaims: no source coverage, no local source/image equality, no exact-rank
openness, no inverse chart, no density/Jacobian transport, no normal
crossings, pole order, or RLCT.

Latest A2 product-family certificate and adapted lower bound:
`ProductReduction.lean` proves
`ChartLocalSuffixState.recursiveDetCharts_productCoordinateEdges_succSucc`.
`RegularSuspensionCoordinates.lean` proves
`paperEndpointFixedBaseProductReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean`,
`exists_pos_radius_le_productReductionCertificate_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_nhdsWithin_source`,
`paperEndpointFixedBaseTriangularMultiplierSquareSumProduct_exists_pos_eventually_le_of_recursiveDetCharts`,
`exists_pos_radius_le_pos_const_triangularMultiplierSquareSumProduct_eventually_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source`,
and
`exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source`.
Together these give the adapted fixed-base product-difference lower bound for
the explicit multi-edge product family on a small source/regular-coordinate
product neighborhood.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-product-family-certificate-and-adapted-lower-bound.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-product-family-certificate-and-adapted-lower-bound.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-family-certificate-and-adapted-lower-bound.md`.
Nonclaims: no original-loss comparison, no product chart, no source coverage,
no density/Jacobian transport, no normal crossings, pole order, or RLCT
extraction.

Latest A2 original-loss local integrability for the explicit product family:
`OriginalLossLocalMeasure.lean` proves
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density`.
It consumes the landed self-base product-family adapted lower bound and the
existing original-loss finite-integral handoff to remove the explicit
`hadapted_lower` hypothesis for the concrete multi-edge product family.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-original-loss-local-integrability-product-family.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-original-loss-local-integrability-product-family.md`.
Review:
`threads/03-block-product-reduction/review-a2-original-loss-local-integrability-product-family.md`.
Nonclaims: no signed-box source chart construction, no pushforward proof, no
residual monomial lower-bound proof, no density/Jacobian transport, no normal
crossings, pole order, or RLCT extraction.

Latest A2 edge-matrix product-family original-loss front end:
`OriginalLossLocalMeasure.lean` proves
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density`.
It removes global `Continuous CedgeBase`, using local `ContinuousAt CedgeBase
x0` for the product-family lower bound and an explicit fixed-base edge-matrix
measurability hypothesis for source-measure plumbing.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-original-loss-local-integrability-product-family-edge-matrix.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-original-loss-local-integrability-product-family-edge-matrix.md`.
Review:
`threads/03-block-product-reduction/review-a2-original-loss-local-integrability-product-family-edge-matrix.md`.
Nonclaims: no signed-box source chart construction, no pushforward proof, no
residual monomial lower-bound proof, no density/Jacobian transport, no normal
crossings, pole order, or RLCT extraction.

Latest A2 original-loss product-step inverse-density handoff:
`OriginalLossLocalMeasure.lean` now proves
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase`.
It specializes the existing edge-matrix original-loss product-family front end
to the concrete chart-side inverse product-step Jacobian density along
`paperEndpointFixedBaseP13RawOrderTuple`, using the already-proved p.13
inverse-density continuity and positivity lemmas.  Reproduction and statement
card:
`threads/03-block-product-reduction/reproduction-a2-original-loss-product-step-inverse-density-handoff.md`
and
`threads/03-block-product-reduction/statement-card-a2-original-loss-product-step-inverse-density-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-original-loss-product-step-inverse-density-handoff.md`.
Nonclaims: no p.13 source chart construction, source coverage, source/product
pushforward, signed-box density identification, original prior transport,
normal crossings, pole order, or RLCT extraction.

Latest A2 local-source signed-box and monomial-unit finite-integral boundary:
`RegularSuspensionLocalMeasure.lean` proves
`exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_loss_density_bounds`,
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource`,
`signedBox_monomialLower_sourceDensityBounds_of_monomialUnits`, and
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialLower_edgeMatrix`.
This replaces the full source-rank-stratum front end by an explicit measurable
local source and derives the signed-box residual lower bound plus transported
source-density measurability/nonnegativity/monomial upper bound from
monomial-times-bounded-unit hypotheses.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-source-signed-box-monomial-unit-boundary.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-source-signed-box-monomial-unit-boundary.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-source-signed-box-monomial-unit-boundary.md`.
Nonclaims: no local chart construction, source coverage, pushforward proof,
density/Jacobian formula, normal-crossing extraction, pole order, or RLCT.

Latest A2 local-source monomial-unit finite-integral wrapper:
`RegularSuspensionLocalMeasure.lean` now proves
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_residualSource_signedBox_withDensity_monomialUnits_edgeMatrix`.
It composes the elementary monomial-unit inequality package with the
local-source signed-box finite-integral theorem, replacing expanded
residual/source-density monomial inequality hypotheses by supplied residual
and source-density unit identities plus a.e. unit bounds.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-source-monomial-unit-finite-integral-wrapper.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-source-monomial-unit-finite-integral-wrapper.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-source-monomial-unit-finite-integral-wrapper.md`.
Nonclaims: no local chart construction, source coverage, pushforward proof,
density/Jacobian formula, concrete monomial-unit production,
normal-crossing extraction, pole order, or RLCT.

Latest A2 local-source adapted-loss finite-integral socket:
`RegularSuspensionLocalMeasure.lean` now proves
`exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss`.
It is the local-source analogue of the existing adapted-loss finite-integral
socket: the proof multiplies the adapted lower bound by the positive
adapted-to-loss comparison constant and delegates to the local-source p.13
theorem.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-source-adapted-loss-finite-integral-socket.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-source-adapted-loss-finite-integral-socket.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-source-adapted-loss-finite-integral-socket.md`.
Nonclaims: no adapted lower-bound proof, original-loss comparison, chart
construction, source coverage, density/Jacobian transport, normal crossings,
pole order, or RLCT.

Latest A2 original-loss local-source finite-integral socket:
`OriginalLossLocalMeasure.lean` now proves
`exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower`.
It specializes the local-source adapted-loss socket to concrete endpoint
square-Frobenius `lossDLN` by using the finite endpoint basis comparison and
the adapted Frobenius-loss/square-sum identity.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-original-loss-local-source-finite-integral-socket.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-original-loss-local-source-finite-integral-socket.md`.
Review:
`threads/03-block-product-reduction/review-a2-original-loss-local-source-finite-integral-socket.md`.
Nonclaims: no local source/chart construction, source coverage,
pushforward/Jacobian transport, monomial-unit production, normal crossings,
pole order, or RLCT.

Latest A2 measurable local-source package from source certificates:
`ProductReductionEntryIdealBoundary.lean` now proves
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource`
and
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource_of_measurable_edgeMatrix`.
`RegularSuspensionLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix`.
Together these extract `source = U inter sourceRankStratum` from the local
source certificate, prove measurability and basepoint membership, carry the
canonical source-rank conclusion on `source`, and record the `nhdsWithin`
equality needed to reuse source-stratum-local p.13 bounds on the local source.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-measurable-local-source-from-source-certificate.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-measurable-local-source-from-source-certificate.md`.
Review:
`threads/03-block-product-reduction/review-a2-measurable-local-source-from-source-certificate.md`.
Nonclaims: no signed-box chart construction, source image/coverage theorem,
pushforward/Jacobian transport, residual/source-density monomial-unit
production, normal crossings, pole order, or RLCT.

Latest A2 local-source product-family adapted lower bound:
`RegularSuspensionLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase`.
It combines the measurable local-source extractor with the explicit self-base
multi-edge p.13 product-coordinate adapted lower bound, returning the local
source, source-rank data, `nhdsWithin` equality, positive radius/constant, and
the lower bound over `nhdsWithin x0 source`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-source-product-family-adapted-lower-bound.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-source-product-family-adapted-lower-bound.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-source-product-family-adapted-lower-bound.md`.
Nonclaims: no signed-box chart construction, source image/coverage theorem,
pushforward/Jacobian transport, original/KL loss comparison,
residual/source-density monomial-unit production, normal crossings, pole order,
or RLCT.

Latest A2 local-source original-loss product-family continuation:
`OriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_forall_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_multiEdgeProductCoordinateEdgeFamily_selfBase`.
It composes the local-source product-family adapted lower-bound theorem with
the local-source original-loss finite-integral socket, returning the local
source, source-rank data, `nhdsWithin` equality, positive radius/constant, and
a continuation for concrete endpoint `lossDLN` finite local integrals once
residual positivity/integrability and density bounds are supplied on that
source.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-local-source-original-loss-product-family-continuation.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-local-source-original-loss-product-family-continuation.md`.
Review:
`threads/03-block-product-reduction/review-a2-local-source-original-loss-product-family-continuation.md`.
Nonclaims: no signed-box chart construction, source image/coverage theorem,
pushforward/Jacobian transport, residual/source-density monomial-unit
production, residual integrability proof, normal crossings, pole order, or
RLCT.

Latest A2 selected-entry signed-box monomial-unit data:
`SelectedEntrySignedBoxMeasure.lean` now proves concrete signed-box
monomial-unit data for the elementary selected-entry pivot chart.  The
coordinate index is `Option {i // i in center.erase pivot}`; the pivot
coordinate has loss exponent `1` and formal density exponent
`(center.erase pivot).card`, while all non-pivot residual coordinates have
exponent `0`.

Lean names:
`SelectedEntrySignedBox.residual_eq_unit_mul_abs_monomial`,
`SelectedEntrySignedBox.sourceDensity_eq_abs_pivotFirstJacobian_det`,
`SelectedEntrySignedBox.sourceDensity_eq_unit_mul_abs_monomial`,
`SelectedEntrySignedBox.monomialUnitHypotheses`, and
`SelectedEntrySignedBox.monomialLower_sourceDensityBounds`, with matching
center-subtype wrappers
`SelectedEntrySignedBox.CenterCoord.monomialUnitHypotheses` and
`SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds`.

Nonclaims: no analytic chart domains, source image/coverage theorem,
weighted pushforward, analytic Jacobian/source-density transport, full DLN
loss comparison, normal crossings, pole order, or RLCT.

Latest A2 selected-entry chart Jacobian pushforward:
`SelectedEntrySignedBoxMeasure.lean` now proves the actual derivative
determinant and weighted signed-box pushforward for the finite center-indexed
selected-entry chart.  Lean names:
`SelectedEntrySignedBox.CenterCoord.chartMapFDeriv_det`,
`SelectedEntrySignedBox.CenterCoord.sourceDensity_eq_abs_chartMapFDeriv_det`,
`SelectedEntrySignedBox.CenterCoord.signedBoxMeasure_eq_volume_restrict`,
`SelectedEntrySignedBox.CenterCoord.volume_pivot_hyperplane_eq_zero`,
`SelectedEntrySignedBox.CenterCoord.signedBoxSet_ae_eq_inter_pivot_ne_zero`,
`SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet_inter_pivot_ne_zero`,
`SelectedEntrySignedBox.CenterCoord.measurableSet_chartMap_image_signedBoxSet`,
`SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_withDensity_sourceDensity_eq_restrict_image_of_subset_pivot_ne_zero`,
`SelectedEntrySignedBox.CenterCoord.map_chartMap_restrict_nonzeroSignedBox_withDensity_sourceDensity_eq_restrict_image`,
`SelectedEntrySignedBox.CenterCoord.chartMap_image_signedBoxSet_ae_eq_inter_pivot_ne_zero`,
and
`SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-jacobian-pushforward.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-jacobian-pushforward.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-chart-jacobian-pushforward.md`.
Nonclaims: no p.13 source chart construction, original source image/coverage,
original source measure identity, full DLN loss comparison, normal crossings,
pole order, or RLCT.

Latest A2 selected-entry chart-image local handoff:
`SelectedEntrySignedBoxLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix`.
It specializes the selected-entry local-source finite-integral handoff to
`source = chartMap pivot '' signedBoxSet Rres`, `sourceChart = chartMap pivot`,
and `μ = volume`, using the finite chart transport theorem to discharge the
weighted pushforward and chart-image measurability to discharge source
measurability.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-image-local-handoff.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-image-local-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-chart-image-local-handoff.md`.
Nonclaims: no p.13 source chart construction in the original DLN parameter
space, original source image/coverage, original source measure identity, full
DLN loss comparison, normal crossings, pole order, or RLCT.

Latest A2 selected-entry chart-image original-loss wrapper:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_adaptedProductDifferenceSquareSum_lower`.
It keeps the integration source as the finite chart image
`chartMap pivot '' signedBoxSet Rres` and uses the endpoint basis comparison
to replace the abstract loss by the original fixed-endpoint-basis `lossDLN`,
while retaining the adapted-product lower bound as an explicit hypothesis.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-chart-image-original-loss-wrapper.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-chart-image-original-loss-wrapper.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-chart-image-original-loss-wrapper.md`.
Nonclaims: no original p.13 source chart construction, source-rank stratum
coverage, original-source measure identity, derivation of the adapted-product
lower bound from original-source coordinates, normal crossings, pole order, or
RLCT.

Latest A2 selected-entry local source-stratum original-loss bridge:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase`.
It weakens the previous source-stratum wrapper's global source/image equality
to an explicit open-neighborhood equality
`Ulocal ∩ sourceStratum = Ulocal ∩ chartMap pivot '' signedBoxSet Rres`.
The proof transports `nhdsWithin` bounds across this local equality, applies
the finite chart-image original-loss wrapper, shrinks the final open set into
`Ulocal`, and rewrites the restricted source-stratum measure there.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-local-source-stratum-original-loss-bridge.md`.
Nonclaims: the local equality is not proved; no p.13 source chart
construction, source-rank image/coverage theorem, original-source measure
transport, normal crossings, pole order, or RLCT.

Latest A2 selected-entry residual coordinate square-sum:
`RegularSuspensionCoordinates.lean` now proves
`aoyagiCoordinateSquareSum_comp_equiv`, and
`SelectedEntrySignedBoxMeasure.lean` now proves
`SelectedEntrySignedBox.CenterCoord.residual_eq_aoyagiCoordinateSquareSum_chartMap`
and
`SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_eq_residual_of_coord_readout`.
The first selected-entry theorem identifies the finite center-coordinate
residual with the square-sum of the selected-entry chart coordinates.  The
second packages the honest bridge shape: another finite coordinate family has
that residual square-sum only under an explicit finite equivalence and
pointwise coordinate readout.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-source-chart-coverage-boundary.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-residual-coordinate-square-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-residual-coordinate-square-sum.md`.
Nonclaims: no fixed-base residual-coordinate readout, source chart
construction, source coverage, source-measure transport, normal crossings,
pole order, or RLCT.

Latest A2 selected-entry original-loss readout wrapper:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_eq_chartMap_selectedEntryCenter_signedBox_withDensity_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_of_residualBlockCoordinateReadout`.
It replaces the raw scalar `hresidual_eq` input to the local source-stratum
original-loss endpoint by an explicit finite equivalence from fixed-base
residual indices to selected-entry center coordinates and a pointwise
coordinate-readout hypothesis.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-original-loss-readout-wrapper.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-original-loss-readout-wrapper.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-original-loss-readout-wrapper.md`.
Nonclaims: no construction of the readout, no source chart construction,
source coverage, source-measure transport, normal crossings, pole order, or
RLCT.

Latest A2 selected-entry residual-product matrix readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_residualProduct_eq_matrix`.
It converts a supplied fixed-base suffix residual-product matrix identity at
`SelectedEntrySignedBox.CenterCoord.chartMap pivot y` into the pointwise
selected-entry coordinate readout used by the original-loss wrapper, using
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct` and
`AoyagiResidualBlockCoordinateIndex.value_matrix`.  Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-product-matrix-readout.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-residual-product-matrix-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-residual-product-matrix-readout.md`.
Nonclaims: no construction of `CedgeBase`, no proof of the residual-product
matrix identity, no construction of the residual-index equivalence, no source
coverage, source-measure transport, normal crossings, pole order, or RLCT.

Latest A2 selected-entry residual-factor readout boundary:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualProduct_eq_selectedEntryCenter_matrix_of_residualFactorProduct_eq_matrix`.
It derives the selected-entry residual-product matrix identity from the
Aoyagi-shaped data: a supplied compatible residual-factor family, proofs that
the transformed Schur residual blocks are those factors, and a supplied
ordered factor-product identity to the selected-entry coordinate matrix.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-residual-factor-readout-boundary.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-residual-factor-readout-boundary.md`.
Nonclaims: no construction of compatible factors, no factor-product proof, no
residual-index equivalence construction, no source/image equality,
source-measure transport, normal crossings, pole order, or RLCT.

Latest A2 selected-entry prescribed-matrix readout:
`SelectedEntryOriginalLossLocalMeasure.lean` now proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_chartMap_of_prescribedEdgeMatrix_residualProduct_eq_matrix`.
It starts from a supplied fixed-base matrix family `Ebase`, uses
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices`
to identify the realised continuous edge family's fixed-base matrices with
`Ebase`, and delegates to the residual-product matrix readout bridge.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-selected-entry-prescribed-matrix-readout.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-selected-entry-prescribed-matrix-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-selected-entry-prescribed-matrix-readout.md`.
Nonclaims: no construction of `Ebase`, no proof of the residual-product
matrix identity, no construction of the residual-index equivalence, no source
coverage, source-measure transport, normal crossings, pole order, or RLCT.

Latest A2 single-edge residual-product realisation:
`ProductReduction.lean` now proves
`ChartLocalSuffixState.residualProduct_productCoordinateSingleEdge_eq`, and
`RegularSuspensionCoordinates.lean` proves
`paperEndpointFixedBaseSingleEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq`.
The one-edge p.13 block matrix has transformed Schur residual `D` under
`IsUnit Ctop.det`, and the suffix-state bridge identifies this with the raw
residual product.  Reproduction, statement card, and review:
`threads/03-block-product-reduction/reproduction-a2-single-edge-residual-product-realisation.md`,
`threads/03-block-product-reduction/statement-card-a2-single-edge-residual-product-realisation.md`,
and
`threads/03-block-product-reduction/review-a2-single-edge-residual-product-realisation.md`.
Nonclaims: no raw lower-right-block identity, no multi-edge arbitrary final
residual realisation, no source-data choice of `D`, no source chart, no source
coverage, no source-measure transport, no normal crossings, pole order, or
RLCT.

Latest A2 residual-product factor frontier:
`ProductReduction.lean` now defines
`ChartLocalSuffixState.residualFactorProduct` and proves
`ChartLocalSuffixState.residualProduct_eq_residualFactorProduct_of_residualBlock_eq`
and
`ChartLocalSuffixState.residualProduct_productCoordinateEdges_succSucc_eq_residualFactorProduct`.
The new factor product is the explicit decreasing product of supplied residual
factors `C p`; if every suffix transformed Schur residual block below the
endpoint `j` equals `C p`, then the suffix `residualProduct` equals this
explicit factor product.
For raw multi-edge p.13 product-coordinate matrices this follows from the
existing residual-block theorem.  `RegularSuspensionCoordinates.lean` also now
proves
`paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean_residualProduct_eq_base`,
which exposes that the fixed-base p.13 product-coordinate constructor
preserves the base suffix residual product.  Reproductions, statement cards,
and review:
`threads/03-block-product-reduction/reproduction-a2-residual-factor-product.md`,
`threads/03-block-product-reduction/statement-card-a2-residual-factor-product.md`,
`threads/03-block-product-reduction/reproduction-a2-product-coordinate-residual-product-preservation.md`,
`threads/03-block-product-reduction/statement-card-a2-product-coordinate-residual-product-preservation.md`,
and
`threads/03-block-product-reduction/review-a2-residual-product-factor-frontier.md`.
Nonclaims: no construction of the residual factors from Aoyagi source data, no
selected-entry residual-product matrix identity, no arbitrary final residual
matrix realization in the multi-edge case, no fixed-base source chart, no
residual-index equivalence, no source coverage, source-measure transport,
normal crossings, pole order, or RLCT.

Latest A2 residual-factor rank obstruction:
`ProductReduction.lean` now proves
`ChartLocalSuffixState.residualFactorProduct_trans` and
`ChartLocalSuffixState.rank_residualFactorProduct_le_card_intermediate`.
The first splits the explicit factor product through any intermediate residual
index `q`; the second uses `Matrix.rank_mul_le_left` and
`Matrix.rank_le_card_width` to show that the terminal factor product has rank
at most `card (kappa q)` over a nontrivial coefficient ring.  Reproduction and
statement card:
`threads/03-block-product-reduction/reproduction-a2-residual-factor-product-rank-obstruction.md`
and
`threads/03-block-product-reduction/statement-card-a2-residual-factor-product-rank-obstruction.md`.
Review:
`threads/03-block-product-reduction/review-a2-residual-factor-product-rank-obstruction.md`.
Nonclaims: no selected-entry matrix factorization result, no source-factor
construction, no residual-index equivalence, no source coverage, no
source-measure transport, no normal crossings, no pole order, and no RLCT.

Latest A2 Case 2 displayed-product entrywise selected-center RHS:
`Case2ResidualFactorProduct.lean` now proves
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_centerCoordinateSubmatrix_of_entrywise`
and
`residualFactorProduct_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-entrywise-selected-center-rhs.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-displayed-product-entrywise-selected-center-rhs.md`,
and
`threads/03-block-product-reduction/review-a2-case2-displayed-product-entrywise-selected-center-rhs.md`.
This is finite extensionality only; the pointwise readout, endpoint
equivalences, compatible factors, source/image equality, normal crossings,
pole order, and RLCT remain open.

Latest A2 Case 2 displayed-product successor source-chart map:
`Case2ResidualFactorProduct.lean` now proves
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_successorSourceChartMapMatrix_of_entrywise`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-successor-source-chart-map.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-displayed-product-successor-source-chart-map.md`,
and
`threads/03-block-product-reduction/review-a2-case2-displayed-product-successor-source-chart-map.md`.
This is finite endpoint reindexing only; the successor source-chart readout,
selected-center readout, endpoint/source data, compatible factors,
source/image equality, normal crossings, pole order, and RLCT remain open.

Latest A2 Case 2 displayed-product entry expansion:
`Case2ResidualFactorProduct.lean` now proves
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply` and
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_apply_eq_sum_freeCprime`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-displayed-product-entry-expansion.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-displayed-product-entry-expansion.md`,
and
`threads/03-block-product-reduction/review-a2-case2-displayed-product-entry-expansion.md`.
This is finite matrix multiplication only; selected-center/source-chart
readout, endpoint/source data, compatible factors, source/image equality,
normal crossings, pole order, and RLCT remain open.

Latest A2 Case 2 source-chart CenterCoord alignment:
`SelectedEntrySignedBoxMeasure.lean` now proves
`case2DisplayedSourceChartMap_eq_selectedEntrySignedBoxCenterCoord_chartMap_apply`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-source-chart-centercoord-alignment.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-source-chart-centercoord-alignment.md`,
and
`threads/03-block-product-reduction/review-a2-case2-source-chart-centercoord-alignment.md`.
This is definitional vocabulary alignment for the old Case 2 source chart;
post-pivot product readout, successor source-chart readout, source/image
equality, normal crossings, pole order, and RLCT remain open.

Latest A2 Case 2 successor readout CenterCoord matrix:
`Case2ResidualSelectedEntryChartBridge.lean` now proves
`residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-successor-readout-centercoord-matrix.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-successor-readout-centercoord-matrix.md`,
and
`threads/03-block-product-reduction/review-a2-case2-successor-readout-centercoord-matrix.md`.
This is conditional finite composition; successor readout, endpoint
equivalences, compatible factors, source/image equality, normal crossings,
pole order, and RLCT remain open.

Latest A2 Case 2 concrete two-edge factor family:
`Case2ResidualFactorProduct.lean` now defines
`case2PostPivotTwoEdgeDomain` and
`case2PostPivotFreeTwoEdgeFactorFamily`, and proves
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_freeTwoEdgeFactorProduct`.
`Case2ResidualSelectedEntryChartBridge.lean` also proves
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-concrete-two-edge-factor-family.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-concrete-two-edge-factor-family.md`,
and
`threads/03-block-product-reduction/review-a2-case2-concrete-two-edge-factor-family.md`.
This specializes the displayed Case 2 two-edge chain and removes generic
endpoint/factor boilerplate; successor readout, source-produced `Cprime`,
source/image equality, normal crossings, pole order, and RLCT remain open.

Latest A2 Case 2 paper-Cprime source-following product:
`Case2ResidualFactorProduct.lean` now proves
`residualFactorProduct_case2PostPivotFreeTwoEdgeFactorFamily_paperCprime_eq_sourceResidualBlock_successorFollowingFactor`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-case2-paper-cprime-source-following-factor-product.md`,
`threads/03-block-product-reduction/statement-card-a2-case2-paper-cprime-source-following-factor-product.md`,
and
`threads/03-block-product-reduction/review-a2-case2-paper-cprime-source-following-factor-product.md`.
This is the unweighted concrete residual-factor-product handoff for Aoyagi's
paper `C' = Q^-1 C`; successor selected-entry readout, source production,
source/image equality, normal crossings, pole order, and RLCT remain open.

Latest A2 Case 2 post-pivot compatible residual-factor identity audit:
`threads/03-block-product-reduction/reproduction-a2-case2-post-pivot-compatible-residual-factor-identity.md`
records a killed source claim. Aoyagi's Case 2 calculation supplies the
post-pivot product `D_(J+1) * C'_+`, but not an identity making that product
the successor selected-entry `CenterCoord.chartMap` matrix. No Lean theorem
was added; the existing conditional `..._of_entrywise` bridges remain the
correct boundary. Review:
`threads/03-block-product-reduction/review-a2-case2-post-pivot-compatible-residual-factor-identity.md`.

Latest A2 Schur-core formal Jacobian unit:
`ProductReductionStepJacobian.lean` now proves that the fixed-pivot Schur-core
formal tangent map for Aoyagi's coordinate change is a linear equivalence and
has unit determinant in the finite side-index case.  Lean names:
`SchurCoreTangent`, `schurCoreFormalJacobian`,
`schurCoreFormalJacobianInverse`, `schurCoreFormalJacobianEquiv`, and
`schurCoreFormalJacobian_det_isUnit`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-schur-core-formal-jacobian-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-schur-core-formal-jacobian-unit.md`,
and
`threads/03-block-product-reduction/review-a2-schur-core-formal-jacobian-unit.md`.
This is formal finite Jacobian arithmetic only; nonlinear derivative,
source-measure pushforward, density transport, exact determinant
sign/exponent, the full product-step Jacobian, normal crossings, pole order,
and RLCT remain open.

Latest A2 product-step fixed-passive formal Jacobian unit:
`ProductReductionStepJacobian.lean` now proves the fixed-passive p. 13 one-step
formal tangent map is a linear equivalence and has unit finite determinant.
Lean names:
`ProductStepFixedPassiveRawTangent`,
`ProductStepFixedPassiveChartTangent`,
`productStepFixedPassiveFormalJacobian`,
`productStepFixedPassiveFormalJacobianInverse`,
`productStepFixedPassiveFormalJacobianEquiv`, and
`productStepFixedPassiveFormalJacobian_det_isUnit`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-fixed-passive-formal-jacobian-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-fixed-passive-formal-jacobian-unit.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-fixed-passive-formal-jacobian-unit.md`.
This fixes `D`, `A1`, and `A3`, so it is not the full p. 13 tangent map; no
analytic derivative, source-measure pushforward, density/Jacobian transport,
normal crossings, pole order, or RLCT is proved.

Latest A2 full product-step formal Jacobian formulas:
`ProductReductionStepJacobian.lean` now records the full p. 13 forward and
inverse formal tangent formulas and the chart-output raw-order permutation.
Lean names:
`ProductReductionStepRawTangent`,
`ProductReductionStepChartTangent`,
`productReductionStepFormalJacobianFormula`,
`productReductionStepFormalJacobianInverseFormula`, and
`productReductionStepChartTangentRawOrderEquiv`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-full-formal-jacobian-formulas.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-formal-jacobian-formulas.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-formal-jacobian-formulas.md`.
This is formula-level Lean plus determinant-order plumbing only; the bundled
full `LinearMap`, `LinearEquiv`, determinant unit theorem, analytic derivative,
source-measure transport, normal crossings, pole order, and RLCT remain open.

Latest A2 full product-step bundled formal linear maps:
`ProductReductionStepJacobian.lean` now defines the full forward and inverse
formal tangent formulas as bundled `LinearMap`s and proves the application
theorems against the previously recorded formula functions. Lean names:
`productReductionStepFormalJacobian`,
`productReductionStepFormalJacobian_apply`,
`productReductionStepFormalJacobianInverse`, and
`productReductionStepFormalJacobianInverse_apply`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-full-linear-maps.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-linear-maps.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-linear-maps.md`.
This is the linearity layer only; the full `LinearEquiv`, determinant unit
theorem, analytic derivative, source-measure transport, normal crossings,
pole order, and RLCT remain open.

Latest A2 full product-step formal Jacobian equivalence:
`ProductReductionStepJacobian.lean` now proves both formula-composition
identities at the raw-derived chart base point and bundles the full raw/chart
formal tangent map as a `LinearEquiv`. Lean names:
`productReductionStepFormalJacobianInverseFormula_formula_chartBase`,
`productReductionStepFormalJacobianFormula_inverseFormula_chartBase`,
`productReductionStepFormalJacobianEquiv`,
`productReductionStepFormalJacobianEquiv_apply`, and
`productReductionStepFormalJacobianEquiv_symm_apply`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-full-formal-jacobian-equivalence.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-formal-jacobian-equivalence.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-formal-jacobian-equivalence.md`.
This proves finite formal invertibility only. The full determinant-unit theorem
still needs the chart-output raw-order endomorphism; analytic derivative,
source-measure transport, normal crossings, pole order, and RLCT remain open.

Latest A2 full product-step raw-order formal Jacobian unit:
`ProductReductionStepJacobian.lean` now composes the full raw/chart formal
tangent map with `productReductionStepChartTangentRawOrderEquiv`, producing a
raw-shaped endomorphism and proving its finite `LinearMap.det` is a unit. Lean
names: `productReductionStepFormalJacobianRawOrder`,
`productReductionStepFormalJacobianRawOrder_apply`,
`productReductionStepFormalJacobianRawOrderEquiv`,
`productReductionStepFormalJacobianRawOrderEquiv_apply`, and
`productReductionStepFormalJacobianRawOrder_det_isUnit`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-full-raw-order-jacobian-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-raw-order-jacobian-unit.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-raw-order-jacobian-unit.md`.
This is a finite formal determinant-unit certificate only; analytic derivative,
source-measure transport, normal crossings, pole order, and RLCT remain open.

Latest A2 product-step ambient derivative:
`ProductReductionStepDerivative.lean` now begins the analytic derivative layer
for the p. 13 coordinate change. Lean names:
`hasFDerivAt_matrix_inv_of_isUnit_det`,
`productReductionStepTopologyTupleToChart`,
`productReductionStepTopologyTupleToChart_topologyTuple`,
`productReductionStepTopologyTupleToChart_topologyTuple_chartBase`, and
`hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-ambient-derivative.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-ambient-derivative.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-ambient-derivative.md`.
This proves matrix inverse differentiability on determinant-unit real square
matrices, the tuple-level map/record bridge, and the `Ctop = C1*A1`
component derivative. The full tuple derivative, analytic determinant formula,
source-measure transport, normal crossings, pole order, and RLCT remain open.

Latest A2 product-step F2 ambient derivative:
`ProductReductionStepDerivative.lean` now proves the first inverse-dependent
component derivative for `F2 = -A1^{-1}A2`. Lean names:
`matrixMulContinuousLinearMap`, `matrixMulContinuousLinearMap_apply`, and
`hasFDerivAt_productReductionStepTopologyTupleToChart_F2`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-f2-ambient-derivative.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-f2-ambient-derivative.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-f2-ambient-derivative.md`.
This identifies the analytic derivative of the `F2` coordinate with
`productReductionStepFormalJacobian_dF2` under `IsUnit x.A1.det`. The `F3`
and `C` components, full tuple derivative, analytic determinant formula,
source-measure transport, normal crossings, pole order, and RLCT remain open.

Latest A2 product-step F3 ambient derivative:
`ProductReductionStepDerivative.lean` now proves the analytic derivative of
`F3 = F3old - D*A3*(C1*A1)^{-1}`. Lean name:
`hasFDerivAt_productReductionStepTopologyTupleToChart_F3`.
The proof reuses `hasFDerivAt_productReductionStepTopologyTupleToChart_Ctop`,
`hasFDerivAt_matrix_inv_of_isUnit_det`, and `matrixMulContinuousLinearMap`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-f3-ambient-derivative.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-f3-ambient-derivative.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-f3-ambient-derivative.md`.
This identifies the analytic derivative of the `F3` coordinate with
`productReductionStepFormalJacobian_dF3` under `IsUnit x.C1.det` and
`IsUnit x.A1.det`. The `C` component, full tuple derivative, analytic
determinant formula, source-measure transport, normal crossings, pole order,
and RLCT remain open.

Latest A2 product-step C ambient derivative:
`ProductReductionStepDerivative.lean` now proves the analytic derivative of
`C = A4 - A3*A1^{-1}*A2`. Lean name:
`hasFDerivAt_productReductionStepTopologyTupleToChart_C`.
The proof reuses `hasFDerivAt_matrix_inv_of_isUnit_det` and
`matrixMulContinuousLinearMap`, grouping the tail as `(A3*A1^{-1})*A2`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-c-ambient-derivative.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-c-ambient-derivative.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-c-ambient-derivative.md`.
This identifies the analytic derivative of the `C` coordinate with
`productReductionStepFormalJacobian_dC` under `IsUnit x.A1.det`. All
component derivatives are now available; full tuple derivative assembly,
analytic determinant formula, source-measure transport, normal crossings,
pole order, and RLCT remain open.

Latest A2 product-step full ambient derivative:
`ProductReductionStepDerivative.lean` now proves the full ambient derivative
of `productReductionStepTopologyTupleToChart`. Lean name:
`hasFDerivAt_productReductionStepTopologyTupleToChart`.
The proof assembles the component theorems for `Ctop`, `F2`, `F3`, and `C`
with passive projection derivatives for `D`, `A1`, and `A3`, and identifies
the derivative with `productReductionStepFormalJacobian x`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-full-ambient-derivative.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-full-ambient-derivative.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-full-ambient-derivative.md`.
This closes the ambient differentiability-to-formal-Jacobian identification.
Analytic determinant formula, source-measure transport, normal crossings, pole
order, and RLCT remain open.

Latest A2 product-step raw-order ambient derivative:
`ProductReductionStepDerivative.lean` now proves the derivative of the
raw-order composite of the ambient tuple map. Lean name:
`hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder`.
The proof composes the full ambient derivative theorem with
`productReductionStepChartTangentRawOrderEquiv` and identifies the derivative
with `productReductionStepFormalJacobianRawOrder x`, whose determinant unit
theorem `productReductionStepFormalJacobianRawOrder_det_isUnit` was already
landed. The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-raw-order-ambient-derivative.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-raw-order-ambient-derivative.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-raw-order-ambient-derivative.md`.
This reaches the determinant-facing ambient derivative map. Analytic
chart/subtype change of variables, source-measure transport, normal crossings,
pole order, and RLCT remain open.

Latest A2 product-step raw-order fderiv determinant unit:
`ProductReductionStepDerivative.lean` now proves unitness of the determinant
of the actual ambient Frechet derivative of the raw-order composite. Lean name:
`fderiv_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit`.
The proof uses `HasFDerivAt.fderiv` on
`hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder` and closes by
`productReductionStepFormalJacobianRawOrder_det_isUnit`. The reproduction,
statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-raw-order-fderiv-det-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-raw-order-fderiv-det-unit.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-raw-order-fderiv-det-unit.md`.
This closes only the ambient determinant-unit bridge. Analytic chart/subtype
change of variables, source-measure transport, normal crossings, pole order,
and RLCT remain open.

Latest A2 product-step determinant-chart fderivWithin bridge:
`ProductReductionStepDerivative.lean` now proves the raw determinant-chart
open-domain derivative and determinant-unit statement. Lean names:
`isOpen_productReductionStepRawTopologyTuple_detChart`,
`hasFDerivWithinAt_productReductionStepTopologyTupleToChart_rawOrder_detChart`,
and
`fderivWithin_productReductionStepTopologyTupleToChart_rawOrder_det_isUnit`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-det-chart-fderivwithin.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-det-chart-fderivwithin.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-det-chart-fderivwithin.md`.
This closes only the ambient open-domain determinant-chart bridge. It does not
prove subtype differentiability, local injectivity, source-measure transport,
density transport, normal crossings, pole order, or RLCT.

Latest A2 product-step raw-order determinant-chart injectivity:
`ProductReductionStepDerivative.lean` now proves injectivity of the exact
raw-order product-step tuple map on the raw determinant-chart set. Lean names:
`ProductReductionStepRawCoordinates.topologyTuple_injective`,
`ProductReductionStepChartCoordinates.topologyTuple_injective`,
`productReductionStepRawCoordinatesOfTopologyTuple`,
`productReductionStepTopologyTupleToChart_ofTopologyTuple`, and
`injOn_productReductionStepTopologyTupleToChart_rawOrder_detChart`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-raw-order-injon-det-chart.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-raw-order-injon-det-chart.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-raw-order-injon-det-chart.md`.
This supplies only the injectivity hypothesis for future Jacobian
change-of-variables work. It does not prove source-measure transport, density
transport, normal crossings, pole order, or RLCT.

Latest A2 product-step weighted additive-Haar change of variables:
`ProductReductionStepMeasure.lean` now proves the raw determinant-chart
weighted pushforward identity via Mathlib's Jacobian theorem. Lean names:
`ProductReductionStepRawTopologyTuple`,
`productReductionStepRawDetChartSet`,
`isOpen_productReductionStepRawDetChartSet`,
`nullMeasurableSet_productReductionStepRawDetChartSet`,
`productReductionStepTopologyTupleToChartRawOrder`,
`productReductionStepRawOrderJacobianCLM`,
`productReductionStepRawOrderJacobianAbsDet`, and
`map_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart_withDensity_abs_det`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-weighted-haar-cov.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-weighted-haar-cov.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-weighted-haar-cov.md`.
This proves only weighted additive-Haar transport to the image of the raw
determinant chart. It does not specialize to `volume`, identify that image
with the whole target determinant chart, transport the original DLN
source/prior measure, prove source coverage, construct normal crossings,
compute pole order, or extract an RLCT.

Latest A2 product-step determinant-chart image:
`ProductReductionStepMeasure.lean` now proves that the raw-order p. 13
product-step coordinate map sends the raw determinant chart onto the
raw-shaped target determinant chart. Lean names:
`ProductReductionStepRawCoordinates.topologyTuple_mem_rawDetChartSet`,
`productReductionStepRawCoordinatesOfTopologyTuple_of_topologyTuple`,
`productReductionStepChartCoordinatesOfRawOrderTopologyTuple`,
`productReductionStepChartCoordinatesOfRawOrderTopologyTuple_detChart`,
`productReductionStepChartCoordinatesOfRawOrderTopologyTuple_rawOrder`,
`ProductReductionStepChartCoordinates.rawOrderTopologyTuple_mem_rawDetChartSet`,
`mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart`,
`surjOn_productReductionStepTopologyTupleToChartRawOrder_detChart`,
`bijOn_productReductionStepTopologyTupleToChartRawOrder_detChart`,
`image_productReductionStepTopologyTupleToChartRawOrder_detChart`, and
`map_productReductionStepRawOrder_restrict_detChart_withDensity_absDet_eq_restrict_detChart`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-det-chart-image.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-det-chart-image.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-det-chart-image.md`.
This is only determinant-chart image identification and the corresponding
weighted Haar target rewrite. It does not transport the original DLN
source/prior measure, prove source coverage, construct normal crossings,
compute pole order, or extract an RLCT.

Latest A2 product-step Jacobian density positivity:
`ProductReductionStepMeasure.lean` now proves the determinant unitness and
strict positivity of the raw-order product-step Jacobian density on the raw
determinant chart. Lean names:
`productReductionStepRawOrderJacobianCLM_det_isUnit`,
`productReductionStepRawOrderJacobianAbsDet_pos`, and
`eventually_productReductionStepRawOrderJacobianAbsDet_pos_nhds`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-jacobian-density-pos.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-jacobian-density-pos.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-jacobian-density-pos.md`.
This does not prove density continuity, local boundedness above, source/prior
measure comparison, source coverage, normal crossings, pole order, or RLCT.

Latest A2 product-step Jacobian density continuity:
`ProductReductionStepMeasure.lean` now proves local continuity and two-sided
eventual unit bounds for the source-side forward raw-order product-step
Jacobian density at determinant-chart points. Lean names:
`continuousAt_productReductionStepRawOrderJacobianCLM_apply_of_mem_rawDetChartSet`,
`continuousAt_productReductionStepRawOrderJacobianCLM_of_mem_rawDetChartSet`,
`continuousAt_productReductionStepRawOrderJacobianAbsDet_of_mem_rawDetChartSet`,
`exists_pos_eventually_le_productReductionStepRawOrderJacobianAbsDet_nhds`,
and
`exists_pos_eventually_productReductionStepRawOrderJacobianAbsDet_le_nhds`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-jacobian-density-continuity.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-jacobian-density-continuity.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-jacobian-density-continuity.md`.
This does not prove chart-side inverse-density transport, original DLN
source/prior measure comparison, source coverage, normal crossings, pole
order, or RLCT.

Latest A2 product-step inverse Jacobian density:
`ProductReductionStepMeasure.lean` now proves local continuity, positivity,
and positive lower/upper eventual bounds for the chart-side reciprocal
raw-order product-step Jacobian density at target determinant-chart points.
Lean names:
`continuousAt_productReductionStepChartRawOrderToRawTopologyTuple_of_mem_rawDetChartSet`,
`productReductionStepRawOrderInverseJacobianDensity`,
`productReductionStepRawOrderInverseJacobianDensity_pos`,
`continuousAt_productReductionStepRawOrderInverseJacobianDensity_of_mem_rawDetChartSet`,
`exists_pos_eventually_le_productReductionStepRawOrderInverseJacobianDensity_nhds`,
and
`exists_pos_eventually_productReductionStepRawOrderInverseJacobianDensity_le_nhds`.
The reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-product-step-inverse-jacobian-density.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-inverse-jacobian-density.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-inverse-jacobian-density.md`.
This controls `|det D Phi(Phi^{-1}(y))|^{-1}` as a local unit.  It does not
prove an unweighted source-measure pushforward theorem, original DLN
source/prior measure comparison, source coverage, normal crossings, pole
order, or RLCT.

Latest A2 p.13 regular-coordinate inverse-density handoff:
`ProductReductionStepRegularDensity.lean` defines the concrete left-endpoint
p. 13 raw-shaped target tuple
`(Ctop(u),Dtail(x),F3(u),Ctop(u),F2(u),0,C0(x))`, proves centered
determinant-chart membership and self-base continuity, and composes this tuple
with the abstract inverse-density theorem to prove continuity and positivity
of the chart-side reciprocal density along it.  Reproduction and statement
card:
`threads/03-block-product-reduction/reproduction-a2-product-step-regular-coordinate-inverse-density.md`
and
`threads/03-block-product-reduction/statement-card-a2-product-step-regular-coordinate-inverse-density.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-step-regular-coordinate-inverse-density.md`.
This is not source coverage, original source/prior transport, unweighted
measure transport, normal crossings, pole order, or RLCT.

Latest A2 p.13 product-step inverse-density finite-integral handoff:
`RegularSuspensionLocalMeasure.lean` now specializes the existing p.13
continuous-density finite-integral theorem to the concrete chart-side inverse
product-step Jacobian density along `paperEndpointFixedBaseP13RawOrderTuple`.
It also provides the weighted signed-box residual-source version.  Lean names:
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_continuousAt_selfBase`
and
`exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_selfBase`.
Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-product-step-inverse-density-finite-integral-handoff.md`
and
`threads/03-block-product-reduction/statement-card-a2-product-step-inverse-density-finite-integral-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-product-step-inverse-density-finite-integral-handoff.md`.
This is a local finite-integral consumer only; it does not prove source
coverage, a product-step pushforward theorem, original source/prior transport,
signed-box density identification, normal crossings, pole order, or RLCT.

Latest A2 suffix-step raw-order inverse-density handoff:
`ProductReductionStepSuffixDensity.lean` defines the arbitrary suffix-step
raw-shaped target tuple
`chartLocalSuffixStateStepRawOrderTargetTuple` and proves determinant-chart
membership, raw tuple continuity, target tuple continuity, and chart-side
inverse-density continuity/positivity.  Lean names:
`continuousAt_productReductionStepTopologyTupleToChartRawOrder_of_mem_rawDetChartSet`,
`chartLocalSuffixStateStepRawOrderTargetTuple`,
`chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet`,
`continuousAt_chartLocalSuffixState_stepRawCoordinates_topologyTuple`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_of_raw`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity`,
`continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_of_fields`,
and
`chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_pos`.
Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-suffix-step-raw-order-inverse-density.md`
and
`threads/03-block-product-reduction/statement-card-a2-suffix-step-raw-order-inverse-density.md`.
Review:
`threads/03-block-product-reduction/review-a2-suffix-step-raw-order-inverse-density.md`.
This is local product-step chart/density infrastructure
only; it does not prove source coverage, product-chart construction for the
original DLN source, product-step pushforward, source/prior transport,
signed-box density identification, normal crossings, pole order, or RLCT.

Latest A2 raw-order inverse-density pushforward:
`ProductReductionStepMeasure.lean` now proves the unweighted raw
determinant-chart pushforward orientation for the p. 13 product-step map.
Lean names:
`productReductionStepRawOrderInverseJacobianDensity_apply_chartMap`,
`productReductionStepRawOrderJacobianAbsDet_mul_inverseJacobianDensity_apply_chartMap`,
and
`map_productReductionStepRawOrder_restrict_detChart_eq_withDensity_inverseJacobian`.
The proof uses the existing weighted additive-Haar COV identity and the
pointwise cancellation of the forward Jacobian density with the chart-side
reciprocal density after applying the raw-order map; it does not add an
inverse-map derivative theorem.  Reproduction, statement card, and review are
at
`threads/03-block-product-reduction/reproduction-a2-product-step-raw-order-inverse-density-pushforward.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-raw-order-inverse-density-pushforward.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-raw-order-inverse-density-pushforward.md`.
This is raw product-chart Haar transport only. It does not prove original DLN
source/prior transport, p.13 source-chart construction, source coverage,
signed-box density identification, regular suspension, normal crossings, pole
order, or RLCT.

## Ledger rules

- `Source ref` must eventually include PDF page numbers or stable local source
  anchors.
- `Lean target/status` records names only after the statement exists. Do not
  reserve impressive names before the statement is precise.
- `Reproduction/status` records the pen-and-paper derivation and independent
  check. A substantial calculation with this field pending is not
  formalisation-ready.
- `Review/status` is independent from build status. A theorem can be green and
  still fail fidelity or bedrock.
- Cited and deferred boundaries must appear in this table and in the matching
  claim card.
- Source references come from Aoyagi's PDF for this expedition. Do not fill
  ledger gaps from the quiver paper.

Latest A2 p.13 raw product-step preimage:
`ProductReductionStepRegularDensity.lean` now proves the pointwise raw
preimage algebra for the left-endpoint p.13 product step.  Lean names:
`paperEndpointFixedBaseP13RawPreimageTuple`,
`paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet`,
`paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet_center`, and
`productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple`.
The source tuple is `(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)`, the target tuple is
`(Ctop,Dtail,F3,Ctop,F2,0,C0)`, and the determinant hypothesis is
`IsUnit det(Ctop)`.  Reproduction and statement card are at
`threads/03-block-product-reduction/reproduction-a2-p13-raw-product-step-preimage.md`
and
`threads/03-block-product-reduction/statement-card-a2-p13-raw-product-step-preimage.md`;
review passed at
`threads/03-block-product-reduction/review-a2-p13-raw-product-step-preimage.md`.
This is raw product-chart algebra only: no source coverage, original p.13
source-chart construction, source/prior transport, signed-box density,
product-measure pushforward, normal crossings, pole order, or RLCT.

Latest A2 p.13 product-coordinate left-step raw preimage:
`ProductReductionStepRegularDensity.lean` now proves that the actual
left-endpoint suffix-step coordinates of the constructed p.13 multi-edge
product-coordinate family are the explicit raw preimage tuple.  Lean names:
`paperEndpointFixedBaseP13ProductCoordinateMatrixFamily`,
`p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple`, and
`p13ProductCoordinateLeftStepRawOrderTargetTuple_eq_rawOrderTuple`.  The raw
suffix-step tuple is `(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)`, and under
`IsUnit det(Ctop)` the raw-order target tuple is
`(Ctop,Dtail,F3,Ctop,F2,0,C0)`.
Reproduction and statement card are at
`threads/03-block-product-reduction/reproduction-a2-p13-product-coordinate-left-step-raw-preimage.md`
and
`threads/03-block-product-reduction/statement-card-a2-p13-product-coordinate-left-step-raw-preimage.md`;
review passed after low-severity naming and stale-note repairs at
`threads/03-block-product-reduction/review-a2-p13-product-coordinate-left-step-raw-preimage.md`.
This is pointwise product-coordinate algebra only: no source coverage,
original p.13 source-chart construction, source/prior transport, signed-box
density, product-measure pushforward, regular-suspension certification,
normal crossings, pole order, or RLCT.

Latest A2 p.13 left-step conditional raw pushforward consumer:
`ProductReductionStepMeasure.lean` now proves
`aemeasurable_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart`
`ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict`, and
`map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian`, the
generic composition consumer for the raw-order inverse-density pushforward
under an explicit raw source pushforward hypothesis.  Chart null-measurability,
raw-order map a.e.-measurability, and raw-chart support are internal.
`ProductReductionStepRegularDensity.lean`
adds `p13ProductCoordinateLeftStepRawTopologyTuple`,
`paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one`,
`paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero`,
`p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one`,
`p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero`,
`ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart`,
`ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart`,
`map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map`, and
`map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map`.
The public p.13 theorem assumes
`Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
m.restrict rawDetChart` and concludes the raw-order target tuple has density
`productReductionStepRawOrderInverseJacobianDensity` over the restricted raw
Haar measure.  The `Ctop` determinant-unit a.e. fact is derived from raw-chart
support under the same supplied raw pushforward; it is no longer a separate
consumer input.
The section facts record that the p.13 raw preimage fixes raw `C1 = I` and raw
`A3 = 0`; in nontrivial raw `C1` or `A3` directions this is lower-dimensional,
so p.13 should not be read as a proof of the full raw-Haar pushforward.
Reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-conditional-raw-pushforward-consumer.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-conditional-raw-pushforward-consumer.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-conditional-raw-pushforward-consumer.md`.
The follow-up section-guardrail review is at
`threads/03-block-product-reduction/review-a2-p13-left-step-raw-section-guardrail.md`.
The follow-up raw-chart-support review is at
`threads/03-block-product-reduction/review-a2-p13-left-step-ctop-from-raw-chart-support.md`.
This is a conditional measure consumer only: no proof of the supplied raw
pushforward, original source/prior transport, source coverage, signed-box
density identification, product-measure pushforward, regular-suspension
certification, normal crossings, pole order, or RLCT.

Latest A2 p.13 left-step raw tuple measurability:
`ChartTopology.lean` now proves
`measurable_chartLocalSuffixState_residualProduct_real` and
`measurable_chartLocalSuffixState_residualBlock_real`.
`ProductReductionStepRegularDensity.lean` now proves
`measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix`,
`aemeasurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix`,
`measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix`,
`aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix`,
and
`map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix`.
The result derives the raw tuple a.e.-measurability premise from fixed-base
edge-matrix measurability, but still assumes the raw source pushforward to
`m.restrict rawDetChart`.
Reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-raw-tuple-measurability.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-raw-tuple-measurability.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-raw-tuple-measurability.md`.
This is finite Borel bookkeeping only: no proof of the supplied raw
pushforward, original source/prior transport, source coverage, signed-box
density identification, product-measure pushforward, regular-suspension
certification, normal crossings, pole order, or RLCT.

Latest A2 p.13 left-step section-image measure:
`ProductReductionStepRegularDensity.lean` now proves
`map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix`.
Under fixed-base edge-matrix measurability and a.e. raw determinant-chart
support for the actual left-step raw tuple `X`, Lean proves
`Measure.map Y eta = Measure.map Phi (Measure.map X eta)` for the p.13
raw-order target tuple `Y` and the raw-order product-step map `Phi`.  This is
the section-image theorem recommended by xhigh source/API and pen-and-paper
scouts after rejecting the full raw-Haar pushforward as false for p.13.
Reproduction and statement card are at
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-section-image-measure.md`
and
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-section-image-measure.md`;
review passed at
`threads/03-block-product-reduction/review-a2-p13-left-step-section-image-measure.md`.

Latest A2 p.13 left-step local raw-det support:
`ProductReductionStepRegularDensity.lean` now proves local raw
determinant-chart support for the actual p.13 left-step section.  Lean names:
`p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet`,
`exists_pos_radius_le_forall_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet`,
`ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball`,
and
`exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball`.
For sufficiently small regular coordinates `u`, `det Ctop(u)` is a unit, so
the actual raw tuple `(I,Dtail,F3,Ctop,-Ctop*F2,0,C0)` lies in the raw
determinant chart.  The a.e. corollaries turn regular-coordinate ball support
into the raw-chart support hypothesis for the section-image theorem.
Reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-local-raw-det-support.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-local-raw-det-support.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-local-raw-det-support.md`.
This is section-domain support only: no full raw-Haar pushforward, source
coverage, source/prior transport, signed-box density identification,
regular-suspension certification, normal crossings, pole order, or RLCT.

Latest A2 p.13 left-step small-ball section image:
`ProductReductionStepRegularDensity.lean` now proves
`exists_pos_radius_le_map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_ae_regular_mem_ball`.
It combines the local raw-det support radius with the section-image theorem:
under fixed-base edge-matrix measurability and for a sufficiently small
regular-coordinate ball, a local `(x,u)` measure supported a.e. in that ball
satisfies
`Measure.map Y eta = Measure.map Phi (Measure.map X eta)`.
Reproduction, statement card, and review are at
`threads/03-block-product-reduction/reproduction-a2-p13-left-step-small-ball-section-image.md`,
`threads/03-block-product-reduction/statement-card-a2-p13-left-step-small-ball-section-image.md`,
and
`threads/03-block-product-reduction/review-a2-p13-left-step-small-ball-section-image.md`.
This is section-image bookkeeping only: no full raw-Haar pushforward, source
coverage, source/prior transport, density identification, normal crossings,
pole order, or RLCT.

Latest A2 p.13 raw pushforward source-boundary audit:
direct source extraction and rendered-page checking of Aoyagi PDF pp. 5-14,
plus xhigh source, Lean-boundary, and pen-and-paper audits, killed the proposed
source-backed theorem
`Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
m.restrict rawDetChart`.  The source contains the generic Hironaka substitution
on p.6, Lemma 2/Theorem 3 block substitutions on pp.10-13, and the p.13 LCT
equality, but no concrete p.13 source/product-coordinate pushforward,
Jacobian/density transport, raw determinant-chart image theorem, or coverage
theorem.  The positive-rank section obstruction explains why the theorem
cannot be recovered from the raw section: the p.13 tuple fixes `C1 = I` and
`A3 = 0`, while the raw determinant chart permits open subsets with `C1 != I`.
The section obstruction disappears only in the `rho = 0` exception, which
still does not prove the remaining source-map pushforward.  No Lean theorem
was added; the existing inverse-density consumers keep raw pushforward
supplied, and the section-image theorem remains the honest replacement.
Audit:
`threads/03-block-product-reduction/source-audit-a2-p13-left-step-raw-pushforward-boundary.md`.

Latest A2 p.13 local source coverage boundary:
`threads/03-block-product-reduction/source-audit-a2-p13-local-source-coverage-boundary.md`
records that the source-stratum local-subset local-source theorem is only a
consumer.  Aoyagi pp. 10-13 do not state the local inclusion into
`localSource`, source/image equality, determinant-chart finite coverage, a
local inverse with passive variables, source-measure pushforward, or
density/Jacobian transport.  The current proved Lean facts remain forward
p.13 source-rank image membership, local raw-section support, section-image
measure identity, and conditional finite-integral handoffs.  Reverse
source-rank coverage and p.13 source transport are still supplied/deferred.

Latest A2 product-coordinate residual-rank readback:
`RegularSuspensionCoordinates.lean` proves
`paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_residualBlock_rank_of_mem_sourceRankStratum`.
It consumes source-rank membership for the constructed p.13 product-coordinate
family and `IsUnit(det Ctop(u))`, then derives
`rank(residualBlock Ebase p) = rEdge p - r` for every edge.  The proof is
finite rank algebra only and uses the existing p.13 endpoint/middle block-rank
lemmas.  It is not source coverage, local inverse, source/image equality,
measure transport, normal crossings, pole order, or RLCT.

Latest A5 Lemma 5 first-nonbase cardinal bound:
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le` is now
proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.  It consumes
a finite supplied candidate set, terminal binary-prefix-delta chain data for
each candidate, supplied base-value interval membership, and supplied
injectivity of the deterministic first-nonbase-or-base selector.  It produces
the upper bound `candidates.card <= a*(ell-a)+1` by building an
`AoyagiLemma5CountDatumClassifier` and applying the existing counted-datum
classifier cardinal theorem.

This is a finite cardinality adapter only.  It is not a source construction of
Aoyagi's branch family, a proof of canonical classifier/injectivity, a
back-to-label/no-extra theorem, a finite minimum-to-`lambda` bridge, pole
order, normal crossings, or RLCT.

Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-first-nonbase-cardinal-bound-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-first-nonbase-cardinal-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-first-nonbase-cardinal-bound-a5.md`.

Follow-up order-notation handoff:
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le_theorem2OrderFormula`
is proved in
`lean/DLNFibre/DLN/Aoyagi/Lemma5FirstNonbaseOrderBridge.lean`.  It restates
the same finite first-nonbase bound under Definition 3 ceiling data as
`candidates.card <= data.theorem2OrderFormula`.  It does not construct the
source classifier, prove selector injectivity, terminal exactness, pole order,
normal crossings, or RLCT.
Artifacts:
`threads/05-arithmetic-tail/reproduction-lemma5-first-nonbase-order-formula-bound-a5.md`
and
`threads/05-arithmetic-tail/statement-card-a5-lemma5-first-nonbase-order-formula-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-first-nonbase-order-formula-bound-a5.md`.

Latest A4 Case 2 finite raw-pivot chart-family boundary:
`SelectedEntryNormalCrossing.lean` now defines
`Case2FiniteRawPivotChartRegular`,
`Case2FiniteRawPivotTransitionRegular`, and proves
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.finiteRawPivotChartFamilyBoundary`.
This replaces the syntactic `True`-predicate boundary witness with predicates
carrying the finite selected-entry chart formula, finite center-ideal
principalization, and finite affine overlap pair.

Labels:

- Proved: finite residual-block nonemptiness under continuation, raw-pivot
  selected-entry chart formula, finite center-ideal principalization, finite
  affine ordered-pair overlap certificates, and the resulting nontrivial
  `Case2ResidualBlockChartFamilyBoundary`.
- Cited: Aoyagi's displayed Case 2 selected-entry blow-up calculation as the
  source anchor for the finite formula.
- Deferred: analytic atlas coverage, analytic transition regularity,
  source/suffix production, analytic Jacobian compatibility, normal crossings,
  pole order, and RLCT extraction.

Artifacts:
`threads/04-blow-up-certificate/reproduction-case2-finite-raw-pivot-chart-family-boundary-a4.md`,
`threads/04-blow-up-certificate/statement-card-a4-case2-finite-raw-pivot-chart-family-boundary.md`,
and
`threads/04-blow-up-certificate/review-case2-finite-raw-pivot-chart-family-boundary-a4.md`.

Latest A2 p.13 passive-variable local source chart boundary:
`threads/03-block-product-reduction/reproduction-a2-p13-passive-variable-local-source-chart-boundary.md`
records a source-boundary audit, with review at
`threads/03-block-product-reduction/review-a2-p13-passive-variable-local-source-chart-boundary.md`.
It proves no new Lean theorem.  The audit confirms that the full one-step raw
determinant chart is already formalised, the p.13 reduced tuple is a section
fixing raw `C1=I` and `A3=0`, and a retained-passive multi-step source chart
would be a new construction needing explicit source map, coverage,
product-measure, and density/Jacobian fields.  Treat any theorem deriving
full raw-Haar pushforward from the p.13 section as rejected by this boundary.

Latest A2 product-step A1 formal inverse:
`ProductReduction.lean` proves the record-level p.13 one-step inverse laws
under the weaker hypothesis `IsUnit A1.det`:
`productReductionStepCoordinate_left_inverse_of_isUnit_A1` and
`productReductionStepCoordinate_right_inverse_of_isUnit_A1`.  The older
determinant-chart inverse theorems remain wrappers for chart-domain use.
Artifacts:
`threads/03-block-product-reduction/reproduction-a2-product-step-a1-formal-inverse.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-a1-formal-inverse.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-a1-formal-inverse.md`.
No derivative/measure chart-domain weakening, source coverage, source-measure
transport, normal crossings, pole order, or RLCT is proved.

Latest A2 product-step formal Jacobian A1 unit:
`ProductReductionStepJacobian.lean` proves A1-only versions of the full p.13
formal tangent inverse-composition laws, raw/chart `LinearEquiv`, raw-order
`LinearEquiv`, and finite raw-order determinant-unit theorem.  Main Lean
names:
`productReductionStepFormalJacobianInverseFormula_formula_chartBase_of_isUnit_A1`,
`productReductionStepFormalJacobianFormula_inverseFormula_chartBase_of_isUnit_A1`,
`productReductionStepFormalJacobianEquiv_of_isUnit_A1`,
`productReductionStepFormalJacobianRawOrderEquiv_of_isUnit_A1`, and
`productReductionStepFormalJacobianRawOrder_det_isUnit_of_isUnit_A1`.
The older determinant-chart names remain wrappers with the old visible
`hC1 hA1` arguments.
Artifacts:
`threads/03-block-product-reduction/reproduction-a2-product-step-formal-jacobian-a1-unit.md`,
`threads/03-block-product-reduction/statement-card-a2-product-step-formal-jacobian-a1-unit.md`,
and
`threads/03-block-product-reduction/review-a2-product-step-formal-jacobian-a1-unit.md`.
This is finite formal tangent algebra only.  It does not weaken analytic
derivative or measure determinant-chart hypotheses, does not prove `C1*A1`
invertible from `A1`, and does not prove source coverage, source-measure
transport, normal crossings, pole order, or RLCT.

Latest A6 Definition 3 equal-width finite Theorem 2 formula:
`FinalFormula.lean` proves `aoyagiSelectedWidthPairSum_const`, and
`Definition3Bridge.lean` proves
`AoyagiDefinition3SourceData.exists_consecutive_equalWidth_theorem2Formula_of_constant_reducedWidth_decomposition`.
For the source-backed equal-width branch, the theorem returns consecutive
source data, explicit ceiling data, order `a*(L-a)+1`, selected pair sum
`((L+1)*L*w^2)/2`, and the unfolded finite lambda formula.  The branch
selection audit remains in force: this is not arbitrary Definition 3
source-data quantification.
Artifacts:
`threads/06-dln-translation/reproduction-definition3-equal-width-theorem2-formula-a6.md`,
`threads/06-dln-translation/statement-card-a6-definition3-equal-width-theorem2-formula.md`,
and
`threads/06-dln-translation/review-definition3-equal-width-theorem2-formula-a6.md`.
No Eq5 production, chart production, normal crossings, pole order, or RLCT is
proved.

Latest A5 Eq5 endpoint first-nonbase upper bound:
`threads/05-arithmetic-tail/reproduction-lemma5-terminal-minimum-counted-datum-classifier-source-attempt-a5.md`
checks the terminal-minimum counted-datum classifier source route against
Aoyagi Lemma 5, PDF pp. 24-27.  Verdict: the full
`TC.TerminalMinimumCountDatumClassifier` is not source-constructed by the
printed paragraph.  The interval count is present, but `classify`, `injOn`,
and back-to-label/no-extra fields remain supplied.

Lean theorem:
`AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_le_of_eq5EndpointChain_firstInteriorNonbase`
is proved in `lean/DLNFibre/DLN/Aoyagi/Lemma5Eq5TerminalClassifier.lean`.
It consumes explicit Eq5 endpoint-chain data for every terminal-minimum label
and supplied injectivity of the deterministic first-nonbase-or-base selector,
then derives `TC.terminalMinimumLabels.card <= a*(N+1-a)+1`.
Statement card:
`threads/05-arithmetic-tail/statement-card-a5-lemma5-eq5-endpoint-first-nonbase-upper-bound.md`.
Review:
`threads/05-arithmetic-tail/review-lemma5-eq5-endpoint-first-nonbase-upper-bound-a5.md`.

This is a conditional upper-bound hardening only.  It does not prove selector
injectivity, branch-label injectivity, no-extra coverage, terminal-label
exactness, pole order, normal crossings, or RLCT.

Latest A2 retained-passive transformed-edge reconstruction:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq`.
Given retained-passive blocks
`M_p=[A1_p,-A1_p F2_p; A3_p,C_p-A3_p F2_p]`, fixed-base edges
`E_p=[I,F2_{p+1};0,I]*M_p`, the terminal condition `F2_last=0`, and unit
determinants for every `A1_p`, the deterministic suffix-state recursion has
`transformedEdge E p (suffixState E last p.succ) = M_p` for every edge.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-transformed-edge-reconstruction.md`.
This is finite transformed-edge reconstruction only: no endpoint recovery for
`A1_0` or `A3_last`, source-rank coverage, source/image equality,
source-measure pushforward, density/Jacobian theorem, normal crossings, pole
order, or RLCT.

Latest A2 retained-passive Ctop determinant chart tracking:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_Ctop`,
`ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc`,
and
`ChartLocalSuffixState.suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix`.
For the same retained-passive fixed-base edges, the recursive suffix-state top
block satisfies `Ctop_p = Ctop_{p+1} * A1_p`; hence the recursive `Ctop`
determinants are units when all `det(A1_p)` are units.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-det-chart.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-det-chart.md`.
This is finite determinant-chart bookkeeping only for a full reconstructed
family with all `A1_p` determinant-unit: no endpoint recovery for `A1_0` or
`A3_last`, no retained-passive coordinate-domain theorem with active `Ctop_0`
and passive `A1_p` for `p > 0`, no coverage, no source/image theorem, no
source-measure pushforward, no density/Jacobian theorem, no normal crossings,
no pole order, and no RLCT.

Latest A2 retained-passive A1 readback:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_A1_eq_suffixState_Ctop_inv_mul_Ctop`.
For a full determinant-unit retained-passive `A1` family, adjacent recursive
top blocks recover each supplied factor by
`A1_p = Ctop_{p+1}^-1 * Ctop_p`.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1-readback.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1-readback.md`.
This is constructor-side finite readback only: at `p=0`, `A1_0` is still an
input and `hA1` assumes its determinant is a unit.  It is not yet the
retained-passive coordinate-domain theorem with active `Ctop_0=I+X` and
passive `A1_p` for `p>0`; no `A3_last` recovery, coverage, source/image
theorem, source-measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT is proved.

Latest A2 retained-passive D/L recurrences:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.schurResidualBlock_retainedPassiveTransformedEdge`,
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_D`,
`ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix_castSucc`,
`ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix`,
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_L`, and
`ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_lowerLeftBlock_L`.
For retained-passive blocks, the Schur residual is `C_p`, the residual field is
`D_p=D_{p+1}*C_p` and `D_i=residualFactorProduct C last i`, and the one-step
left-multiplier lower-left contribution is
`-(D_{p+1}*A3_p*(Ctop_{p+1}*A1_p)^-1)`.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-d-l-recurrence.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-d-l-recurrence.md`.
This is finite suffix-state bookkeeping only: no iterated F3 sum, no
`A3_last` recovery, no coordinate-domain theorem, no source coverage,
source/image theorem, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive lower-left L recursion:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc`
and
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop`.
These specialize the one-step lower-unitriangular update to actual suffix
states and rewrite the contribution using current `Ctop_p`.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-l-lowerleft-recursion.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-l-lowerleft-recursion.md`.
This is one-edge recursive bookkeeping only: no iterated F3 sum, no
`A3_last` solve, no coordinate-domain theorem, no source coverage, no
source/image theorem, no measure pushforward, no density/Jacobian theorem, no
normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive lower-left L tail sum:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveLowerLeftTailSum`,
`ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_self`,
`ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_castSucc`,
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum`,
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_tailSum`,
`ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_self`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_castSucc`,
`ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_eq_productTailSum`,
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum`,
and
`ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum`.
These iterate the one-edge recurrence into a recursive finite tail sum and an
explicit product-tail form.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-l-tail-sum.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-l-tail-sum.md`.
This is finite suffix-state algebra only: no `A3_last` solve, no coordinate
domain theorem, no source coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive final-edge endpoint solve:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last` and
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_last_eq_of_A3_eq_neg_target_mul_Ctop`.
For a nonempty edge family, the last product-tail term is
`-(I*A3_last*Ctop_last^-1)`, and under `IsUnit Ctop_last.det`,
`A3_last=-G*Ctop_last` makes that last tail equal to `G`.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a3-last-endpoint-solve.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a3-last-endpoint-solve.md`.
This is local endpoint algebra only: no prefix `G=F3_0+prefix`, no coordinate
domain theorem, no source coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive `A3_last` prefix target:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveA3WithoutLast`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_withoutLast_last`,
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last`,
and
`ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq`.
The final-zeroed product tail is the signed earlier contribution; choosing
`A3_last=-(F3-EarlyTail)*Ctop_last` under `IsUnit Ctop_last.det` makes the full
source tail equal `F3`.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a3-last-prefix-target.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a3-last-prefix-target.md`.
This is finite tail algebra only: no coordinate-domain theorem, active
`Ctop_0`/`A1_0` reconstruction, source coverage, source/image theorem, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive `A1_0` endpoint target:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst`,
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_mul_first`,
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive`,
`ChartLocalSuffixState.retainedPassiveCtopProduct_zero_eq_target_of_A1_zero_eq`,
`ChartLocalSuffixState.retainedPassiveA1_zero_det_isUnit_of_A1_zero_eq_tail_inv_mul`,
`ChartLocalSuffixState.retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul`,
and
`ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq`.
For `Tail=A1_last*...*A1_1`, the full top-left product splits as
`Tail*A1_0`; if `A1_0=Tail^-1*Ctop`, the product and the source-left
suffix-state top block are `Ctop`.  The passive-tail determinant unit is
proved from pointwise passive units for all `p != 0`, and `det(Ctop)` unit
then gives the solved `A1_0` unit.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1-first-endpoint-target.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1-first-endpoint-target.md`.
This is finite top-left endpoint algebra only: no full coordinate-domain
theorem, `F2` readback, combined `A3_last`/`F3` source-map theorem, source
coverage, source/image theorem, measure pushforward, density/Jacobian theorem,
normal crossings, pole order, or RLCT.

Latest A2 retained-passive active endpoint package:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointFields_eq_targets`.
For retained-passive fixed-base edges satisfying the solved `A1_0` and
`A3_last` endpoint formulas, the source-left suffix state reads back
`F2_0`, `Ctop`, and `F3`, and every transformed edge is the prescribed
retained-passive transformed block at suffix state `S_{p+1}`.  Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-active-endpoint-package.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-active-endpoint-package.md`.
This is endpoint fixed-base packaging only: no bundled coordinate domain,
two-sided local inverse, source coverage, source/image theorem, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive transformed-edge readbacks:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveTransformedEdge_readbacks` and
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_readbacks`.
For the retained-passive transformed block
`M_p=[A1_p,-A1_p F2_p;A3_p,C_p-A3_p F2_p]`, Lean reads back `A1_p`,
`-A1_p*F2_p`, `F2_p`, `A3_p`, and `C_p`; the `F2_p` readback uses
`IsUnit det(A1_p)` to cancel `A1_p^-1*A1_p`.  The fixed-base version rewrites
the deterministic transformed edge to `M_p` before applying the block theorem.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-transformed-edge-readbacks.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-transformed-edge-readbacks.md`.
This is per-edge finite readback only: no bundled coordinate domain,
two-sided local inverse, source coverage, source/image theorem, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive fixed-base readback package:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_activeEndpointAndEdgeReadbacks_eq_targets`.
Under the solved endpoint hypotheses for `A1_0` and `A3_last`, plus
`F2_last=0`, passive `A1_p` unit hypotheses for `p != 0`, and `det(Ctop)` unit,
the fixed-base edge family has source-left readbacks `-S_0.B=F2_0`,
`S_0.Ctop=Ctop`, and `lowerLeft(S_0.L)=F3`; for each edge, the deterministic
transformed edge reads back `A1_p`, `F2_p`, `A3_p`, and `C_p`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-fixed-base-readback-package.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-fixed-base-readback-package.md`.
This is finite fixed-base packaging only: no bundled coordinate domain,
two-sided local inverse, source coverage, source/image theorem, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive solved family constructors:
`RetainedPassiveCoordinates.lean` proves the solved endpoint constructor layer:
`ChartLocalSuffixState.retainedPassiveSolvedA1`,
`ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_solvedA1`,
`ChartLocalSuffixState.retainedPassiveSolvedA1_zero_eq_tail_inv_mul`,
`ChartLocalSuffixState.retainedPassiveSolvedA1_passive_det_isUnit`,
`ChartLocalSuffixState.retainedPassiveSolvedA3`,
`ChartLocalSuffixState.retainedPassiveA3WithoutLast_solvedA3`,
`ChartLocalSuffixState.retainedPassiveSolvedA3_last_eq_target`, and
`ChartLocalSuffixState.retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets`.
The wrapper theorem builds solved full `A1` and `A3` families from passive seed
data and proves the same fixed-base active/per-edge readbacks, without
assuming endpoint equations for `A1_0` or `A3_last`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-family-constructors.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-solved-family-constructors.md`.
This is constructor-side finite algebra only: no bundled coordinate domain,
two-sided local inverse, source coverage, source/image theorem, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive coordinate-data source map:
`RetainedPassiveCoordinates.lean` defines
`ChartLocalSuffixState.RetainedPassiveCoordinateData` and its projections
`solvedA1`, `solvedA3`, and `edgeMatrix`.  The theorem
`ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets`
proves that the bundled data's fixed-base edge family has the active
source-left and per-edge transformed-edge readbacks under the finite side
conditions `F2_last=0`, passive `A1seed` determinant units, and `det(Ctop)`
unit.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-coordinate-data-source-map.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-coordinate-data-source-map.md`.
This is a finite algebraic source-map object only: no open coordinate domain,
topology, measure, Jacobian, local inverse, source coverage, source/image
theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive recoverable readbacks:
`RetainedPassiveCoordinates.lean` proves
`ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverableReadbacks_eq_targets`
and
`ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_recoverable_ext`.
The readback theorem recovers exactly the non-dummy retained coordinates from
the bundled edge family under the finite side conditions: source-left `F2_0`,
`Ctop`, and `F3`; per-edge `A1seed_p` for `p != 0`, `F2_{p.castSucc}`,
`A3seed_p` for `p != Fin.last M`, and `C_p`.  The extensionality theorem says
equal edge families force equality of these recoverable fields, while omitting
the dummy seed fields `A1seed 0` and `A3seed (Fin.last M)`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-recoverable-readbacks.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-recoverable-readbacks.md`
passed.
This is finite recoverable-coordinate algebra only: no full record
injectivity, open coordinate domain, topology, measure, Jacobian, source-rank
coverage, source/image theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive nonredundant coordinate data:
`RetainedPassiveCoordinates.lean` defines
`ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData`, with fields
`A1passive`, nonterminal `F2`, `A3passive`, `C`, `Ctop`, and `F3`.  The helper
projections `A1seed`, `F2full`, `A3seed`, and `toCoordinateData` embed this
dummy-free object into the older bundled `RetainedPassiveCoordinateData` by
setting `A1seed 0=0`, `A3seed (Fin.last M)=0`, and
`F2full (Fin.last (M+1))=0`.

The theorem
`ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_readbacks_eq_targets`
recovers exactly the stored fields from `data.edgeMatrix`, under passive
`A1passive` determinant-unit hypotheses and `det(Ctop)` unit.  The theorem
`ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.edgeMatrix_ext`
proves full equality of two nonredundant records from equality of their edge
families, with the same side conditions on both records.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-nonredundant-coordinate-data.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-nonredundant-coordinate-data.md`
passed.
This is finite coordinate algebra only: no open coordinate domain, topology,
determinant-unit neighborhood, source-rank coverage, source/image theorem,
measure pushforward, density/Jacobian theorem, normal crossings, pole order,
or RLCT.

Latest A2 retained-passive determinant-chart domain:
`RetainedPassiveCoordinates.lean` defines
`ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.detChart` and
`detChartSet`.  The predicate packages exactly the side conditions used by
the nonredundant readback theorem: `det(Ctop)` unit and determinant-unit
passive `A1passive` blocks.  Lean proves the domain-scoped wrappers
`toCoordinateData_passiveA1_units_of_detChart`,
`edgeMatrix_readbacks_eq_targets_of_detChart`,
`edgeMatrix_ext_of_detChart`, and `injOn_edgeMatrix_detChartSet`.

`RetainedPassiveCoordinatesTopology.lean` gives the nonredundant coordinate
record the product topology on `(A1passive,F2,A3passive,C,Ctop,F3)` and proves
`isOpen_detChartSet` plus `detChartSet_mem_nhds`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-det-chart-domain.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-det-chart-domain.md`
passed.
This is coordinate-domain topology only: no image openness, continuity of
`edgeMatrix`, source-rank coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive projection continuity:
`RetainedPassiveCoordinatesTopology.lean` proves product-topology continuity
for every stored field of `RetainedPassiveNonredundantCoordinateData`:
`continuous_A1passive`, `continuous_F2`, `continuous_A3passive`,
`continuous_C`, `continuous_Ctop`, and `continuous_F3`.

The same file proves componentwise continuity of the dummy-slot embeddings
`continuous_A1seed`, `continuous_F2full`, and `continuous_A3seed`.  Each
component is either one of the stored projections or a constant zero map.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-projection-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-projection-continuity.md`
passed.

This is a staging topology layer only: no continuity of `solvedA1`,
`solvedA3`, `toCoordinateData`, or `edgeMatrix`; no image openness,
source-rank coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive solved-A1 continuity:
`RetainedPassiveCoordinatesTopology.lean` proves
`RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA1TailAfterFirst`,
continuity of the passive top-left tail product as a function of the
nonredundant coordinate data.

It also proves
`RetainedPassiveNonredundantCoordinateData.continuous_solvedA1_detChart_subtype`:
for every `p : Fin (M+1)`, the map
`data ↦ (data.1.toCoordinateData).solvedA1 p` is continuous on the subtype
`{data // data.detChart}`.  The zero component uses inverse continuity on the
tail determinant-unit locus; nonzero components reduce to `A1seed`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-a1-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-solved-a1-continuity.md`
passed.

This is solved-top-left endpoint continuity only: no continuity of
`solvedA3`, `toCoordinateData`, or `edgeMatrix`; no image openness,
source-rank coverage, source/image theorem, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive solved-A3 continuity:
`RetainedPassiveCoordinatesTopology.lean` proves
`continuous_retainedPassiveA3WithoutLast`, `continuous_residualFactorProduct_C`,
`solvedA1_det_isUnit_of_detChart`,
`continuous_residualFactorProduct_solvedA1_detChart_subtype`,
`residualFactorProduct_solvedA1_det_isUnit_of_detChart`,
`continuous_retainedPassiveLowerLeftProductTailSum_detChart_subtype`, and
`continuous_solvedA3_detChart_subtype`.

The final solved `A3` component is continuous because the early lower-left
tail sum is a finite continuous sum and the solved-`A1` product in each inverse
factor is determinant-unit on the determinant-chart subtype.  Non-final
components reduce to `A3seed`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-solved-a3-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-solved-a3-continuity.md`
passed.

This completes endpoint-family continuity only: no continuity of `edgeMatrix`;
no image openness, source-rank coverage, source/image theorem, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive edge-matrix continuity:
`RetainedPassiveCoordinatesTopology.lean` proves
`continuous_edgeMatrix_detChart_subtype_apply` and
`continuous_edgeMatrix_detChart_subtype`.

For each edge `p`, the proof unfolds the nonredundant source map to the
fixed-base block formula and composes the already-proved continuity of
`solvedA1 p`, `solvedA3 p`, `F2full p.castSucc`, `F2full p.succ`, and `C p`.
The second theorem is the Pi-family continuity wrapper.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-edge-matrix-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-edge-matrix-continuity.md`
passed.

This is source-map continuity on `{data // data.detChart}` only: no image
openness, source-rank coverage, source/image theorem, local homeomorphism,
measure pushforward, density/Jacobian theorem, normal crossings, pole order,
or RLCT.

Latest A2 retained-passive source-readback object:
`RetainedPassiveCoordinates.lean` proves the finite inverse packaging names
`ext_fields`, `sourceReadbackSuffixState`,
`sourceReadbackTransformedEdge`, `sourceReadback`, and
`sourceReadback_edgeMatrix_eq`.

The readback map is total on retained-passive-shaped edge families.  On the
image of the determinant-chart source map, it recovers the original
nonredundant coordinates fieldwise.  The proof uses the already proved
`edgeMatrix_readbacks_eq_targets_of_detChart`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-readback-object.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-readback-object.md`
passed.

This is finite readback packaging only: no arbitrary edge-family image
membership, image openness, source-rank coverage, source/image theorem, local
homeomorphism, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive source-readback continuity:
`RetainedPassiveCoordinates.lean` defines
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart`, the
source-side recursive determinant predicate for the deterministic readback
suffix states.

`RetainedPassiveCoordinatesTopology.lean` proves
`continuousAt_sourceReadbackSuffixState_fields`,
`continuousAt_sourceReadbackTransformedEdge`,
`continuousAt_sourceReadback`, and
`continuous_sourceReadback_sourceRecursiveDetChart_subtype`.  The main theorem
is pointwise `ContinuousAt` under `ContinuousAt E x0` and
`sourceRecursiveDetChart (E x0)`; the subtype theorem is only a corollary.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-readback-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-readback-continuity.md`
passed.

This is finite readback continuity only: no arbitrary edge-family image
membership, image openness, source-rank coverage, source/image theorem, local
homeomorphism, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive source-recursive reconstruction spine:
`ProductReduction.lean` proves the generic block-algebra lemma
`fromBlocks_schurReadbacks_eq`: on an invertible selected top-left corner,
one-step Schur readbacks reassemble the original block matrix.

`RetainedPassiveCoordinates.lean` proves the first source-side reconstruction
spine under `sourceRecursiveDetChart`:
`sourceReadbackSuffixState_Ctop_det_isUnit_of_sourceRecursiveDetChart`,
`sourceReadback_detChart_of_sourceRecursiveDetChart`,
`sourceReadback_F2full_eq_neg_sourceReadbackSuffixState_B`,
`sourceReadbackSuffixState_Ctop_castSucc`,
`sourceReadback_A1Tail_eq_sourceReadbackSuffixState_Ctop_of_ne_zero`,
`sourceReadback_A1TailAfterFirst_eq_sourceReadbackSuffixState_Ctop_succ_zero`,
and `sourceReadback_solvedA1_eq_topLeftCorner`.

These theorems prove determinant propagation to all source suffix `Ctop`
blocks, retained-passive determinant-chart membership of `sourceReadback E`,
the `F2full = -B` readback recurrence, and solved-`A1` reconstruction from
visited transformed-edge top-left corners.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-recursive-reconstruction-spine.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-recursive-reconstruction-spine.md`
passed after API cleanup.

This is partial finite right-inverse algebra only: no solved-`A3` endpoint
reconstruction and no full `edgeMatrix (sourceReadback E) = E` theorem yet.
No image openness, source-rank coverage, source/image theorem, local
homeomorphism, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive source right inverse:
`ProductReduction.lean` proves
`ChartLocalSuffixState.step_lowerLeftBlock_L_of_L_eq_lowerUnitriangular` and
the existential wrapper
`ChartLocalSuffixState.step_lowerLeftBlock_L_of_exists_L_eq_lowerUnitriangular`.

`RetainedPassiveCoordinates.lean` proves
`retainedPassiveSolvedA3_last_eq_of_productTailSum_eq`,
`retainedPassiveSolvedA3_last_eq_of_productTailSum_eq_of_ne_last`,
`sourceReadback_solvedA1_residualFactorProduct_eq_Ctop`,
`sourceReadbackSuffixState_D_eq_residualFactorProduct_C`,
`sourceReadbackSuffixState_lowerLeftBlock_L_eq_lowerLeftProductTailSum`,
`sourceReadback_solvedA3_eq_lowerLeftBlock`,
`retainedPassiveTransformedEdge_sourceReadback_eq_sourceReadbackTransformedEdge`,
and `edgeMatrix_sourceReadback_eq_of_sourceRecursiveDetChart`.

The final theorem states that every edge family satisfying
`sourceRecursiveDetChart` is recovered from its source readback:
`(sourceReadback E).edgeMatrix = E`.  This completes the finite right-inverse
direction on the recursive determinant chart.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-right-inverse.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-right-inverse.md`
passed with API cleanup.

This is not a local homeomorphism or global image theorem.  No openness,
source-rank coverage, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT is proved.

Latest A2 retained-passive source-recursive chart homeomorphism:
`RetainedPassiveCoordinates.lean` proves
`RetainedPassiveNonredundantCoordinateData.solvedA1_det_isUnit_of_detChart`
and
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChart_edgeMatrix_of_detChart`.

`RetainedPassiveCoordinatesTopology.lean` proves
`continuous_edgeMatrix_sourceRecursiveDetChart_subtype`,
`continuous_sourceReadback_detChart_subtype`, and defines
`detChart_sourceRecursiveDetChart_homeomorph`.

The homeomorphism is between the retained-passive determinant-coordinate
subtype and the explicit source-recursive determinant edge subtype.  It uses
the already proved finite inverse laws in both directions.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-recursive-chart-homeomorph.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-recursive-chart-homeomorph.md`
passed.

This does not prove ambient openness of `sourceRecursiveDetChart`, equality
with the whole source image, source-rank coverage, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive source-recursive chart openness:
`RetainedPassiveCoordinates.lean` defines
`RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet` and
proves `mem_sourceRecursiveDetChartSet` plus
`sourceRecursiveDetChart_iff`.

`RetainedPassiveCoordinatesTopology.lean` proves
`sourceRecursiveDetChartSet_mem_nhds` and
`isOpen_sourceRecursiveDetChartSet`.

The theorem says that the named source-recursive determinant chart is open in
the ambient edge-family space.  It relies on the existing transformed-edge
continuity API and the generic selected determinant-chart openness theorem.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-recursive-chart-openness.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-recursive-chart-openness.md`
passed.

This does not prove equality with the whole source image, source-rank
coverage, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT.

Latest A2 retained-passive all-edge pair source-staged target shear:
`RetainedPassiveCoordinatesJacobian.lean` defines
`retainedPassiveSourceStagedSuccessorF2` and proves
`retainedPassiveSourceStagedSuccessorF2_castSucc`,
`retainedPassiveSourceStagedSuccessorF2_last`,
`F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
and
`F2C_all_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_sourcePair`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-all-edge-pair-source-staged-target-shear.md`
passed by xhigh `Dewey`.

The staged successor family uses the casted successor source tangent at
nonterminal edges and zero only at the terminal edge.  The all-edge equality is
proved by `Fin.lastCases`, using the terminal edge-pair package in the terminal
case and the source-staged nonterminal package in the `castSucc` case.  The
source-pair recovery rewrites to the formal edge-pair family and applies the
formal edge-pair inverse.  This is not a target-side determinant-one
equivalence, not an actual derivative determinant formula, not a descending
construction, and not measure transport, normal crossings, pole order, or
RLCT.

Latest A2 retained-passive edge-pair source-staged tuple assembly:
`RetainedPassiveCoordinatesJacobian.lean` proves
`edgePairSourceStagedShearedTopologyTupleEdgeRawOrderFDerivAt` and
`edgePairSourceStaged_sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-edge-pair-source-staged-tuple-assembly.md`
passed by xhigh `Dalton`.

The tuple order is `(A1passive, F2, A3passive, C, Ctop, F3)`.  The hybrid
tuple keeps the derivative-staged `A1passive`, passive `A3`, `Ctop`, and `F3`
branches from `shearedTopologyTupleEdgeRawOrderFDerivAt`, and replaces only
`F2` and `C` with the all-edge source-staged normalized families.  It then
proves equality with the formal raw-order Jacobian by combining the old tuple
equality with the all-edge `(F2,C)` equality.  This is not a fully
source-staged tuple, not a target-side determinant-one equivalence, not an
actual derivative determinant formula, and not measure transport, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive passive A1 source-staged shear:
`RetainedPassiveCoordinatesJacobian.lean` defines
`retainedPassiveSourceStagedSuccessorA3` and proves
`retainedPassiveSourceStagedSuccessorA3_castSucc`,
`retainedPassiveSourceStagedSuccessorA3_last`,
`fderiv_retainedPassive_toCoordinateData_solvedA3_castSucc_apply`,
`fderiv_retainedPassive_toCoordinateData_F2_succ_apply`,
`retainedPassive_F2_succ_mul_fderiv_solvedA3_eq_sourceStagedSuccessorA3`,
and
`A1passive_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a1passive-source-staged-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1passive-source-staged-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1passive-source-staged-shear.md`
passed by xhigh `Lagrange`.

The nonterminal solved-`A3` projection derivative is proved only at
`p.castSucc`.  The all-edge lower-left readout is proved only after
left-multiplication by `coord.F2 q.succ`; the terminal case is killed by the
terminal zero extended `F2` slot, not by a false terminal `solvedA3` derivative
identity.  The passive `A1` staged theorem substitutes this multiplier
identity and the all-edge successor `F2` derivative readout into the old
passive `A1` bridge.  This is not `Ctop` staging, not `F3` staging, not a
fully source-staged tuple, not a target-side determinant-one equivalence, not
an actual derivative determinant formula, and not measure transport, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive formal non-edge recovery:
`RetainedPassiveCoordinatesJacobian.lean` proves
`retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive`,
`retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop`, and
`retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-formal-nonedge-recovery.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-formal-nonedge-recovery.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-formal-nonedge-recovery.md`
passed by xhigh `Nash`.

These are point-specialized formal-map inverse formulas for the non-edge
branches: passive `A1` by projection, `Ctop` by left multiplication with
`Tail`, and `F3` by right multiplication with `(-LastTop)⁻¹`.  The `Ctop` and
`F3` formulas use determinant-chart unit hypotheses.  This is not actual
derivative identification, not source staging for `Ctop`/`F3`, not a
target-side determinant-one equivalence, not actual derivative determinant
equality, and not measure transport, normal crossings, pole order, or RLCT.

Latest A2 retained-passive Ctop source-staged successor shear:
`RetainedPassiveCoordinatesJacobian.lean` proves
`Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-source-staged-successor-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-source-staged-successor-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-source-staged-successor-shear.md`
passed by xhigh `Kant`.  Focused and full `DLNFibre` builds passed; the sorry
scan and `git diff --check` passed.  Axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.

The theorem rewrites only the successor `F2` derivative and the multiplied
successor lower-left derivative in the existing `Ctop` bridge.  The
tail-inverse derivative remains explicit.  Nonclaims: no tail-inverse product
formula, no `F3` source staging, no target-side determinant-one shear,
determinant equality, measure transport, normal crossings, pole order, or
RLCT.

Latest A2 retained-passive tail-inverse derivative:
`RetainedPassiveCoordinatesJacobian.lean` proves
`fderiv_retainedPassive_A1TailAfterFirst_inv_eq_tail_fderiv` and
`Ctop_tail_fderiv_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-tail-inverse-fderiv.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-tail-inverse-fderiv.md`.
Review:
pen-and-paper PASS from xhigh `Boole`; Lean/API scout PASS from xhigh
`Mencius`; implementation review PASS from xhigh `Epicurus`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-tail-inverse-fderiv.md`.

The first theorem composes the existing passive-tail differentiability theorem
with the matrix inverse derivative on determinant-unit square matrices and
uses the passive `A1` determinant-chart hypotheses to prove `IsUnit det(Tail)`.
It identifies `d(Tail^{-1})` as
`-Tail^{-1} * dTail * Tail^{-1}` while keeping
`dTail = (fderiv Tfun z) v` opaque.  The second theorem substitutes this into
the Ctop successor-staged bridge with the positive sign.  Nonclaims: no
recursive product formula for `dTail`, no full `Ctop` source staging, no `F3`
source staging, no target-side determinant-one shear, determinant equality,
measure transport, normal crossings, pole order, or RLCT.
Focused and full `DLNFibre` builds passed; `scripts/sorries` reported zero
forbidden markers; `git diff --check` passed; both new theorem axiom audits
report only `[propext, Classical.choice, Quot.sound]`.

Latest A2 retained-passive tail product derivative recursion:
`RetainedPassiveCoordinatesDerivative.lean` proves
`differentiableAt_retainedPassiveA1seed_residualFactorProduct`,
`fderiv_retainedPassive_A1seed_residualFactorProduct_self_apply`, and
`fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-tail-product-fderiv-recursion.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-tail-product-fderiv-recursion.md`.
Review:
pen-and-paper PASS from xhigh `Bacon`; Lean/API scout PASS from xhigh `Kuhn`;
implementation review PASS after documentation wording fix from xhigh
`Schrodinger`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-tail-product-fderiv-recursion.md`.

This is the recursive product-rule step for passive top-left suffix products:
the endpoint empty product has zero derivative, and the nonterminal passive
step gives
`d(P_{p.castSucc}) = d(P_{p.succ})*A1seed_p + P_{p.succ}*v.A1passive_q`
for `p=q.succ`.  It uses no determinant-chart hypothesis and does not include
the dummy `A1seed 0`.  Nonclaims: no closed finite-sum formula for `dTail`, no
full `Ctop` source staging, no `F3` source staging, no target-side
determinant-one shear, determinant equality, measure transport, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive tail endpoint derivative:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassive_A1TailAfterFirst_zero_apply`,
`fderiv_retainedPassive_A1TailAfterFirst_succ_apply`, and
`fderiv_retainedPassive_A1TailAfterFirst_pos_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-tail-endpoint-fderiv.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-tail-endpoint-fderiv.md`.
Review:
pen-and-paper scout PASS from xhigh `Goodall`; Lean/API scout PASS from xhigh
`Bohr`; implementation review PASS from xhigh `Russell`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-tail-endpoint-fderiv.md`.

This packages the actual tail map endpoint: `M=0` is the empty product with
zero derivative; positive tail length is the first recurrence step
`d(Tail) = d(Psucc)*A1seed_p + Psucc*v.A1passive_0`, with `p` the first
passive seed index.  It uses no determinant-chart hypothesis and does not
include dummy `A1seed 0`.  Nonclaims: no closed finite-sum formula for
`dTail`, no full `Ctop` source staging, no `F3` source staging, no target-side
determinant-one shear, determinant equality, measure transport, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive Ctop tail endpoint substitution:
`RetainedPassiveCoordinatesJacobian.lean` proves
`Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and
`Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-tail-endpoint-substitution.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-tail-endpoint-substitution.md`.
Review:
pen-and-paper scout PASS from xhigh `Godel`; Lean/API scout PASS from xhigh
`Hooke`; implementation review PASS from xhigh `Galileo`, recorded at
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-tail-endpoint-substitution.md`.

This substitutes the endpoint `dTail` theorem into the existing Ctop bridge.
The zero case kills the empty-tail correction.  The positive case keeps the
already-positive sign and uses
`Tail^{-1} * (d(Psucc)*A1seed_p + Psucc*v.A1passive_0) * Tail^{-1} * Ctop`,
with the suffix derivative still explicit.  Nonclaims: no closed finite-sum
formula for `dTail`, no full `Ctop` source staging, no `F3` source staging,
no target-side determinant-one shear, determinant equality, measure transport,
normal crossings, pole order, or RLCT.

Latest A2 retained-passive nonterminal edge-pair staged target shear:
`RetainedPassiveCoordinatesJacobian.lean` proves
`fderiv_retainedPassive_toCoordinateData_F2_nonterminal_succ_apply`,
`F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`,
and
`F2C_nonterminal_target_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-nonterminal-edge-pair-staged-target-shear.md`;
first xhigh review failed on derivative/source staging, and post-repair xhigh
review passed.
The theorem handles one nonterminal edge `q = p.castSucc` under a supplied
successor input `Xsucc` equal to the source tangent `v.F2_(p.succ)` transported
along `Fin.succ_castSucc p`, and the projection lemma identifies that casted
source tangent with the actual derivative of the successor extended `F2` slot.
It packages the normalized target pair as the formal edge pair and reuses the
formal inverse to recover the current source `F2` and `C` tangents.  This is
not a full descending induction, not a
target-side determinant-one equivalence, not an actual derivative determinant
formula, and not measure transport, normal crossings, pole order, or RLCT.

Latest A2 retained-passive terminal edge-pair target shear:
`RetainedPassiveCoordinatesJacobian.lean` proves
`F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F2`, and
`F2C_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_recovers_C`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-terminal-edge-pair-target-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-terminal-edge-pair-target-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-terminal-edge-pair-target-shear.md`
passed by xhigh `Mendel` and `Ramanujan`.

The theorem packages the terminal actual target-side normalized `(F2,C)` pair
and then applies the already-landed formal inverse formulas to recover the
source terminal `F2` and `C` tangents.  Nonclaims: no nonterminal staged
target-side shear, determinant-one target equivalence, actual derivative
determinant formula, measure theorem, normal crossings, pole order, or RLCT.

## A2 retained-passive edge-pair product equivalence

Status: Proved in Lean; reproduced on paper; xhigh implementation review
passed.

Claim: under determinant-chart unit hypotheses for every `A p`, the dependent
product of the edge-local `(F,C)` maps is a linear equivalence.  After
raw-order regrouping, its inverse recovers every formal source edge pair by

```text
F_p = (A p)^-1 * (H p * U_C_p - U_F2_p)
C_p = U_C_p + G p * F_p.
```

Lean proves the generic product equivalence in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalLinearDeterminant.lean`, the
raw regrouped equivalence in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalRawOrder.lean`, and the
retained-passive chart-specialized equivalence in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.

Lean names:

```text
edgeLocalFCPairPiLinearEquiv
edgeLocalFCPairPiLinearEquiv_apply
edgeLocalFCPairPiLinearEquiv_symm_apply
retainedPassiveFormalRawF2CLinearEquiv
retainedPassiveFormalRawF2CLinearEquiv_apply
retainedPassiveFormalRawF2CLinearEquiv_symm_apply
retainedPassiveFormalRawF2CLinearEquivAt
retainedPassiveFormalRawF2CLinearEquivAt_apply_sourcePair
retainedPassiveFormalRawF2CLinearEquivAt_symm_apply
retainedPassiveFormalRawF2CLinearEquivAt_symm_recovers_sourcePair
```

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-edge-pair-product-equiv.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-edge-pair-product-equiv.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-edge-pair-product-equiv.md`,
accepted by xhigh `Huygens`.

Kill condition: the theorem must remain a formal edge-pair statement.  It does
not include the endpoint `Ctop`/`F3` factors or prove an actual derivative
determinant comparison.

Nonclaims: no full target-side shear, measure theorem, normal crossings, pole
order, or RLCT follows from this product equivalence.

## A2 retained-passive terminal `F2` target shear

Status: Proved in Lean; reproduced on paper; xhigh implementation review
passed.

Claim: at the terminal retained-passive edge `p = Fin.last M`, the successor
`F2` derivative term in the actual `F2` shear vanishes because the extended
successor `F2` coordinate is the constant terminal zero.  Therefore

```text
dY12_p + dA1_p * coord.F2 p.castSucc = formal.F2_p.
```

Lean proves this in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean` as

```text
fderiv_retainedPassive_toCoordinateData_F2_last_apply
F2_terminal_target_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt
```

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-terminal-f2-target-shear.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-terminal-f2-target-shear.md`.

Review:
`threads/03-block-product-reduction/review-a2-retained-passive-terminal-f2-target-shear.md`,
accepted by xhigh `Huygens`.

Kill condition: this must stay terminal-edge only.  Nonterminal edges still
carry the successor derivative and require staged triangular construction.

Nonclaims: no nonterminal shear, full determinant factorization, measure
theorem, normal crossings, pole order, or RLCT is proved by this terminal
bridge.

Latest A2 retained-passive tuple shear assembly and formal F2 recovery:
`RetainedPassiveCoordinatesJacobian.lean` now defines
`shearedTopologyTupleEdgeRawOrderFDerivAt` and proves
`sheared_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
assembling the six component bridges into a tuple-level equality with
`retainedPassiveFormalRawOrderJacobianAt`.

It also proves
`retainedPassiveFormalRawOrderJacobianAt_recovers_F2`: for
`u = retainedPassiveFormalRawOrderJacobianAt z v`, the formal target
coordinates satisfy

```text
(coord.solvedA1 p)^-1 *
  (coord.F2 p.succ * u.C_p - u.F2_p)
= v.F2_p.
```

Reproductions:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and
`threads/03-block-product-reduction/reproduction-a2-retained-passive-formal-f2-recovery.md`.
Statement cards:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-formal-f2-recovery.md`.
Reviews:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-tuple-shear-assembly.md`
and
`threads/03-block-product-reduction/review-a2-retained-passive-formal-f2-recovery.md`
passed xhigh review.

The tuple assembly is not a determinant theorem.  The F2 recovery is the first
brick for a staged target-side shear, using only the formal `(F2,C)` formulas,
`solvedA1_det_isUnit_of_detChart`, and matrix inverse cancellation.  Nonclaims:
no determinant-one target-side linear equivalence, no actual derivative
determinant formula, no measure pushforward, no normal crossings, no pole
order, and no RLCT.

Latest A2 retained-passive formal C recovery:
`RetainedPassiveCoordinatesJacobian.lean` now proves
`retainedPassiveFormalRawOrderJacobianAt_recovers_C`.  For
`u = retainedPassiveFormalRawOrderJacobianAt z v`, it proves

```text
u.C_p + coord.solvedA3 p *
  ((coord.solvedA1 p)^-1 * (coord.F2 p.succ * u.C_p - u.F2_p))
= v.C_p.
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-formal-c-recovery.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-formal-c-recovery.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-formal-c-recovery.md`
passed by xhigh `Huygens the 5th`.

The proof uses `retainedPassiveFormalRawOrderJacobianAt_recovers_F2`, unfolds
the formal `C` component, and cancels `-G*x + y + G*x`.  It introduces no new
invertibility beyond the determinant-chart solved-`A1` input already used in
formal `F2` recovery.  Nonclaims: no target-side `LinearEquiv`, determinant
equality, actual derivative determinant formula, measure pushforward, normal
crossings, pole order, or RLCT.

Latest A2 edge-local `(F,C)` pair inverse equivalence:
`MatrixLinearDeterminant.lean` now proves
`edgeLocalFCPairLinearMapInverse`, `edgeLocalFCPairLinearMapInverse_apply`,
`edgeLocalFCPairLinearEquiv`, `edgeLocalFCPairLinearEquiv_apply`, and
`edgeLocalFCPairLinearEquiv_symm_apply`.

For `IsUnit A.det`, the generic finite-linear map

```text
(F,C) |-> (-(A + H*G)*F + H*C, -G*F + C)
```

has inverse

```text
(U,V) |-> (A^{-1} * (H*V - U),
           V + G * (A^{-1} * (H*V - U))).
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-edge-local-fc-pair-inverse-equiv.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-edge-local-fc-pair-inverse-equiv.md`.
Review:
`threads/03-block-product-reduction/review-a2-edge-local-fc-pair-inverse-equiv.md`
passed by xhigh `Halley the 5th` after a proof-performance failure was fixed.

The proof is finite linear algebra: explicit identities plus nonsingular
inverse cancellation.  Nonclaims: no retained-passive total target-side shear,
actual derivative determinant comparison, measure pushforward, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive actual-derivative F3 shear bridge:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_topologyTupleEdgeRawOrder_F3_component_shear_apply` and
`fderiv_topologyTupleEdgeRawOrder_F3_shear_apply`.  The full theorem states
that the actual raw-order Frechet derivative's terminal lower-left component
becomes `v.F3 * (-LastTop)` after subtracting the earlier lower-left tail
derivative times the terminal top factor and adding the base terminal
lower-left residual `(coord.F3 - Early)` times the derivative of that terminal
top factor.

`RetainedPassiveCoordinatesJacobian.lean` proves
`F3_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
which rewrites the same identity through
`retainedPassiveFormalRawOrderJacobianAt`, using
`retainedPassiveLastTopResidualFactorProduct_eq` for the terminal factor.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.
Independent pen-and-paper check passed by xhigh `Epicurus the 5th`; Lean
reconnaissance passed by xhigh `Godel the 5th`; implementation/orientation
review passed by xhigh `Jason the 5th`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-f3-shear-bridge.md`.

This is a sheared terminal-component bridge only.  It completes the current
component list but does not prove the full analytic derivative factorization,
determinant equality, measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT.

Latest A2 retained-passive actual-derivative passive A1 shear bridge:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_topologyTupleEdgeRawOrder_A1passive_component_shear_apply` and
`fderiv_topologyTupleEdgeRawOrder_A1passive_shear_apply`.  The full theorem
states that the actual raw-order Frechet derivative's passive top-left
component becomes the stored passive top-left tangent after subtracting the
successor-`F2` derivative times the base solved lower-left block and
subtracting the base successor-`F2` coefficient times the solved lower-left
derivative.

`RetainedPassiveCoordinatesJacobian.lean` proves
`A1passive_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
which rewrites the same identity through
`retainedPassiveFormalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.
Independent pen-and-paper check passed by xhigh `Herschel the 5th`;
implementation review passed by xhigh `Nash the 5th`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-a1passive-shear-bridge.md`.

This is a sheared passive-component bridge only.  It does not cover the first
top-left `Ctop` coordinate, terminal `F3`, full analytic derivative
factorization, determinant equality, measure pushforward, density/Jacobian
theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive actual-derivative F2 shear bridge:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_topologyTupleEdgeRawOrder_F2_component_shear_apply` and
`fderiv_topologyTupleEdgeRawOrder_F2_shear_apply`.  The full theorem states
that the actual raw-order Frechet derivative's upper-right component becomes
the formal upper-right component after adding the raw top-left derivative
times the fixed left `F2` coefficient and subtracting the successor-`F2`
derivative times the base residual block `C`.

`RetainedPassiveCoordinatesJacobian.lean` proves
`F2_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
which rewrites the same identity through
`retainedPassiveFormalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.
Independent pen-and-paper check passed by xhigh `Lorentz the 5th`;
implementation review passed by xhigh `Anscombe the 5th`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-f2-shear-bridge.md`.

This is a sheared component bridge only.  It does not prove the full analytic
derivative factorization, determinant equality, measure pushforward,
density/Jacobian theorem, normal crossings, pole order, or RLCT.

Latest A2 retained-passive actual derivative C unshear:
`RetainedPassiveCoordinatesTopology.lean` proves
`rawEdgeTupleA3_topologyTupleEdgeRawOrder`.
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_topologyTupleEdgeRawOrder_C_component_unshear_apply` and
`fderiv_topologyTupleEdgeRawOrder_C_unshear_apply`.
`RetainedPassiveCoordinatesJacobian.lean` proves
`C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-c-unshear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-c-unshear.md`.

This is the first retained-passive actual-derivative-to-formal-shape shear
identity.  It proves only the lower-right `C` component after shearing by the
lower-left raw derivative component, plus its point-specialized formal-map
component bridge.  Nonclaims: no full analytic derivative factorization, no
explicit full determinant formula, no equality with
`retainedPassiveFormalRawOrderJacobianAbsDetAt`, no measure pushforward, no
normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive actual derivative passive A3 identity:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_topologyTupleEdgeRawOrder_A3passive_apply`.
`RetainedPassiveCoordinatesJacobian.lean` proves
`rawEdgeTupleA3_fderiv_topologyTupleEdgeRawOrder_castSucc_eq_formalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-a3passive-identity.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-a3passive-identity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-a3passive-identity.md`.

This proves that passive nonterminal lower-left coordinates are identity
components of the actual Frechet derivative and agree with the corresponding
component of the point-specialized formal raw-order map.  Nonclaims: no
terminal `F3` component, no full analytic derivative factorization, no
explicit full determinant formula, no equality with
`retainedPassiveFormalRawOrderJacobianAbsDetAt`, no measure pushforward, no
normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive actual-derivative Ctop shear bridge:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_topologyTupleEdgeRawOrder_Ctop_component_shear_apply` and
`fderiv_topologyTupleEdgeRawOrder_Ctop_shear_apply`.  The full theorem states
that the actual raw-order Frechet derivative's first top-left component becomes
`Tail^{-1} * v.Ctop` after subtracting the successor-`F2` derivative times the
base solved lower-left block, subtracting the base successor-`F2` coefficient
times the solved lower-left derivative, and subtracting the passive-tail
inverse derivative times the base `Ctop` block.

`RetainedPassiveCoordinatesJacobian.lean` proves
`Ctop_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
which rewrites the same identity through
`retainedPassiveFormalRawOrderJacobianAt`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.
Independent pen-and-paper check passed by xhigh `Einstein the 5th`;
implementation review passed by xhigh `Bohr the 5th`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-actual-derivative-ctop-shear-bridge.md`.

This is a sheared first-top-left component bridge only.  It does not prove the
terminal `F3` bridge, full analytic derivative factorization, determinant
equality, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT.

Latest A2 edge-local `(F,C)` pair determinant:
`MatrixLinearDeterminant.lean` proves
`edgeLocalFCPairLinearMap_apply` and `edgeLocalFCPairLinearMap_det_eq` for the
finite linear map

```text
(F, C) |->
  (-(A + H*G) * F + H*C,
   -G*F + C).
```

In the `(F,C)` input and `(Y12,Y22)` output order, the determinant is

```text
(-A).det ^ Fintype.card kappa.
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-edge-local-fc-pair-determinant.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-edge-local-fc-pair-determinant.md`.
Review:
`threads/03-block-product-reduction/review-a2-edge-local-fc-pair-determinant.md`
passed by xhigh `Lagrange the 4th`.

The proof factors the map into a lower shear, diagonal left multiplication by
`-A` on the `F` block, and an upper shear.  It also promotes reusable
product/shear determinant helpers in `MatrixLinearDeterminant.lean`; the older
private duplicates in `ProductReductionStepJacobian.lean` now use those
promoted helpers.
Nonclaims: no full retained-passive determinant formula, analytic derivative
theorem, source-prior transport, density/pushforward theorem, normal
crossings, pole order, or RLCT.

Latest A2 fixed-passive formal Jacobian determinant:
`ProductReductionStepJacobian.lean` defines the diagonal/shear factorization
of `productStepFixedPassiveFormalJacobian` and proves

```text
productStepFixedPassiveFormalJacobian_eq_shear_comp_diagonal
productStepFixedPassiveFormalJacobian_det_eq_multiplication_blocks
productStepFixedPassiveFormalJacobian_det_eq
```

The determinant theorem is the raw-to-chart fixed-passive one-step formula

```text
A1.det ^ Fintype.card rho
* (-A1^{-1}).det ^ Fintype.card nu.
```

Reproduction and statement card:
`threads/03-block-product-reduction/reproduction-a2-fixed-passive-formal-jacobian-determinant.md`
and
`threads/03-block-product-reduction/statement-card-a2-fixed-passive-formal-jacobian-determinant.md`.
Review:
`threads/03-block-product-reduction/review-a2-fixed-passive-formal-jacobian-determinant.md`
accepted by xhigh `Arendt the 4th`.

This is finite formal-linear Jacobian arithmetic only.  It does not prove the
retained-passive total determinant formula, an analytic derivative theorem,
source-prior transport, normal crossings, pole order, or RLCT.

Latest A2 retained-passive raw-order determinant formula reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-determinant-formula.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-determinant-formula.md`
record the pen-and-paper determinant calculation for the retained-passive
raw-order coordinate map.

Status: Reproduced; rectangular determinant API Lean-proved; retained-passive
explicit product formula not Lean-proved.

Claim target: on `topologyTupleDetChartSet`, the forward absolute determinant
of `topologyTupleEdgeRawOrder` should factor as

```text
|det Tail|^(-|rho|)
* |det LastTop|^(|kappa'_(M+1)|)
* product_{p : Fin (M+1)} |det (A p)|^(|kappa'_p|).
```

Endpoint check: xhigh read-only scout `Boole the 4th` confirmed that
`LastTop` is the local one-edge terminal factor in `retainedPassiveSolvedA3`,
namely `solvedA1 (Fin.last M)`.  Thus `LastTop` is the last passive top block
for `M > 0`, and `Ctop` for `M = 0`.  It is not
`retainedPassiveA1TailAfterFirst`.

Lean landed:
`linearMap_det_mulLeftLinearMap` and `linearMap_det_mulRightLinearMap` in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`.

Remaining Lean gap: factor the Frechet derivative into determinant-one
shears/permutations plus the `Tail`, edge-local `A p`, and `LastTop` factors.

Kill condition: do not use this card as a proved Lean theorem, source-prior
pushforward, selected-entry chart theorem, source-rank coverage theorem,
normal-crossing theorem, pole-order theorem, or RLCT extraction.  The current
VM could not extract the PDF; source-fidelity against Aoyagi p.13 still needs
manual/PDF-readable review.

Latest A2 retained-passive canonical local-source COV:
`RetainedPassiveLocalMeasure.lean` proves
`measure_map_restrict_retainedPassiveP13CanonicalLocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-canonical-local-source-cov.md`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-canonical-local-source-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-canonical-local-source-cov.md`
passed by xhigh `Sartre the 4th`.

This theorem specializes the previous local-source COV bridge to the canonical
fixed-base source edge-family chart built from raw-order inverse coordinates.
It removes the external realization-map and a.e.-measurability hypotheses for
that canonical chart-produced measure, using fixed-base edge realization and
continuity on the raw-order target chart.  Nonclaims: no original source-prior
transport, selected-entry image equality, source-rank coverage, explicit
determinant formula, normal crossings, pole order, or RLCT.

Latest A2 retained-passive unconditional inverse-density COV:
`RetainedPassiveCoordinatesMeasure.lean` proves
`nullMeasurableSet_topologyTupleRawOrderSourceRecursiveDetChartSet`,
`continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_of_mem_rawSourceChart`,
`continuousAt_topologyTupleEdgeRawOrderInverseJacobianDensity_comp_of_mem_rawSourceChart`,
`map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian`,
`map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac`, and
`map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-unconditional-inverse-density-cov.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-unconditional-inverse-density-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-unconditional-inverse-density-cov.md`
accepted by xhigh `Heisenberg the 4th`.

The target-side inverse density is continuous because it is the reciprocal of
the forward determinant density after the raw-order inverse chart, and the
denominator is positive on the inverse image of the raw-order target chart.
This continuity discharges the forward, target-side, and composed density
a.e.-measurability hypotheses needed by the earlier conditional inverse-density
COV theorem.  Focused `RetainedPassiveCoordinatesMeasure` and full `DLNFibre`
builds passed; full build had only pre-existing unrelated linter warnings.
`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`; `git diff --check` passed.  Nonclaims: no explicit determinant
formula, source-prior transport, selected-entry target-image equality,
source-rank coverage, normal crossings, pole order, or RLCT.

Latest A2 retained-passive inverse Jacobian density:
`RetainedPassiveCoordinatesMeasure.lean` now extends the retained-passive
raw-order COV layer with the chart-side inverse density
`topologyTupleEdgeRawOrderInverseJacobianDensity`.  Lean names:

```text
topologyTupleEdgeRawOrderInverseJacobianDensity
topologyTupleEdgeRawOrderInverseJacobianDensity_apply_chartMap
topologyTupleEdgeRawOrderFDerivAbsDet_mul_inverseJacobianDensity_apply_chartMap
topologyTupleEdgeRawOrderInverseJacobianDensity_pos_of_mem_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_eq_withDensity_inverseJacobian_of_aemeasurable
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-inverse-jacobian-density.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-inverse-jacobian-density.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-inverse-jacobian-density.md`
accepted by xhigh `Raman the 4th`.

The pointwise theorem proves that the target-side density
`J(topologyTupleEdgeRawOrderInverse y)⁻¹` restricts to `J(z)⁻¹` on
`y = topologyTupleEdgeRawOrder z`, and that it cancels the forward
`ENNReal.ofReal J(z)` density on the determinant chart.  The measure theorem
is an inverse-density pushforward only under explicit a.e.-measurability
hypotheses for the forward density, inverse density, and composed inverse
density.  Focused and full builds, `scripts/sorries`, and `git diff --check`
passed.

Nonclaims: no determinant formula, no determinant-density continuity or
measurability, no source-prior density theorem, no original DLN source
pushforward, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive composed weighted COV:
`RetainedPassiveCoordinatesMeasure.lean` now proves downstream composition
forms for the forward weighted and conditional inverse-density raw-order COV
theorems, plus edge-family decoder specializations.  Lean names:

```text
map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_eq_map_restrict_rawSourceChart
map_topologyTupleEdgeMatrix_withDensity_absDet_eq_map_edgeFamilyOfRawOrderTuple
map_comp_topologyTupleEdgeRawOrder_restrict_detChart_eq_map_invJac_of_aemeasurable
map_topologyTupleEdgeMatrix_restrict_detChart_eq_map_edgeFamily_invJac_of_aemeasurable
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-composed-weighted-cov.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-composed-weighted-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-composed-weighted-cov.md`
accepted by xhigh `Harvey the 4th`.

The generic theorems are `Measure.map` composition after the already-proved
COV identities.  The edge-family theorems add only the raw-order decoder
identity by `Measure.map_congr`.  Focused and full builds, `scripts/sorries`,
and `git diff --check` passed.

Nonclaims: no determinant formula, no determinant-density continuity or
measurability, no source-prior density theorem, no original DLN source
pushforward, no local-source coverage, no normal crossings, no pole order, and
no RLCT.

Latest A2 retained-passive raw-order local-source COV bridge:
`RetainedPassiveLocalSource.lean` proves
`paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_of_edgeFamilyOfRawOrderTuple_realization`,
and `RetainedPassiveLocalMeasure.lean` proves
`measure_map_restrict_retainedPassiveP13LocalSource_eq_map_comp_topologyTupleEdgeRawOrder_withDensity_absDet_of_realization`.

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-local-source-cov-bridge.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-local-source-cov-bridge.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-local-source-cov-bridge.md`
accepted by xhigh `Parfit the 4th`.

The source lemma turns raw-order target-chart membership into retained-passive
p.13 local-source membership under an explicit fixed-base edge-family
realization identity.  The measure theorem combines this membership with the
already-proved composed weighted COV theorem to prove
`mu.restrict localSource = Measure.map (sourceChart o topologyTupleEdgeRawOrder)
((m.restrict S).withDensity (ofReal o J))` for
`mu = Measure.map sourceChart (m.restrict T)`.

Nonclaims: no determinant-density continuity, inverse-density measurability,
original source-prior transport, selected-entry target-image equality,
source-rank coverage, normal crossings, pole order, or RLCT.

Latest A2 retained-passive raw-order Jacobian density interface:
`RetainedPassiveCoordinatesDerivative.lean` now defines
`topologyTupleEdgeRawOrderFDerivAbsDet` and proves positivity of the forward
absolute `fderiv` determinant on `topologyTupleDetChartSet`, eventual
positivity near chart points, and local lower/upper bounds under an explicit
`ContinuousAt` hypothesis.  Lean names:

```text
topologyTupleEdgeRawOrderFDerivAbsDet
topologyTupleEdgeRawOrderFDerivAbsDet_pos_of_mem_topologyTupleDetChartSet
eventually_topologyTupleEdgeRawOrderFDerivAbsDet_pos_nhds
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds_of_continuousAt
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds_of_continuousAt
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-jacobian-density-interface.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-jacobian-density-interface.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-jacobian-density-interface.md`
accepted by xhigh `Laplace the 4th`.

This is a supplied-continuity density interface only.  It does not prove
continuity of the retained-passive derivative family, a determinant formula,
an inverse-density formula, a measure pushforward, a source-density identity,
normal crossings, pole order, or RLCT.

Latest A2 retained-passive raw-order C1 and density continuity:
`RetainedPassiveCoordinatesDerivative.lean` now proves the forward raw-order
map is `C^1` at tuple determinant-chart points and derives continuity of its
Frechet derivative and absolute determinant density.  Lean names:

```text
contDiffAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
continuousAt_fderiv_topologyTupleEdgeRawOrder_apply_of_mem_topologyTupleDetChartSet
continuousAt_topologyTupleEdgeRawOrderFDerivAbsDet_of_mem_topologyTupleDetChartSet
exists_pos_eventually_le_topologyTupleEdgeRawOrderFDerivAbsDet_nhds
exists_pos_eventually_topologyTupleEdgeRawOrderFDerivAbsDet_le_nhds
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-c1-density-continuity.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-c1-density-continuity.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-c1-density-continuity.md`
accepted by xhigh `Wegener the 4th`.

This supersedes the previous supplied-continuity-only status for the forward
absolute determinant density.  It does not prove an explicit determinant
formula, inverse-density measurability, original source-prior transport,
selected-entry target-image equality, source-rank coverage, normal crossings,
pole order, or RLCT.

Latest A2 retained-passive raw-order weighted change of variables:
`RetainedPassiveCoordinatesMeasure.lean` packages the retained-passive
raw-order chart for Mathlib's Jacobian theorem.  Lean names:

```text
nullMeasurableSet_topologyTupleDetChartSet
map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det
map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart
map_topologyTupleEdgeRawOrder_restrict_detChart_withDensity_abs_det'
map_topologyTupleEdgeRawOrder_withDensity_absDet_eq_restrict_rawSourceChart'
```

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-raw-order-weighted-cov.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-raw-order-weighted-cov.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-raw-order-weighted-cov.md`
accepted by xhigh `Aristotle the 4th`.

This is the forward weighted COV identity for
`topologyTupleEdgeRawOrder` on `topologyTupleDetChartSet`, with source-side
weight `|det Df|` and target restricted to the image/named raw source chart.
It does not prove determinant formula/continuity, inverse density, source-prior
density identity, original DLN source pushforward, normal crossings, pole
order, or RLCT.

## 2026-06-26 A2 full-to-adjacent-window outside-factor transport

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-full-to-adjacent-window-outside-factor-transport.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-full-to-adjacent-window-outside-factor-transport.md`.
Review:
`threads/03-block-product-reduction/review-a2-full-to-adjacent-window-outside-factor-transport.md`
passed by xhigh `Mencius the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`,
`lean/DLNFibre/DLN/Aoyagi/Case2ResidualSelectedEntryChartBridge.lean`.

Lean proves the generic product split and middle-factor substitution:

```text
ChartLocalSuffixState.residualFactorProduct_split_adjacent_two
ChartLocalSuffixState.residualFactorProduct_split_adjacent_two_of_middle_eq
```

and the Case 2 selected-entry specialization:

```text
residualFactorProduct_split_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise
```

This theorem family is finite residual-product bookkeeping.  It rewrites a
longer product through an adjacent Case 2 window as left outside product,
selected-entry middle matrix, and right outside product.  Nonclaims: no
outside-factor identity or absorption, no endpoint equivalence construction,
no real source chart/suffix production, no fixed pivot nonzero provenance, no
source image, pushforward/Jacobian, original-loss, normal-crossing,
pole-order, or RLCT statement.

## 2026-06-26 A2 source-readback per-factor residual block

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-source-readback-per-factor-residual-block.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-source-readback-per-factor-residual-block.md`.
Review:
`threads/03-block-product-reduction/review-a2-source-readback-per-factor-residual-block.md`
passed by xhigh `Pascal the 4th`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.

Lean now proves:

```text
sourceReadback_C_eq_schurResidualBlock_sourceReadbackTransformedEdge
```

This exposes the field definition of `sourceReadback.C`: for each edge `p`,
the source-readback residual factor is the Schur residual block of
`sourceReadbackTransformedEdge E p`.  The proof is definitional and requires
no determinant-chart hypothesis.

Nonclaims: no displayed Case 2 factor identity, no endpoint equivalence, no
full-to-window transport, no fixed successor pivot nonzero, no source chart,
no source image, no pushforward/Jacobian theorem, no original-loss comparison,
no normal crossings, no pole order, and no RLCT.

## 2026-06-26 A2 retained-passive source-map factor readout

Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-map-factor-readout.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-map-factor-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-map-factor-readout.md`
passed by xhigh `Confucius the 4th`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now proves:

```text
schurResidualBlock_sourceReadbackTransformedEdge_edgeMatrix_eq_C

schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_one_eq_residualBlock

schurResidualBlock_sourceReadbackTransformedEdge_case2PostPivotRetainedPassiveData_edgeMatrix_zero_eq_freeFollowingFactor
```

The generic theorem says that if retained-passive data are in `detChart`,
then the Schur residual block of the transformed source edge of
`data.edgeMatrix` at edge `p` is `data.C p`.  The Case 2 specializations apply
this to the synthetic two-edge datum and recover the displayed post-pivot
residual block at edge `1` and the displayed free following factor at edge
`0`.

Nonclaims: no real Aoyagi source chart production, no fixed-base endpoint
equivalence, no full-suffix collapse, no selected-entry entrywise readout, no
fixed pivot nonzero, no source image, no pushforward/Jacobian theorem, no
original-loss comparison, no normal crossings, no pole order, and no RLCT.

Latest A2 adjacent two-edge residual-factor transport:
`ProductReduction.lean` proves
`ChartLocalSuffixState.residualFactorProduct_one_edge_eq_factor`,
`ChartLocalSuffixState.residualFactorProduct_adjacent_two_eq_mul`, and
`ChartLocalSuffixState.residualFactorProduct_adjacent_two_submatrix_eq_mul`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-adjacent-two-edge-residual-factor-transport.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-adjacent-two-edge-residual-factor-transport.md`.
Review:
`threads/03-block-product-reduction/review-a2-adjacent-two-edge-residual-factor-transport.md`
passed by xhigh `Zeno the 4th`.

The one-edge theorem collapses `residualFactorProduct C p.succ p.castSucc` to
`C p`. The adjacent two-edge theorem splits through the middle endpoint and
collapses the two one-edge pieces, giving the order `C p.succ * C p.castSucc`.
The submatrix theorem composes this with `Matrix.submatrix_mul_equiv`.
Nonclaims: no residual-factor construction from suffix states, no fixed-base
endpoint alignment, no full-suffix collapse, no Case 2 factor identities, no
pivot nonzero proof, no source chart/source image, no measure
pushforward/Jacobian theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 adjacent-window Case 2 selected-entry consumer:
`Case2ResidualFactorProduct.lean` proves
`case2DisplayedPostPivotFreeTwoEdgeFactorProduct_eq_residualFactorProduct_adjacent_two_submatrix`
and
`residualFactorProduct_adjacent_two_eq_centerCoordinateMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`.
`Case2ResidualSelectedEntryChartBridge.lean` proves
`residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_entrywise`
and
`exists_residualFactorProduct_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero`.
`RetainedPassiveCase2SelectedEntryChartBridge.lean` proves
`exists_residualFactorProduct_retainedPassiveCoordinateData_adjacent_two_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_pivot_ne_zero`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-adjacent-window-case2-selected-entry-consumer.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-adjacent-window-case2-selected-entry-consumer.md`.
Review:
`threads/03-block-product-reduction/review-a2-adjacent-window-case2-selected-entry-consumer.md`
passed by xhigh `Herschel the 4th`.

Theorems consume an adjacent window, endpoint equivalences, and factor
identities.  The pivot theorem additionally consumes the already-supplied
fixed successor pivot nonzero condition for the displayed product.  Nonclaims:
no endpoint equivalence construction, no full-suffix/fixed-base endpoint
collapse, no source-readback factor identity proof, no pivot nonzero proof, no
source image, no pushforward/Jacobian theorem, no normal crossings, no pole
order, and no RLCT.

Latest A2 retained-passive Case 2 pivot-nonzero source readout:
`SelectedEntrySignedBoxMeasure.lean` proves
`SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero`,
`SelectedEntrySignedBox.CenterCoord.chartMap_preimageOfPivotNeZero`, and
`SelectedEntrySignedBox.CenterCoord.exists_chartMap_eq_value_of_pivot_ne_zero`.
`Case2ResidualSelectedEntryChartBridge.lean` proves
`exists_successorSourceChartMap_entrywise_of_case2DisplayedPostPivotFreeTwoEdgeFactorProduct_pivot_ne_zero`.
`RetainedPassiveCase2SelectedEntryChartBridge.lean` proves
`exists_case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_pivot_ne_zero`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-case2-pivot-nonzero-source-readout.md`.

The theorem replaces the full entrywise successor-source readout hypothesis
for the synthetic Case 2 two-edge datum by a single supplied nonzero condition
at the fixed successor pivot `(J+2,J+2)`, after the endpoint equivalence
`tau ~= Case2ResidualColIndex n S (J+1)`.  It constructs `yNext` by dividing
all target coordinates by the pivot coordinate.  Nonclaims: no proof of the
pivot nonzero condition, no source chart construction, no endpoint alignment,
no longer-suffix transport, no source image equality, no measure
pushforward/Jacobian theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive Case 2 synthetic two-edge data:
`RetainedPassiveCase2SelectedEntryChartBridge.lean` defines
`case2PostPivotRetainedPassiveData` and proves
`case2PostPivotRetainedPassiveData_detChart` plus
`case2PostPivotRetainedPassiveData_hdataFactor_of_entrywise`, with alias
`case2PostPivotRetainedPassiveData_residualFactorProduct_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_entrywise`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-case2-synthetic-data.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-case2-synthetic-data.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-case2-synthetic-data.md`
passed by xhigh `Ampere the 3rd`.

The datum is the concrete post-pivot Case 2 `Fin 3` endpoint family with
active `C` factors definitionally equal to
`case2PostPivotFreeTwoEdgeFactorFamily`; determinant-chart membership is
proved from identity `Ctop` and identity passive `A1`.  The data-level
selected-entry residual-factor identity still assumes the entrywise
successor-source readout and endpoint equivalence.  No source chart,
fixed-base edge realization, longer-suffix transport, normal-crossing
production, pole order, or RLCT is proved.

## 2026-06-26 A2 retained-passive Case 2 selected-entry bridge

Reproduction:
`reproduction-a2-retained-passive-case2-selected-entry-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-case2-selected-entry-bridge.md`.
Review:
`review-a2-retained-passive-case2-selected-entry-bridge.md`.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryChartBridge.lean`.

Lean now proves:

```text
residualFactorProduct_retainedPassiveCoordinateData_eq_selectedEntryCenter_matrix_of_case2PostPivot_entrywise

residualFactorProduct_retainedPassiveCoordinateData_eq_successorSelectedEntryCenterCoordChartMapMatrix_of_case2PostPivot_entrywise
```

The first theorem is the generic selected-center retained-passive two-edge
adapter.  The second is the Aoyagi source-shaped successor-center adapter on
the `(S,J+1)` residual domains.

Nonclaims: no longer suffix slicing/transport, no construction of
`retainedData`, no proof of the entrywise product readout, no source chart or
source image equality, no pushforward/Jacobian theorem, no original-loss
comparison, no normal crossings, no pole order, and no RLCT.

## 2026-06-26 A2 retained-passive coordinate-data edge-matrix residual-factor bridge

Reproduction:
`reproduction-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.
Statement card:
`statement-card-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.
Review:
`review-a2-retained-passive-coordinate-data-edge-matrix-residual-factor-bridge.md`.

Lean files:
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`,
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalMeasure.lean`.

Lean now proves:

```text
sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq

PaperEndpointFixedBaseRegularCoordinateSourceData.sourceReadback_residualFactorProduct_eq_matrix_of_retainedPassiveCoordinateData_edgeMatrix

PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_retainedPassiveCoordinateData_edgeMatrix
```

The first theorem is the pure fixed-base p.13 inverse bridge: source readback
recovers retained-passive coordinate data from the fixed-base edge family when
that edge family is the data's `edgeMatrix` and the data satisfies `detChart`.
The second theorem pushes this through the source-readback residual-factor
product.  The third derives the selected-entry residual square-sum from the
data-level residual-factor matrix identity.

Nonclaims: no construction of retained-passive data, no Case 2 entrywise
product identity, no source chart construction, no source image equality, no
pushforward/Jacobian proof, no original-loss comparison, no normal crossings,
no pole order, and no RLCT.

Latest A2 retained-passive source-readback residual readout:
`RetainedPassiveLocalSource.lean` proves
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-source-readback-residual-readout.md`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-source-readback-residual-readout.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-source-readback-residual-readout.md`
passed by xhigh `Descartes the 3rd`.

The theorem rewrites the fixed-base p.13 residual coordinate map through the
retained-passive source readback: the coordinate map is
`AoyagiResidualBlockCoordinateIndex.value` of
`residualFactorProduct (sourceReadback E).C (Fin.last (M + 1)) 0`, with
`E` the fixed-base edge-matrix family.  It composes the existing
`paperEndpointFixedBaseResidualBlockCoordinateMap_eq_residualProduct` theorem
with
`RetainedPassiveNonredundantCoordinateData.sourceReadbackSuffixState_D_eq_residualFactorProduct_C`.

Nonclaims: no selected-entry coordinate readout, no source chart
construction, no source image equality, no measure pushforward, no
Jacobian/density theorem, no original-loss comparison, no normal crossings, no
pole order, and no RLCT.

Latest A2 retained-passive selected-entry source-readback residual-factor
handoff:
`RetainedPassiveLocalMeasure.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.aoyagiCoordinateSquareSum_paperEndpointFixedBaseResidualBlockCoordinateMap_eq_selectedEntryCenter_residual_of_sourceReadback_residualFactorProduct_eq_matrix`
and
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity_of_sourceReadback_residualFactorProduct_eq_matrix`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-selected-entry-source-readback-residual-factor-handoff.md`
passed by xhigh `Newton the 3rd`.

The algebra theorem derives the selected-entry residual square-sum from the
retained-passive source-readback residual-factor product matrix identity and a
finite equivalence from endpoint residual coordinates to the selected center.
The local-measure theorem then calls the previous selected-entry
retained-passive handoff with the derived residual equality.

Nonclaims: no source chart construction, no source image equality, no
pushforward/Jacobian proof, no original-loss comparison, no normal crossings,
no pole order, and no RLCT.

Latest A2 retained-passive selected-entry signed-box handoff:
`RetainedPassiveLocalMeasure.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_selectedEntryCenter_signedBox_withDensity`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-selected-entry-signed-box-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-selected-entry-signed-box-handoff.md`.
Focused build passed.  The theorem consumes a supplied retained-passive source
chart, weighted pushforward, residual readout, and local loss/density bounds,
and discharges the selected-entry monomial-unit identities and unit bounds from
`SelectedEntrySignedBox.CenterCoord`.  Nonclaims: no source chart construction,
no weighted pushforward/Jacobian proof, no original-loss comparison, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive p.13 coverage boundary:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-p13-source-chart-boundary.md`
and
`threads/03-block-product-reduction/statement-card-a2-retained-passive-p13-source-chart-coverage-boundary.md`
record a reviewed boundary, not a Lean theorem.  Review is at
`threads/03-block-product-reduction/review-a2-retained-passive-p13-source-chart-coverage-boundary.md`;
Boyle the 3rd found no blocking issue.  The proposed next theorem is a
coverage result for a retained-passive p.13 local source tied to
`sourceRecursiveDetChartSet`.  Current status: no Lean name and no proof.
Nonclaims: no coverage removed, no raw measure pushforward, no
Jacobian/density theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive local-source coverage:
`RetainedPassiveLocalSource.lean` defines
`paperEndpointFixedBaseRetainedPassiveP13LocalSource` and proves
`mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts`,
`paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_nhds_of_selfBase`,
and
`exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-local-source-coverage.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-local-source-coverage.md`.
Focused and full builds passed.  The theorem proves that the retained-passive
source preimage is a determinant-chart neighborhood near the self-base point,
and packages the corresponding handoff-shaped source-stratum inclusion.
Nonclaims: no exact-rank openness, no global source-rank cover, no
measurability theorem for the local source, no measure pushforward, no
Jacobian/density theorem, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive fixed-base edge realisation:
`RetainedPassiveLocalSource.lean` proves
`paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix`
and
`sourceReadback_paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOf_retainedPassiveEdgeMatrix_eq`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-fixed-base-edge-realisation.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-fixed-base-edge-realisation.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-fixed-base-edge-realisation.md`
passed by xhigh `Pasteur the 4th`.

The theorem specializes the existing prescribed fixed-base matrix realization
to retained-passive coordinate data: the continuous reverse-edge family
realized from `data.edgeMatrix` has fixed-base edge matrices exactly
`data.edgeMatrix`, and source readback recovers `data` under `data.detChart`.
It is a generic wrapper over the fixed-base realization API and the
retained-passive readback inverse.  Nonclaims: no Case 2 source production,
no longer-suffix slicing/transport, no source image equality, no measure
pushforward/Jacobian theorem, no original-loss comparison, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive local-source measurability:
`RetainedPassiveLocalSource.lean` proves
`continuous_paperEndpointFixedBaseRetainedPassiveP13EdgeMatrix_of_continuous`
and
`measurableSet_paperEndpointFixedBaseRetainedPassiveP13LocalSource_of_continuous`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-local-source-measurability.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-local-source-measurability.md`.
Focused build passed.  The theorem proves only measurability of the chart-tied
local source under global continuity of `Cedge`.  Nonclaims: no source-rank
openness, no residual integrability, no loss/density bounds, no measure
pushforward, no Jacobian/density theorem, no normal crossings, no pole order,
and no RLCT.

Latest A2 retained-passive local-measure handoff:
`RetainedPassiveLocalMeasure.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-local-measure-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-local-measure-handoff.md`.
Focused build passed.  The theorem specializes the existing local-source
finite-integral consumer to the retained-passive determinant-chart local
source, discharging only local coverage and measurability.  Nonclaims: no
source image equality, no measure pushforward, no Jacobian/density theorem, no
residual integrability proof, no original-loss comparison, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive signed-box local-measure handoff:
`RetainedPassiveLocalMeasure.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialLower`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-signed-box-local-measure-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-signed-box-local-measure-handoff.md`.
Focused build passed.  The theorem discharges edge-matrix measurability and
residual positivity/integrability for the retained-passive local source from
global `Continuous Cedge` plus supplied weighted signed-box pushforward and
monomial residual/density hypotheses.  Nonclaims: no source chart
construction, no pushforward proof, no Jacobian/density theorem, no
original-loss comparison, no normal crossings, no pole order, and no RLCT.

Latest A2 retained-passive monomial-unit local-measure handoff:
`RetainedPassiveLocalMeasure.lean` proves
`PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource_residualSource_signedBox_withDensity_monomialUnits`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-monomial-unit-local-measure-handoff.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-monomial-unit-local-measure-handoff.md`.
Focused build passed.  The theorem derives the retained-passive signed-box
handoff from supplied monomial-times-unit identities and unit bounds.
Nonclaims: no source chart construction, no pushforward proof, no
Jacobian/density theorem, no original-loss comparison, no normal crossings, no
pole order, and no RLCT.

Latest A2 retained-passive open partial homeomorphism:
`RetainedPassiveCoordinatesTopology.lean` defines
`RetainedPassiveNonredundantCoordinateData.detChartSet_sourceRecursiveDetChartSet_homeomorph`
and
`RetainedPassiveNonredundantCoordinateData.detChart_sourceRecursiveDetChart_openPartialHomeomorph`.

The first theorem rewrites the predicate-subtype homeomorphism as a
homeomorphism between the named set subtypes.  The second packages source
`detChartSet`, target `sourceRecursiveDetChartSet`, forward `edgeMatrix`, and
inverse `sourceReadback` as an `OpenPartialHomeomorph`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-open-partial-homeomorph.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-open-partial-homeomorph.md`
passed by xhigh `Helmholtz the 3rd`.

This does not prove equality with the whole source image, source-rank
coverage, measure pushforward, density/Jacobian theorem, normal crossings,
pole order, or RLCT.

Latest A2 retained-passive Ctop/F3 recovery consumers:
`RetainedPassiveCoordinatesJacobian.lean` proves
`Ctop_tail_zero_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`,
`Ctop_tail_pos_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`,
and `F3_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-f3-recovery-consumers.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-f3-recovery-consumers.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-f3-recovery-consumers.md`.

These theorems consume existing staged component equalities together with
`retainedPassiveFormalRawOrderJacobianAt_recovers_Ctop` and
`retainedPassiveFormalRawOrderJacobianAt_recovers_F3`.  They require
`z in topologyTupleDetChartSet`; the docs now expose that hypothesis.  The
positive Ctop theorem preserves the order and sign of the first passive
recurrence substitution inside the two inverse-tail factors, and the F3 theorem
uses the terminal solved top-left factor `coord.solvedA1 (Fin.last M)`.
Nonclaims: no closed finite-sum tail derivative, no F3 early-tail derivative
recurrence, no full source-staged tuple, no target-side determinant-one
equivalence, no determinant equality, no measure transport, no normal
crossings, no pole order, and no RLCT.

Latest A2 retained-passive target edge-pair recovery:
`RetainedPassiveCoordinatesJacobian.lean` defines
`retainedPassiveTargetRecoveredF2At` and
`retainedPassiveTargetRecoveredSuccessorF2At`, and proves
`retainedPassiveTargetRecoveredF2At_fderiv_eq_sourceF2`,
`retainedPassiveTargetRecoveredSuccessorF2At_fderiv_eq_sourceStagedSuccessorF2`,
`retainedPassiveTargetEdgePairShearAt_fderiv_eq_formalF2C`, and
`retainedPassiveTargetEdgePairShearAt_fderiv_recovers_sourcePair`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-target-edge-pair-recovery.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-target-edge-pair-recovery.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-target-edge-pair-recovery.md`.

The recovered `F2` family is defined by a backward recurrence: terminal
successor correction is zero at `Fin.last M`; a nonterminal edge uses the
already recovered successor `F2` value transported by the
`Fin.succ_castSucc` cast.  On actual derivative targets the recovered family
equals the source `F2` tangent family, so the induced target-side successor
family equals the earlier source-staged successor family.  The target-side
`(F2,C)` normalized pair therefore rewrites to the point-specialized formal
edge pair, and the existing formal edge-pair inverse recovers `(v.F2, v.C)`.
Nonclaims: no whole-tuple target-side normalization, no determinant-one
target-side `LinearEquiv`, no actual derivative determinant formula, no
measure transport, no normal crossings, pole order, or RLCT.

Latest A2 retained-passive passive A1 target-staged shear:
`RetainedPassiveCoordinatesJacobian.lean` proves
`retainedPassive_F2_succ_mul_rawEdgeTupleA3_fderiv_eq_sourceStagedSuccessorA3`,
`A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
and
`A1passive_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_A1passive`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-a1passive-target-staged-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-a1passive-target-staged-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-a1passive-target-staged-shear.md`.

The formula uses the target-recovered successor `F2` family
`retainedPassiveTargetRecoveredSuccessorF2At z Dzv` and the raw lower-left
target readout `rawEdgeTupleA3 Dzv q` under multiplication by
`coord.F2 q.succ`.  The terminal case uses the zero terminal extended `F2`
slot; it does not identify the terminal raw lower-left target derivative with
zero.  The recovery theorem then projects through
`retainedPassiveFormalRawOrderJacobianAt_recovers_A1passive`.
Nonclaims: no `Ctop` target staging, no `F3` target staging, no whole-tuple
target-side normalization, no determinant-one target-side `LinearEquiv`, no
actual derivative determinant formula, no measure theorem, no normal
crossings, pole order, or RLCT.

Latest A2 retained-passive Ctop target-staged endpoint shear:
`RetainedPassiveCoordinatesJacobian.lean` proves
`Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
`Ctop_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`,
and
`Ctop_tail_pos_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_Ctop`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-ctop-target-staged-endpoint-shear.md`.

The formula replaces the first-edge source-staged successor `F2` correction by
`retainedPassiveTargetRecoveredSuccessorF2At z Dzv` and replaces the
source-staged lower-left correction by `rawEdgeTupleA3 Dzv 0` only under
left multiplication by `coord.F2 0.succ`.  The zero-tail case uses the
terminal zero extended `F2` slot rather than a zero raw lower-left derivative.
The positive-tail theorem preserves the explicit suffix derivative expression
in the landed order.  Nonclaims: no `F3` target staging, no whole-tuple
target-side normalization, no determinant-one target-side `LinearEquiv`, no
actual derivative determinant formula, no measure theorem, no normal
crossings, pole order, or RLCT.

Latest A2 retained-passive F3 zero-tail target-staged shear:
`RetainedPassiveCoordinatesJacobian.lean` proves
`F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
and
`F3_tail_zero_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-mzero-target-staged-shear.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-mzero-target-staged-shear.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-f3-mzero-target-staged-shear.md`.

For `M = 0`, the proof collapses the landed `F3` bridge by zeroing the one-edge
`Early` source tail and identifying the terminal top factor with `coord.Ctop`.
It substitutes the landed Ctop zero-tail target-staged recovery, so the final
target expression uses `retainedPassiveTargetRecoveredSuccessorF2At z Dzv` and
keeps `rawEdgeTupleA3 Dzv 0` only under multiplication by
`coord.F2 (0 : Fin 1).succ`.  Recovery right-multiplies by
`(-(coord.Ctop))⁻¹`.  Nonclaims: no positive-tail `F3` target staging, no
`Early` derivative recurrence, no whole-tuple target-side normalization, no
determinant-one target-side `LinearEquiv`, no actual derivative determinant
formula, no measure theorem, no normal crossings, pole order, or RLCT.

Latest A2 retained-passive F3 positive-tail dLast target-staged slice:
`RetainedPassiveCoordinatesJacobian.lean` proves
`fderiv_retainedPassive_toCoordinateData_solvedA1_succ_apply`,
`F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`,
and
`F3_tail_pos_dLast_target_staged_shear_fderiv_topologyTupleEdgeRawOrder_recovers_F3`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-f3-positive-tail-dlast-target-staged.md`
passed by xhigh `Raman`.
Focused/full builds passed; `scripts/sorries` reported zero forbidden markers;
`git diff --check` passed; theorem axiom audits report only
`[propext, Classical.choice, Quot.sound]`.

The theorem assumes a terminal passive index `q : Fin M` with
`q.succ = Fin.last M`.  It rewrites the terminal top product in the landed
`F3` bridge to `coord.solvedA1 (Fin.last M)`, identifies its derivative with
the passive tangent `v.1 q`, and substitutes the already-landed target-staged
passive `A1` expression.  The early-tail derivative remains explicit:
there is still no positive-tail `dEarly` recurrence.  The terminal raw
lower-left target readout is kept under its displayed `coord.F2 q.succ.succ`
multiplier; it is not set to zero.  Nonclaims: no full positive-tail `F3`
target staging, no whole-tuple target-side normalization, no determinant-one
target-side `LinearEquiv`, no actual derivative determinant formula, no
measure theorem, no normal crossings, pole order, or RLCT.

Latest A2 retained-passive dEarly recursive derivative unfold:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-recursive-unfold.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-recursive-unfold.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-recursive-unfold.md`
passed by xhigh `Faraday`.

The theorem applies the structural recurrence
`retainedPassiveLowerLeftProductTailSum_castSucc` under `fderiv`: for arbitrary
`p : Fin (M + 1)`, the derivative of the lower-left product-tail sum at `p`
is the derivative of the current summand
`-(Cprod * A3p * Pcast^-1)` plus the derivative of the successor tail.  The
current summand derivative remains explicit.  `A3p` is the zeroed family
`retainedPassiveA3WithoutLast`, not the solved terminal lower-left block.
Focused module build and full `DLNFibre` build passed; `scripts/sorries`,
`git diff --check`, and axiom audit passed.  Nonclaims: no source or
target staging for the summand derivative pieces, no full positive-tail `F3`
target staging, no determinant theorem, no measure theorem, no normal
crossings, pole order, or RLCT.

Latest A2 retained-passive dEarly product-rule derivative unfold:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-product-rule-unfold.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-product-rule-unfold.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-product-rule-unfold.md`
passed by xhigh `Wegener`.

The theorem expands the current summand derivative in the recursive lower-left
tail formula:
`-dD * G * P^-1 - D * dG * P^-1 + D * G * P^-1 * dP * P^-1`,
then adds the successor-tail derivative.  The inverse derivative uses
`d(P^-1) = -P^-1 * dP * P^-1`, and all matrix factors remain in order.
`G` is `retainedPassiveA3WithoutLast`, not solved terminal `A3`.  Focused
module build and full `DLNFibre` build passed; `scripts/sorries`,
`git diff --check`, and axiom audit passed.
Nonclaims: no source or target staging for `dD`, `dG`, or `dP`, no full
positive-tail `F3` target staging, no determinant theorem, no measure theorem,
no normal crossings, pole order, or RLCT.

Latest A2 retained-passive dEarly dG source staging:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassiveA3WithoutLast_castSucc_apply` and
`fderiv_retainedPassiveA3WithoutLast_last_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dg-source-staging.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dg-source-staging.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-dg-source-staging.md`
passed by xhigh `Halley` and xhigh `Nietzsche`.

The nonterminal theorem rewrites the derivative of the zeroed lower-left
factor at `q.castSucc` as the passive source tangent `v.2.2.1 q`; the terminal
theorem rewrites the derivative at `Fin.last M` as zero.  This is
`retainedPassiveA3WithoutLast`, not the solved terminal lower-left derivative.
Focused module build, `scripts/sorries`, `git diff --check`, full `DLNFibre`
build, and theorem axiom audit passed; both new theorems have only the
standard `[propext, Classical.choice, Quot.sound]` footprint.  Nonclaims: no
target staging, no `dD` or `dP` staging, no full positive-tail `F3` target
staging, no determinant theorem, no measure theorem, no normal crossings, pole
order, or RLCT.

Latest A2 retained-passive dEarly product-rule dG substitution:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassiveA3WithoutLast_apply` and
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dG_castSucc_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-product-rule-dg-substitution.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-product-rule-dg-substitution.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-product-rule-dg-substitution.md`
passed by xhigh `Averroes`.

The product-rule substitution theorem specializes the retained-passive
`dEarly` current summand to `p = q.castSucc` and rewrites the `A3p` derivative
factor as the passive source tangent `v.2.2.1 q`, preserving the matrix order
`Cprod * dG * Pcast^{-1}`.  Focused module build, `scripts/sorries`,
`git diff --check`, full `DLNFibre` build, and theorem axiom audit passed;
both new theorems have only the standard `[propext, Classical.choice,
Quot.sound]` footprint.  Nonclaims: no `dCprod` staging, no `dPcast` staging,
no target staging, no full positive-tail `F3` target staging, no determinant
theorem, no measure theorem, no normal crossings, pole order, or RLCT.

Latest A2 retained-passive dEarly terminal zero-tail boundary:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassiveLowerLeftProductTailSum_withoutLast_last_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-terminal-zero-tail.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-terminal-zero-tail.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-terminal-zero-tail.md`
passed by xhigh `Aquinas`.

At the terminal tail index `M (Nat.le_succ M)`, the retained-passive lower-left
product-tail sum built from `retainedPassiveA3WithoutLast` is pointwise the
constant zero map, by the algebraic lemma
`retainedPassiveLowerLeftProductTailSum_withoutLast_last`.  The derivative is
therefore zero without any determinant-chart or invertibility hypothesis.
Focused module build, `scripts/sorries`, `git diff --check`, full `DLNFibre`
build, and theorem axiom audit passed; the theorem has only the standard
`[propext, Classical.choice, Quot.sound]` footprint.
Nonclaims: not solved terminal lower-left `A3`/`F3`, no `dCprod` staging, no
`dPcast` staging, no target staging, no full positive-tail `F3` target
staging, no determinant theorem, no measure theorem, no normal crossings,
pole order, or RLCT.

Latest A2 retained-passive dEarly dCprod source staging:
`RetainedPassiveCoordinatesDerivative.lean` proves
`fderiv_retainedPassive_C_apply`,
`fderiv_retainedPassive_C_residualFactorProduct_castSucc_apply`, and
`fderiv_retainedPassiveLowerLeftProductTailSum_castSucc_product_dCprod_dG_castSucc_apply`.
Reproduction:
`threads/03-block-product-reduction/reproduction-a2-retained-passive-dearly-dcprod-source-staging.md`.
Statement card:
`threads/03-block-product-reduction/statement-card-a2-retained-passive-dearly-dcprod-source-staging.md`.
Review:
`threads/03-block-product-reduction/review-a2-retained-passive-dearly-dcprod-source-staging.md`
passed by xhigh `Lovelace`.

This uses `residualFactorProduct_castSucc` and the product rule to rewrite the
stored-`C` suffix derivative as
`dCnext_z(v) * C_z(q.succ) + Cnext(z) * v.2.2.2.1(q.succ)`, then substitutes
that expression into the already dG-staged `dEarly` current summand.  Focused
module build, `scripts/sorries`, `git diff --check`, full `DLNFibre` build,
and theorem axiom audit passed; all three new theorem names have only the
standard `[propext, Classical.choice, Quot.sound]` footprint.  Nonclaims: no
`dPcast` staging, no closed finite-sum formula for `dCprod`, no target
staging, no determinant theorem, no measure theorem, no normal crossings, pole
order, or RLCT.
