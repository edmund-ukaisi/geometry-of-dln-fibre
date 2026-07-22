# Lane A (raw) — Aoyagi RLCT-resolution side enumeration + cross-check

Read-only scout output (elder-commissioned, 2026-07-23). Source: worked.tex + preprint text; cross-checked
against `Core/Aoyagi/*`, `DLN/Aoyagi/*`, `DLN/RLCT/*`. STATUS from bare-sorry census + attributes + AxCheck
comments (NOT `#print axioms`-forced). Synthesized into `../../paper-fidelity-review.md` §A.

## Scope note
Three lanes coexist for `rlct = C/2`: **engine** (`aoyagi_learning_coefficient_via_engine`, single
geometric sorry at `exists_coreResolution` LearningCoefficient:311 + monument bulk MonumentAtlas 11 sorries);
**cited** (`AoyagiCited.rlct_lossDLN_zero_eq_half_cCodim_aoyagi`, PROVEN modulo 2 `@[cited]` axioms bracketing
the built `rlctGlobal`); **skeleton** (`Skeleton.aoyagi_learning_coefficient`, general-r/general-L, DIRTY root
carrying sorryAx; L=2/L=1 endpoints clean-three).

## Key rows (see synthesis §A for the full table)
- Lemma 1 (Object A): PROVEN sorry-free `rlctAt_sumSqFam_le_of_germRepresents`/`_eq_of_germ_eq`/`wrlctAt_*`
  (IdealInvariance). +2 guards LocallyNullZeros (junk-0) + Measurable weight (sound).
- boxed S2 rule (Object C): PROVEN sorry-free `monomialSumSq_wrlctAt_eq` (MonomialRLCT:432),
  `monomialSumSq_two_mul_wrlctAt_eq_min:650`. Needs DivChain. Docstring stale (calls itself blueprint frontier).
- coupled counterexample: `not_divChain_coupled_example` (MonomialRLCT:77).
- Lemma 2 block-elim: PROVEN sorry-free `block_elimination` (Skeleton:242).
- Thm 3 peel (general-r): STATED-sorried `product_reduction` (Skeleton:1105) → `deepest_regular_core_normal_form`
  sorry (Skeleton:1094). r=0: PROVEN `coreReduction` (LearningCoefficient:245).
- Thm 4 deepest point (D1): PROVEN instance `deepest_le_of_homogeneous_core` (DeepestMinRlct:157),
  `rlctGlobal_eq_rlctAt_zero_of_homogeneous` (GlobalHomog:171). All-vars homogeneity; sub-block form not reproduced.
- inductive invariant + b-chain + Jacobian ledger + Case1/2 + coupled diag(b) + Object B existence: the MONUMENT.
  `exists_coreResolution` (LearningCoefficient:311 @[blueprint]); MonumentAtlas 11 sorries; N_p re-bake
  (`canonNormalizationOf` MonumentAtlas:867, `_shearWithinCarve` CanonShear:125 sorry).
- M_{s,k}=Mval=codim + divisorMin=cCodim: PROVEN sorry-free `divisorMin_eq_cCodim` (Engine:45),
  `minAdm_eq_cCodim` (MinAdmCCodim:315), `cCodim_eq_qipMin` (CThetaQIPConverse:833).
- min-over-charts CoV: PROVEN sorry-free `rlctAt_sumSqFam_eq_iInf_charts` (ProductResolution:540) — worked.tex
  stale (still lists it open). Obligations folded into Chart fields.
- flatten: PROVEN sorry-free `exists_flatten` (LearningCoefficient:199), `canonFlatten:215`.
- θ order a(ℓ−a)+1: combinatorial PROVEN `aoyagiPoleOrder`/`rrrTheta`/`boxedOrder`; analytic pole-mult ABSENT.
- Watanabe upper / Aoyagi lower: CITED `cited_watanabe_upper_ax`/`cited_aoyagi_lower_ax` (AoyagiCited:57/67);
  engine lane aims to KILL the lower cite.
- paper defects (Def-3 (T-D), T-profile (T-F), Case-2 (T-E)): MODELED batteries; Lean records carry no
  corruptible field.

## Least-sure (scout)
1. Object C docstring lies (calls itself blueprint frontier; no @[blueprint] attr, zero sorries) — genuinely
   PROVEN, stale docstring. Not #print-axioms-confirmed clean-three.
2. min-over-charts leaf closed; worked.tex one architecture-step behind (2 sorries → effectively 1, the monument).
   The Chart field-set is under active repair (rev-fidelity FAIL bars ii+iv, task #52).
3. `cited_aoyagi_lower_ax` judgment (cited-by-design vs targeted): engine lane aims to kill it; depends on the
   engine-vs-cited destination choice.
