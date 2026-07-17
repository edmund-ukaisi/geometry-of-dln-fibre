# Reuse-map cert — banked library vs the transform-only engine (2026-07-17)

*From the infra-reuse-map seat (verified via git show/grep at genesis refs; bank =
lean/DLNFibre/DLN/RLCT/ on the merged genesis tip: 530 modules / ~160k LoC; ~130 genuine open
sorries of which ~70 sit on paths this engine never touches; monomial_rlct-FREE since 2026-07-09).*

## The one-Prop interface (confirmed)
The engine owes exactly `RouteMBoxThresholdFinite M` (`Validate/RouteMBoxReduction.lean:165`,
0-sorry def). Consumers proven: `aoyagi_learning_coefficient_gen` (HeadlineGenAssembly, 0-sorry,
clean-three force-printed, conditional solely on hbox); the ≤-half (`…_gen_le`,
`r1_resolution_general_le`) unconditional; plug-in wiring 0-sorry. Nothing else is owed.

## EXISTS-AS-IS (0-sorry, consume, never rebuild)
- Monomial threshold reads: MonomialThresholdIdentity, S1NodeBlowup, S1ProductMin.
- Terminal atoms: RouteMSJGammaAtom (gammaAtom_aniso_shifted_eq), RouteMSJQBoxCore,
  RouteMSJProductTube (detGram_lintegral_lt_top), RouteMSJRadialInt/RadialPolar.
- Box covers/null glue: S1Cover, S1BoxAdditive, RouteMCoverLemmas, RouteMNullSliceCov.
- Frobenius/Schur algebra: RouteMSchurAlg, RouteMSJGramResidual, RouteMSJGramSqrt, RouteMSJKyFan,
  RouteMSJRayleigh, frobSq_schur_split_inv.
- Rank charts: RouteMSJCorankStep/Survival/Residual/Peel, RouteMSJRankRCodim.
- Combinatorial budget, whole: RouteMLayerSplit (minAdm/minAdmRec), RouteMSJDecoratedCharge
  (peelCharge), MinAdmCCodim, MinAdmMono, MinAdmPermInvariance, + the QIP family (RouteMSJCorankRec).
- CoV primitives: CoreShearMP, CoreSplitMP, ParamsReshapeMP, DeepestSplitHaar, S1NonMPTransport.
- WORKED PRECEDENT: RouteMBoxThresholdRR4 — the (r,r,4) family end-to-end 0-sorry
  (sub → det-Jacobian → gammaAtom → cover → threshold). The engine = this pattern made generic.

## MISSING (the build, ~3–5 banked-module units)
1. **General chart-tree CoV composer** (~1–2 units): compose an arbitrary substitution tree onto
   the banked atoms; primitives exist, general glue open (ChartShear/S1Transport/RouteMSJTransport
   carry the open pieces).
2. **The tree recursion + coverage** (~2–3 units): Layer B statements + Layer C's reconstruction.
   (The predecessor's SJStepHyp-shaped "research wall" was route-relative — on THIS route the
   worked-out pp.14–22 construction is the filler; the honest new proof content is coverage.)
3. Measurable eigendecomposition — ALREADY BUILT sorry-free on genm-sj5 (merged into the genesis
   tip); verify import, do not rebuild.

## Cautions
- RouteMBoxThresholdRRP (the ∀p extension) carries 3 sorries — a different carve; scoped separately.
- ~70 of the ~130 open sorries live on the ≥-leg/D1-IFT/L2-gauge legacy paths — do NOT get pulled
  into closing them; they are off this route (mint re-point supersedes the Skeleton stubs).
- Predecessor lesson: survey banked state before commissioning ANYTHING (3 redundant commissions).
