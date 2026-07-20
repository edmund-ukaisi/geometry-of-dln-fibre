# lr-survival reviewer verdict — dev L&R / Core-geometry survival across the dev→aoyagi-engine merge

**Function:** claim-soundness / fidelity (survival audit). **Scope:** did dev's L&R-formalised
geometry results survive the `origin/dev → expedition/aoyagi-engine` merge (union aggregator, archive
α-atlas chart Engine, drop 15 stale flat-Core imports)? **Method:** READ-ONLY. `#print axioms` over the
FRESH merged oleans via a scratch `import DLNFibre` elaborated with `lake env lean` (EXIT=0, no
unknown-identifier / no error on any name — which itself proves reachability from the aggregator closure);
`scripts/sorries` census; git inspection of the import-drop commit.

**Merge state at audit:** branch `expedition/aoyagi-engine`, HEAD `f383c478e`; the merge full build is
green (8958 jobs, per tick 426).

---

## (a) Results checked + `#print axioms` footprint

47 named results checked; **all axiom-clean** — `[propext, Classical.choice, Quot.sound]` unless marked
`[propext, Quot.sound]` (a strict subset — even cleaner, no `Classical.choice`). **No `sorryAx`, no
`cited_*`, no unaccounted axiom** anywhere in the geometry surface.

### Determinantal geometry (`Core/RingTheory/Determinantal/*`, `Core/Matrix/RankMinors`; `Matrix` ns)
- `rankStratumCodim_add_rankStratumDim_eq` — `[propext, Quot.sound]`
- `rankStratumDim_eq_ambient_sub_codim` — `[propext, Quot.sound]`
- `dim_params_eq_delta` — `[propext, Quot.sound]`
- `finrank_pivotRankChart_params_eq_rankStratumDim` — clean-three
- `rankLeLocus_eq_vanishingLocus` (rank↔minor bridge) — clean-three
- `rankEqLocus_eq_iUnion_inter_minorChart` (minor-chart cover) — clean-three
- `mem_rankLeLocus_iff_determinantalIdeal_le_ker` — clean-three
- `rank_eq_iff_schur_eq` — clean-three
- `schurComplement_normal_form` — clean-three
- `rank_le_iff_forall_submatrix_det_eq_zero` — clean-three
- `rank_map_eq_of_injective` — clean-three

### Local triviality / atlas (`Algebra` ns)
- `AtlasChart.tripleTransition_cocycle` — clean-three
- `AtlasFibreChart.overlapTransition_isProduct` — clean-three
- `StandardFibreChart.flatModel` — clean-three

### Minimal primes / top-dimensional component count (`Ideal` ns)
- `TopDimMinPrimes` (def) — clean-three
- `bijOn_comap_topDimMinPrimes` — clean-three
- `topDimMinPrimes_ncard_eq_of_ringEquiv` — clean-three

### Codimension engine (`DLNFibre.Core`)
- `cCodim` (def) — clean-three
- `codimRepCanonical_productRankLocusLE_eq_cCodim` (SigmaCodim headline) — clean-three
- `codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal` — clean-three
- `cCodim_stratum_eq` — clean-three
- `varietyDim_productRankLocusLE_stratum` — clean-three

### θ / component count
- `numTop_eq_ncard_topComponents` (UNCONDITIONAL θ headline) — clean-three
- `numTop_eq_ncard_topComponents_of` — clean-three
- `numTop_eq_card_minimising` — clean-three

### Permutation invariance
- `cCodim_comp_perm`, `numTop_comp_perm` (Core) — clean-three
- `minAdm_comp_perm`, `minAdm_eq_cCodim` (DLN; paper's central codim identity) — clean-three

### Orbit
- `codimRep_orbitRankLocus_eq_finrank_deformationExt1` — clean-three
- `finrank_cotangent_eq_varietyDim` — clean-three
- `finrank_range_deformationδ_le_varietyDim` — clean-three
- `isZariskiClosed_orbitRankLocus` (RankLocusClosed) — clean-three

### Fibre codimension final headline
- `codimRepCanonical_fibre_eq_cCodim_add_shift` (FibreCodimFinal) — clean-three
- `codimRepCanonical_fibre_eq_height_fibreGenIdeal` — clean-three
- `codimRepCanonical_fibre_eq_cCodim_add_shift_of_height_bounds` — clean-three

### Relocated-stack spot-checks (`Core/Dimension/*`, `Core/RingTheory/*` — the repointed modules)
- `Dimension.affine_domain_height_add_ringKrullDim_quotient_eq` — clean-three
- `Dimension.height_add_coheight_le` (Catenary) — clean-three
- `Dimension.finrank_cotangentSpace_le_of_isSmoothAt` (Regular) — clean-three
- `Dimension.height_eq_under_of_etale` (Smooth) — clean-three
- `Dimension.ringKrullDim_mvPolynomial_finite` (Codimension) — clean-three
- `trdeg_adjoin_le_genericDifferentialRank` (Trdeg) — clean-three
- `mapBaseChange_injective_of_formallySmooth` (Kaehler/GenericRank) — clean-three
- `Ideal.finrank_cotangentSpace_localization_eq_cotangent` (Ideal/CotangentLocalization) — clean-three
- `Localization.awayOverlapTransition_commutes` (Localization/Overlap) — clean-three
- `derivMatrix_mul_apply` (Derivation/Matrix) — `[propext, Quot.sound]`
- `MvPolynomial.jacobian_apply` (MvPolynomial/CotangentJacobian) — clean-three

---

## (b) Core sorry-census delta from the merge

`scripts/sorries` → **`25 sorry, 0 #exit, 0 native_decide, 3 axiom`** — matches the expected 25
(21 scaffold + 4 off-cone Engine). No growth.

- **Every sorry is DLN/RLCT-side.** The 4 off-cone Engine sorries live in the archived
  `DLN/RLCT/Engine/*` (`CanonicalWitness224`, `ClearableReify`, `GeoAlphaGauge`, `GeoAtlasTransfer`);
  the rest are scaffold in `DLN/RLCT/{Skeleton, Validate/*}` + the `AoyagiCited`/`Skeleton` roots.
- **Zero sorries in the L&R determinantal/orbit/codim/θ/fibre geometry.** The only `Core/` file the
  census flags is `Core/Analysis/RLCT/Cited.lean`, and that hit is the `cited_local_zeta_pole`
  **axiom** (a located cite), NOT a sorry.
- **The 3 axioms are all `@[cited]`-tagged** with source strings and none leaked into any of the 47
  geometry footprints:
  - `cited_local_zeta_pole` (`Core/Analysis/RLCT/Cited.lean`) — Atiyah 1970 / Saito–Watanabe local
    zeta pole = −rlct.
  - `cited_watanabe_upper_ax` (`DLN/RLCT/AoyagiCited.lean`) — Watanabe universal `rlct ≤ ½·codim`.
  - `cited_aoyagi_lower_ax` (`DLN/RLCT/AoyagiCited.lean`) — Aoyagi DLN lower half.

---

## (c) Reachability — nothing orphaned by the 15-import drop

- dev's relocated modules are all imported in `DLNFibre.lean` (lines 1496–1554): `Core.Dimension.*`,
  `Core.RingTheory.*` (incl. `Determinantal.{Strata,Dimension,Schur,LocalTriviality,Atlas,
  AtlasTransition}`, `Kaehler`, `Ideal`, `Localization`, `Derivation`, `MvPolynomial`),
  `Core.Matrix.RankMinors`, `Core.MinimalPrime.*`, `Core.MvPolynomial.*`, `Core.Analysis.RLCT.*`.
- The 47 successful `#print axioms` (elaborated against `import DLNFibre`) prove every checked result is
  in the aggregator closure — a `#print axioms` on an orphaned name would error; none did.
- The 15 dropped flat-Core imports (`IntegralDimension`, `NoetherMonicPositioning`,
  `AffineDomainDimension`, `FlatQuasiFiniteHeight`, `SmoothLocalRelativeDimension`, `SmoothPointRegular`,
  `CotangentJacobian`, `JacobianTrdeg`, `MatrixKaehler`, `DeterminantalChart`, `MvPolynomialKerAeval`,
  `GraphIdealHeight`, `SchurChartIff`, `LocalizationKrullDim`, `AffineLocalizationNoDrop`) point to files
  confirmed **absent** on disk — dev's reorg relocated their content to the nested paths above. Dropping
  the stale imports orphaned nothing.

## Checks not completed
- `scripts/cordon` (the enforcing whole-library cordon gate) timed out at the 5-min cap (heavy full
  pass). Substituted evidence: the 47 clean `#print axioms` footprints (none carry a cited/unaccounted
  axiom) + grep-confirmation that all 3 axioms are `@[cited]`-tagged. This covers the cordon's substance
  for the L&R surface; a full green `scripts/cordon` remains available if the whole-TCB stamp is wanted.

---

## VERDICT: **SURVIVE-CLEAN**

All 47 load-bearing dev L&R / Core-geometry results survive the merge with clean-three (or narrower)
axiom footprints; zero `sorryAx`, zero cited-axiom leak into geometry, zero Core-side sorry growth,
zero orphaning. The merge was additive to dev's Core, as expected. No regression found.
