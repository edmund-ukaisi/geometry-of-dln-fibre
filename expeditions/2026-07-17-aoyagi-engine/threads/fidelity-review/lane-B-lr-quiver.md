# Lane B (raw) — LR §§1–4 (quiver + mult + loci) enumeration + cross-check

Read-only scout output (elder-commissioned, 2026-07-23). Source main.tex 117–872; cross-checked against
`Core/*`. Core is sorry-free (the 6 "sorry" string hits are docstrings/history); no `@[cited]` in §§1–4
(cite-free engine). Synthesized into `../../paper-fidelity-review.md` §B.

## Key rows (PROVEN unless noted)
- Rep_d/mult/Σ^r/fibre: `Core/Setup.lean:33-66` (over any CommRing).
- Thm easy (iso↔orbit): `rankPattern_eq_iff_orbit` (Orbit.lean:267).
- Gabriel indecomposables: MODELED interval modules + barcode (IntervalModule.lean, Gabriel.lean:275);
  categorical classification not named.
- Kostant partitions: `kostantPartitions` (CTheta.lean:115), `IsKostantArray` (OrbitKostant.lean:243).
- Cor gabriel (orbits↔Kostant): `orbitKostantEquiv`, `orbitDiffArrayEquiv` (OrbitKostant.lean:104,218).
- Prop 3.1 mr_comparison (CR↔CM inverse): `diff_cumul`/`cumul_diff` (RankPattern.lean:185,198) +
  `rankFn_eq_iff_orbit` (OrbitKostant.lean:70).
- Voight lemma (slice≅Ext): MODELED — codim consequence proven `varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`
  (VoigtDischarge.lean:51); literal slice≅Ext iso NOT stated; categorical-Ext bridge DEFERRED (DeformationExt.lean:26).
- Cor 3.5 codim `Σm·m`: UNCONDITIONAL `codimRepCanonical_orbitRankLocus_eq_multSum_unconditional`
  (VoigtDischarge.lean:130). Ext-indicator `1[i<u≤j+1≤v]`: `finrank_deformationExt1_interval` (DeformationExt.lean:531).
- Thm addlongest: `codimForm_update_corner` corner-blind (CTheta.lean:215) + `cCodim_rankShift` (CTheta.lean:377).
- Orbit hierarchy + closures `O_s⊆Ō_r⟺s≤r`: `image_orbitRankLocus_eq_repClosure_orbitSet` (OrbitClosure.lean:993)
  + monotone. Paper CITES Abeasis-del Fra; **Lean proves it**.
- Σ^r stratification + Cor irred_comp: `productRankLocusLE_eq_iUnion_orbitRankLocus` (SigmaStratification.lean:135),
  `minimalPrimes_sigmaIdeal_eq`/`irreducibleComponents_sigmaIdeal_equiv` (SigmaComponents.lean:178,189).
- lem:sigma_non_empty: PROVEN in pieces (not one packaged iff; ⟸ needs N≥1).
- lem:rank_0: PARTIAL — codim/count shift PROVEN (`cCodim_rankShift`, `numTop_eq_cTheta_dminus`); explicit dim
  closed-form `(2Σd−d₀−d_N)r−Nr²` + geometric injection NOT named.
- **lem:rank_vs_fibers**: fibre codim PROVEN `codimRepCanonical_fibre_eq_cCodim_add_shift` (FibreCodimFinal.lean:171);
  θ-comp bijection PROVEN `ncard_topDimMinPrimes_fibre_eq_numTop` (FibreThetaCountUnconditional.lean:73);
  **locally-trivial bundle NOT** — `FibreBundleLocallyTrivial` self-disclaims (per-pivot local product + flatness;
  FibreBundleHeadline.lean).
- thm:base_field: PARTIAL — `varietyDim_baseChange_image` (VarietyDimBaseChange.lean:37); 3-claim package (esp.
  claim 3 real-analytic mfld) NOT formalized.
- rmk:real_points, cor:min_ud connected: ABSENT (real geometry, connectedness).
- perm-invariance of (C,θ): PROVEN `codimRepCanonical_productRankLocusLE_comp_perm`, `ncard_topComponents_comp_perm`
  (CThetaGeometricPerm.lean:60,73) [CharZero+Infinite].

## Least-sure + cross-cutting (scout)
1. lem:rank_vs_fibers bundle: codim + θ-count proven; the full locally-trivial bundle over Mat^{=r} NOT built
   (honest gap, self-disclaimed name).
2. thm:base_field: dim-invariance present; the packaged 3-claim thm (claim 3 real-analytic) not found.
3. cor:min_ud smooth AND connected: smoothness infra exists; connectedness no theorem anywhere in Core.
- CROSS-CUTTING: `Ext` throughout §3 is a concrete cochain MODEL `deformationExt1`; the categorical/derived-Ext
  identification is DEFERRED in-docstring (DeformationExt.lean:26). Codim NUMBERS proven unconditionally; the
  modeled-Ext = quiver-Ext¹ is the single most load-bearing name=content caveat in §§1–4.
