-- DLNFibre — single-writer aggregator.
-- Add new module imports at the end; do not reorder existing imports.
-- Core = the network-free engine; DLN = the application (depends on Core).
import DLNFibre.Core.Basic
import DLNFibre.Core.Setup
import DLNFibre.Core.RankPattern
import DLNFibre.Core.Submult
import DLNFibre.Core.IntervalModule
import DLNFibre.Core.BaseChange
import DLNFibre.Core.Barcode
import DLNFibre.Core.Gabriel
import DLNFibre.Core.Orbit
import DLNFibre.Core.OrbitKostant
import DLNFibre.Core.DeformationExt
import DLNFibre.Core.OrbitLinearCodim
import DLNFibre.Core.OrbitCodim
import DLNFibre.Core.CTheta
import DLNFibre.Core.CThetaQIP
import DLNFibre.Core.CThetaQIPConverse
import DLNFibre.DLN.Basic
import DLNFibre.Core.CThetaExplicit
import DLNFibre.Core.CThetaDropM
import DLNFibre.Core.CThetaValue
import DLNFibre.Core.CThetaThetaBridge
-- Voigt-discharge / geometric-codimension Core engine (PR #4, merged to dev).
import DLNFibre.Core.IntegralDimension
import DLNFibre.Core.PolynomialDimension
import DLNFibre.Core.NoetherMonicPositioning
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.AffineDomainDimension
import DLNFibre.Core.FlatQuasiFiniteHeight
import DLNFibre.Core.SmoothLocalRelativeDimension
import DLNFibre.Core.SmoothPointRegular
import DLNFibre.Core.PolynomialCurveLimit
import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.CotangentJacobian
import DLNFibre.Core.BoxMoveDegeneration
import DLNFibre.Core.RankLocusClosed
import DLNFibre.Core.BoxMoveGeneral
import DLNFibre.Core.BoxMoveGeneration
import DLNFibre.Core.OrbitClosure
import DLNFibre.Core.OrbitPullbackDim
import DLNFibre.Core.OrbitSmooth
import DLNFibre.Core.AffineNoetherRank
import DLNFibre.Core.JacobianTrdeg
import DLNFibre.Core.OrbitImageDim
import DLNFibre.Core.OrbitDifferential
import DLNFibre.Core.MatrixKaehler
import DLNFibre.Core.OrbitDifferentialRank
import DLNFibre.Core.OrbitTangentCotangent
import DLNFibre.Core.VoigtDischarge
import DLNFibre.Core.CThetaGeometric
import DLNFibre.Core.SigmaStratification
import DLNFibre.Core.SigmaComponents
import DLNFibre.Core.ThetaComponentCount
import DLNFibre.Core.CCodimCornerMono
import DLNFibre.Core.CCodimZeroMono
import DLNFibre.DLN.RlctPayoff
import DLNFibre.DLN.RlctPayoffGeneral
import DLNFibre.Core.CCodimZeroStrict
import DLNFibre.Core.SigmaCodim
-- q-series primitives (perm-invariance M1): P / Pm / Pmult / Qseries + constant-term-1 + nonneg.
import DLNFibre.Core.QSeries
-- N=1 Durfee identity (perm-invariance M2): P a · P b = ∑_r X^{(a-r)(b-r)} P(a-r) P r P(b-r).
import DLNFibre.Core.QSeriesDurfee
-- Local transfer identity (perm-invariance M3 engine): transferRHS b d = P d · ∏ P bᵢ.
import DLNFibre.Core.QSeriesPeel
-- (C,θ) extraction (M5/L1): cCodim/numTop recovered from Qseries; the symmetry bridge.
import DLNFibre.Core.QSeriesExtraction
-- Permutation invariance prep (perm-invariance M6): Pmult is multiset-symmetric.
import DLNFibre.Core.CThetaPermInvariance
-- Thm 5.6 (the "fivegon", perm-invariance M3b): fivegonSum d = Pmult d, via last-column transfer.
import DLNFibre.Core.QSeriesFivegon
-- Thm 5.5 (M4): corner shift, inverse-Pochhammer orthogonality, per-r Poincaré product.
import DLNFibre.Core.QSeriesShift
import DLNFibre.Core.QSeriesOrth
import DLNFibre.Core.QSeriesThm55
-- Geometric transfer of Cor 5.10: the variety's (C,θ) of Σ̄^r is permutation-invariant (given
-- Kostant-set nonemptiness; discharged from 1 ≤ N + r ≤ min d by the _of_le wrappers).
import DLNFibre.Core.CThetaGeometricPerm
-- Explicit closed-form (C,θ) for an ARBITRARY (non-monotone) d: compose the sort bridge with the
-- Monotone-gated cValue/cTheta. cCodim d r = cValue ((d−r) ∘ Tuple.sort (d−r)) (and θ via cTheta).
import DLNFibre.Core.CThetaArbitrary
-- Determinantal-stratum dimension (fibre-codim AG build, rung 1): dim Mat^{rk≤r}_{m×n} = r(n+m−r),
-- via the N=1 specialisation of the quiver engine (productRankLocusLE ![n,m] r = the determinantal variety).
import DLNFibre.Core.DeterminantalStratumDim
-- Generic tuple over the coordinate ring (shared, CommRing): genericTuple + eval_genericTuple,
-- reused by RankLocusClosed (minor polys) and MultComorphism (the coordinate-ring map of mult).
import DLNFibre.Core.GenericTuple
-- Comorphism keystone (fibre-codim AG build, F1): the coordinate-ring map of `mult` (generic product
-- entries multPoly = mult over MvPolynomial), the bridge eval_multPoly, the fibre as a zero-locus,
-- and fibreGenIdeal = Ideal.map multComap (maxIdealOfPoint B) — the fibre-ring quotient F2 consumes.
import DLNFibre.Core.MultComorphism
-- Fibre-codim LOWER bound (partial Lemma 4.6): codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹ B)
-- from mult⁻¹B ⊆ Σ̄^r. The +r(d_0+d_N−r) shift (the full identity) is now PROVED in FibreCodimFinal
-- (route-β chart build); this module supplies the lower-bound half it anticipated.
import DLNFibre.Core.FibreCodim
-- Fibre-codim G1 (rank-chart build): same rank ⟹ same fibre codim (N≥1), via the GL×GL end-factor
-- action + mult-equivariance + height-comap codim-invariance + rank normal form. Reduces Lemma 4.6
-- to a single normal-form fibre.
import DLNFibre.Core.FibreNormalForm
-- Determinantal pivot-chart presentation (rank-chart build G2-1): the Schur rank criterion
-- rank (fromBlocks Δ B12 B21 B22) = card m ↔ B22 = B21·Δ⁻¹·B12, the explicit chart parametrization
-- Mat^{rk=r}∩U ≅ GL_r × Mat × Mat, + reusable block-diag rank additivity. Feeds G2-3 (the Schur AlgEquiv).
import DLNFibre.Core.DeterminantalChart
-- Bordered Schur minor (G2-2 sub-rung 1): det [[Δ,u],[v,d]] = d·detΔ − v·adjΔ·u over ANY CommRing
-- (universal-coefficient route, no invertible pivot), and the Schur expression = an (r+1)-minor ⟹
-- vanishes on Mat^{rk≤r}. The generator-free handle for the localized base presentation (dodges
-- determinantal-ideal theory, absent at v4.29).
import DLNFibre.Core.DeterminantalChartRing
-- ker of a multivariate aeval = the graph ideal (reusable, arbitrary index type), + the elimination
-- quotient equiv + graph-ideal primality. The generator-free elimination engine (G2-2).
import DLNFibre.Core.MvPolynomialKerAeval
-- Height of a block graph ideal over a field = #eliminated vars (catenary). The `height J = C` engine (G2-2).
import DLNFibre.Core.GraphIdealHeight
-- Reindex + detΔ-localization bridge for the determinantal base: repCoordReindex, blockAlgEquiv
-- (A_eng ≃ MvPolynomial B22block (MvPolynomial SchurVar k)), blockAlgEquiv_detPivot (detΔ ↦ C detSchurS).
-- The reindex/detΔ infra feeding the final localized-base presentation (G2-2 D2).
import DLNFibre.Core.DeterminantalBaseElimination
-- G2-2 COMPLETE: the localized base presentation `basePresentationEquiv : A_loc/Iad ≅ₐ[k] Sd`
-- (free Schur localization, regular dim δ), via the bordered-minor identity (*) + the height squeeze
-- Iad = J (earned honestly, not assumed). Feeds G2-3 (the total presentation + flatness).
import DLNFibre.Core.DeterminantalBasePresentation
-- Route-(b) reducedness chain for G2-3 (R2-3a): the tensor-with-a-field reducedness descent (PROVED),
-- CONDITIONAL on a deep product iso `e : S ≃ₐ[k] R ⊗ F_B` + `IsReduced S`. SUPERSEDED: codim=C+δ was
-- instead closed by the route-β localized chart AlgEquiv (ChartLocalizedAlgEquiv) + FibreCodimFinal;
-- this conditional R2-3b chain is off the critical path (retained as record).
import DLNFibre.Core.FibreReducedTrivialization
-- Deep chart ring (R2-3b-1+2, an early R2-3b-route module): `Sred = Localization.Away(ΔPdeep) ⧸
-- IadDeep` for general d (the engine's base presentation is N=1 only), the RepCoord↔stratum/endpoint
-- bridges, and the localized base→total map `schurToSred : SchurLoc → Sred` giving Sred its
-- SchurLoc-algebra structure (R2-3a's R = SchurLoc, S = Sred). The crux containments (det transport,
-- base→deep sigmaIdeal, NON-circular) proved. OFF the critical path: route-β (ChartLocalizedAlgEquiv)
-- built `e` instead; a self-contained component of the superseded R2-3b route.
import DLNFibre.Core.DeepChartRing
-- Endpoint-normalization gauge AlgEquiv (R2-3b-3): the vertex-unit conjugation `Aᵢ ↦ P_{i+1}·Aᵢ·P_i⁻¹`
-- (= landed `BaseChange.baseChange`) on the generic tuple, `gaugeEquiv d P`, over arbitrary CommRing R,
-- + the transport `gaugeEquiv (multPoly) = P_last·M·P_0⁻¹` (endpoint gauge P_0=H, P_last=L⁻¹ ⟹ L⁻¹·M·H⁻¹).
-- The coordinate change `mult(A)=LEH` ↦ `mult(Ã)=E`. Its `gaugeEquiv` is reused by route-β's seams.
import DLNFibre.Core.EndpointNormalization
-- HEIGHT-DIRECT route, rung H1 (radical-insensitive retarget): `Ideal.height_radical` (height(radical I)
-- = height I, no hypotheses) + `codimRepCanonical_fibre_eq_height_fibreGenIdeal` (codim of the fibre =
-- height of the cut ideal, [IsAlgClosed k] only — NO radicality). Decouples the codim from the (off-path)
-- radicality wall: the RLCT payoff needs only this height.
import DLNFibre.Core.FibreHeightDirect
-- HEIGHT-DIRECT rung H2 (the differential of mult): `multSuffix` (suffix product, mirror of multPrefix) +
-- `pderiv_multPoly`/`eval_pderiv_multPoly` — d(mult) entry = (suffix column s)·(prefix row t), the rank-one
-- outer product per factor. The Jacobian-entry brick H3 (generic Jacobian rank) consumes.
import DLNFibre.Core.MultDifferential
-- HEIGHT-DIRECT rung H3a (assemble the fibre Jacobian): `fibreGen`/`fibreJacobianMatrix`/`fibreJacobian`
-- (entry = eval_pderiv_multPoly = multSuffix·multPrefix), the UNCONDITIONAL tangent = ker(Jacobian)
-- identity (`finrank_cotangentSpace_fibre_eq_finrank_ker`) + the card-rank reading
-- (`finrank_ker_add_rank_fibreJacobianMatrix`: finrank ker + rank = card). H3b supplies rank = C+δ at a
-- generic point; H3c supplies generic smoothness ⟹ ker finrank = local fibre dim.
import DLNFibre.Core.FibreJacobian
-- Route-c sweep structure (homogeneous sweep): `Σ^r = H·F` (`productRankLocus_eq_iUnion_smul_fibre`)
-- via `mult_smul` + `exists_baseChange_of_rank_eq`; every translate same codim (G1). The reachable part
-- of the bundle-shift; the sweep dim-identity `dim Σ^r = δ + dim F` (hSweep) is the residual (= the
-- generic-freeness build, thread 29).
import DLNFibre.Core.EndBaseChangeSweep
-- Reducible-locus catenary: `height I + ringKrullDim(R⧸I) = card` for ANY proper I (no radicality), and
-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
import DLNFibre.Core.RadicalCatenary
-- H5 per-component→codim closer (reusable): `height_eq_of_minimalPrimes_bounds` (height I = v from the
-- per-minimal-prime bounds) + the codim retarget at v = C+δ + G1-transport (one rank-r witness ⟹ all B).
-- NOTE: parallel route-B (minimal-primes) CONDITIONAL bank, superseded by the unconditional
-- FibreCodimFinal route; retained (honestly named `…_of_height_bounds`), not on the critical path.
import DLNFibre.Core.FibreCodimMinPrimes
-- Route-c assembly (conditional bank): `codimRepCanonical(fibre d B) = C + δ` for rank-r B, carrying
-- the sweep dim-identity `hSweep` + the density `hClosure` as named hypotheses (both since discharged
-- in-repo: hSweep in FibreCodimFinal, hClosure in ClosureBridge); catenary hyps via RadicalCatenary.
import DLNFibre.Core.RouteCAssembly
-- (b)-build rung 1 — generic freeness (Grothendieck's lemma, MODULE case): a f.g. module over a
-- (Noetherian) domain is free/flat after inverting one nonzero element (via the Mathlib substrate
-- `exists_free_localizedModule_powers` + FractionRing-is-a-field). Reusable general lemma + a stepping
-- stone for the finite-type-ALGEBRA case (EGA IV 6.9.1, the positive-relative-dim case the fibre needs).
import DLNFibre.Core.GenericFreeness
-- (b)-build route-c foundation: `VarietyDimRadical` — the non-circularity SHIELD `ringKrullDim_quotient_radical`
-- (Krull dim radical-insensitive ⟹ the varietyDim build never re-enters the R2-3b-4 reducedness circularity)
-- + `varietyDim_eq_of_coordRingAlgEquiv` (transport varietyDim across a coordinate-ring AlgEquiv). `SchurGauge`
-- — the Schur pivot block is a SchurLoc-unit (det = the inverted detSchurS), the unit the gauge L/H blocks use.
import DLNFibre.Core.VarietyDimRadical
import DLNFibre.Core.SchurGauge
-- (b)-build route-c: generator-free varietyDim transport. `varietyDim_baseChange_image` (varietyDim
-- invariant under the GL×GL base-change image, no determinantal-ideal theorem) +
-- `varietyDim_fibre_endpoint_conj_eq` (constant fibre dim along the endpoint orbit).
import DLNFibre.Core.VarietyDimBaseChange
-- hClosure PROVED (thread-32 codim sandwich, zero-cite): varietyDim Σ^r = varietyDim Σ̄^r via
-- codim Σ^r = codim Σ̄^r = C (irreducibility-free catenary + ONE corner-r witness orbit), wired into
-- RouteCAssembly so codim(fibre)=C+δ now carries ONLY hSweep.
import DLNFibre.Core.ClosureBridge
-- hSweep build (chart-trivialization): general matrix-rank helpers
-- (diag(I_r,0) rank; rank=0 iff 0; block-diagonal rank-additivity).
import DLNFibre.Core.RankNormalFormDim
-- rung-1 chart-membership iff: rank(mult A) ≤ r ⟺ Schur block = 0 on detΔ≠0.
import DLNFibre.Core.SchurChartIff
-- rung-3 +δ: varietyDim W = varietyDim F + card ι from a coordinate-ring AlgEquiv (domain-free).
import DLNFibre.Core.VarietyDimPolyExtension
-- rung-2a chart normalization: L⁻¹·M·H⁻¹ = diag(I_r,0) over k + factor_chart_matrix (L·E·H = M).
import DLNFibre.Core.ChartSection
-- rung-2b tuple retraction: chartGauge(mult A)•A ∈ fibre E — the regular φ→F via mult_smul.
import DLNFibre.Core.ChartRetraction
-- rung-2 set-level chart bijection Σ^r∩U_Δ ≅ base × F, both directions (round-trip).
import DLNFibre.Core.ChartBijection
-- no-drop ≤ half: ringKrullDim(localization) ≤ ringKrullDim of the ring.
import DLNFibre.Core.LocalizationKrullDim
-- step-3a: gauge-conjugation transport at endpointGauge over SchurLoc
-- (gaugeEquiv(endpointGauge)(multPoly) = L⁻¹·multPoly·H⁻¹).
import DLNFibre.Core.ChartGaugeNormalize
-- no-drop machinery (shared by step-4/5): affine-domain dim(D[1/g])=dim D + the abstract
-- no-drop dim(R[1/g])=dim R when g avoids a top prime of a reducible Noetherian R.
import DLNFibre.Core.AffineLocalizationNoDrop
-- route-3 dimension-arithmetic wrapper (localized chart AlgEquiv + the two no-drops).
import DLNFibre.Core.ChartLocalizedPolyDim
-- schur-side no-drop input (dim(P[1/gfib]) = dim P for P a polynomial extension of O(F)).
import DLNFibre.Core.SchurSideNoDrop
-- clearing-denominators zero-test for the localized-chart-AlgEquiv descent (vanishingIdeal-side).
import DLNFibre.Core.PrincipalOpenComorphism
-- step-3 wiring skeleton: localized chart AlgEquiv e + the two no-drops ⟹ the hSweep shape.
import DLNFibre.Core.ChartSweepWiring
-- route-3 point-realization (seam B): an MvPolynomial vanishing on all fibre points is zero.
import DLNFibre.Core.SchurFibreVanishing
-- chart-descent geometry (seams toward e): localized chart coordinates + Schur-side connection.
import DLNFibre.Core.ChartLocalizedCoordinates
import DLNFibre.Core.ChartSchurConnect
-- Ψ descent (route-3): the substitution into the localized chart + its reconstruction.
import DLNFibre.Core.ChartPsiSubstitution
import DLNFibre.Core.ChartPsiReconstruct
-- gauge-eval commute (seam A): point evaluation, the gauge eval, and the A.3/A.4 tower lemmas.
import DLNFibre.Core.ChartPointEval
import DLNFibre.Core.ChartEvalGauge
import DLNFibre.Core.ChartEvalLemma
import DLNFibre.Core.ChartEvalGaugeCommute
-- chart-eval lemma proper (#66) + geometric realization A∈Σ^r (the route-β descent's eval input).
import DLNFibre.Core.ChartEvalRealize
-- seam C (Ψ descent, closed): chartPsiQuot + the sorry-free chartPsiLoc (localized Ψ hom).
-- chartPsi_dsig_isUnit + chartPsiLoc live in ChartPsiDsigUnit (circular-dep fix).
import DLNFibre.Core.ChartPsiDescent
import DLNFibre.Core.ChartPsiDsigUnit
-- seam D (Φ direction, closed): the forward-gauge comorphism + Σ-side chart-point eval descent.
import DLNFibre.Core.ChartPhiSubstitution
import DLNFibre.Core.ChartPhiFibCoord
import DLNFibre.Core.ChartSigmaAwayZero
import DLNFibre.Core.ChartSigmaEval
import DLNFibre.Core.ChartSigmaEvalGauge
import DLNFibre.Core.ChartSigmaEvalRealize
import DLNFibre.Core.ChartSigmaGaugeBridge
import DLNFibre.Core.ChartPhiDescent
-- chartPhiLoc : Away gF →ₐ[k] Away dsig (the Φ-direction localized hom; seam E glues e from it).
import DLNFibre.Core.ChartPhiLoc
-- seam E (route-β hard rung CLOSED): gauge tower law + Φ∘Ψ/Ψ∘Φ round-trip legs + the localized
-- chart AlgEquiv e := chartLocalizedAlgEquiv : Away dsig ≃ₐ[k] Away gF (AlgEquiv.ofAlgHom).
import DLNFibre.Core.ChartGaugeTower
import DLNFibre.Core.ChartRoundTrip
import DLNFibre.Core.ChartRoundTripH1
import DLNFibre.Core.ChartLocalizedAlgEquiv
-- hsig (source no-drop): ringKrullDim (Away chartDsig) = ringKrullDim O(Σ^r), anchored on =r.
import DLNFibre.Core.SourceNoDrop
-- THE CENTRAL RESULT: codim(fibre d B) = C + δ = cCodim + r·(d_N+d_0−r), unconditional (k : Type 0).
import DLNFibre.Core.FibreCodimFinal
-- THE PAYOFF (destination): BundleShiftInterface discharged from Core — rlct(K^DLN_B)=(C+δ)/2 rests
-- on ONLY the Cited Aoyagi RlctInterface; the geometric half is Proved (k : Type 0). [#52/G4]
import DLNFibre.DLN.BundleShiftDischarge
-- Source-shaped Aoyagi formula surface: her λ formula, with cValue/codim bridge stubs.
import DLNFibre.DLN.Aoyagi.ClosedForm
import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.Lambda
import DLNFibre.DLN.RLCT.BGEngine
import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.Case111Bridge
import DLNFibre.DLN.RLCT.Validate.Case111
-- Measure-side engines, built ahead of their consumers. Kept in the green-gate explicitly: else
-- `lake build DLNFibre` only covers the headline's transitive closure and an orphan engine (broken
-- or unsound) escapes the gate. Re-importing an already-reachable module is harmless (deduped).
import DLNFibre.DLN.RLCT.Foundations.S1Transport
import DLNFibre.DLN.RLCT.Foundations.S1Local
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock
import DLNFibre.DLN.RLCT.Foundations.S1Additive
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import DLNFibre.DLN.RLCT.Foundations.S1G5
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Foundations.S1Cover
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat222
import DLNFibre.DLN.RLCT.Validate.Case212
import DLNFibre.DLN.RLCT.Validate.Case222Value
import DLNFibre.DLN.RLCT.Validate.Case222Cover
import DLNFibre.DLN.RLCT.Validate.Case222Algebra
import DLNFibre.DLN.RLCT.Validate.Case222Lemma2
import DLNFibre.DLN.RLCT.Validate.Case222Resolution
-- (2,2,2) ≥-cover + RLCT headline (ladder 3/3). `Case222Rlct` transitively pulls the cover
-- (`Case222CoverGE`/`Case222CoverGETail`) into the green-gate — else the eq headline + the ≥-cover
-- are not in the build's transitive closure and escape the gate.
import DLNFibre.DLN.RLCT.Validate.Case222Rlct
-- General-M resolution recursion (det-1 straightening phase): the sound recursion-step
-- + `rlctAtOn_germ_local` + the L=1 smooth-block leaf. Kept in the green-gate (0 sorry).
import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion
-- RRR (L=2 / reduced-rank-regression): Aoyagi Thm 1 as the L=2 instance of the general headline
-- (`aoyagi_rrr`) + sorry-free anchors (3/2, 1) + combinatorial `rrrTheta`. General-L-first.
import DLNFibre.DLN.RLCT.Validate.RRR
-- LayerSplit re-architecture: the layer-collapsing carrier + keystone `minAdmRec_eq_minAdm` (R1 carrier
-- blocker resolved; not yet wired into routeStep — the controller-gated migration). Aggregator-gated.
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.RouteMLayerValue
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCover
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGE
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGEL2
import DLNFibre.Core.Matrix.RankNormalForm
import DLNFibre.Core.Matrix.RankNormalFormTriangular
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.DLN.RLCT.Validate.DeepestBaseL1
import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteM4422
-- `RouteM221`: the (2,2,1) NodeAchieverChart VALIDATE-SMALL — the option-(C) chart
-- `phi221 = paramsEquivFlat ∘ pack221 ∘ pivotBlowupOn {0,1} 0` (full-rank pack via the banked
-- `measurePreserving_paramsPack_of_flatIdxEquiv` fed a genuine `Equiv`; the D1 dead-slot guard)
-- built end-to-end through the GENERAL machinery, discharging the atom for a LAYERED node
-- (rate `(u 0)²·U` + det `|u 0|^{minAdm−1}`, both via the general bricks the ∀M build reuses).
import DLNFibre.DLN.RLCT.Validate.RouteM221
-- `RouteM222Det`: ROUTE 2a on the (2,2,2) multi-boundary node — the RATE leg (det leg WIP).
-- `B_det222` (fresh FULL-RANK GenBlk, leaf `Rfin 2 = !![1,x7] ≠ 0` — the D1 fix) at the GENUINE
-- achiever path `tach222 = (2,1,0)` (chain-codim = minAdm = 3, distinct from StructAdm's rate-only
-- (2,1,1)) + `routeMCore_phiDet222 = u²·V` via a ONE-LINE `routeMCore_phiGen` instantiation
-- (NO bridge; two rank-drops telescope to one `u`). Confirms route 2a on a multi-boundary node.
import DLNFibre.DLN.RLCT.Validate.RouteM222Det
-- `RouteMAchieverPath`: ∀M-lift step 1 — the achiever descent path made width-parametric.
-- `tStar M` (a chosen `Mval`-minimizer) + `Mval_tStar_eq` (the path realises `minAdm`) + the Aoyagi
-- residual blocks `rBlock`/`cBlock` + `sum_rBlock_cBlock_eq_minAdm` (the radial `active.card = minAdm`
-- identity). The (2,2,2) `tach222` generalized; regression-checked on the 5 anchors.
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverPath
-- `RouteM3333Det`: the (3,3,3,3) ROUTE-2a validate-small — the 3-BOUNDARY forcing case
-- (rank drops at all 3 boundaries, the Schur/LDU coupling the L=2 anchors don't exercise).
-- `B_det3333` (full-rank, t*=(2,1,0), minAdm 6) + `chartParamsGen_eq_chartParams3333` (THE
-- width-parametric bridge template) + `phiGen_B_det3333_eq_phi3333` (the route-2a chart EQUALS the
-- banked hand-built phi3333 ⟹ det |u0|⁵·|u1|⁴·|u4|²·|u9|³ = RouteM3333Atom EXACTLY) → atom via route 2a.
import DLNFibre.DLN.RLCT.Validate.RouteM3333Det
-- ∀M-lift build phases (1)-(2): the achiever decoder + RATE-side NodeAchieverChart fields, ∀M.
-- `RouteMAchieverStructAdm`: `tach M = Fin.cons (M 0) (tStar M)` (the shifted achiever path) +
-- `structAdm_tach` (admissibility ∀M, via the corrected `StructAdm.hdesc` interior-only descent).
-- `RouteMAchieverRateFields`: `routeMCore_achieverPhi = (x p)²·achieverUfun` (rate ∀M, decoder-agnostic)
-- + `achiever_leaf_integrand` (the `leaf_integrand` field ∀M, det-free) + `achieverUfun_nonneg`.
-- (The `Ubound` a.e.-positivity needs the MvPolynomial `Hmat_0` encoding — the next tide.)
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverStructAdm
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverRateFields
-- ∀M-lift phase 3: the rate-side `Ubound`/`Umeas` ∀M via the MvPolynomial encoding (the chain stack
-- conservatively generalized to `CommRing 𝕜`, `𝕜:=ℝ` default). `achieverUfun_eq_eval` (the unit IS
-- `eval x` of the named `UPolyGen`), `achieverUfun_measurable` (Umeas DONE), `achieverUbound`/
-- `achieverUfun_ae_pos` (Ubound DONE) GIVEN the witness `∃ w, achieverUfun w ≠ 0` (the sole remaining gap).
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverVvalPoly
-- ∀M-lift, the INTERIOR-DROP branch (285/351 M) of the v2 4-branch witness: `InteriorDrop M` (the
-- chain-native decidable classifier, validated ↔ the cert's deepest-interior class) + the corrected
-- colPath witness `exists_achieverUfun_ne_zero_interior` (Hmat_0(ρ,0)=1 via three downward inductions) →
-- `achieverUbound_interior` — the full `NodeAchieverChart.Ubound` field for interior-drop M (no separate
-- witness hypothesis). Reviewer-PASS, S2-free. (Boundary CLEAN/SMEARED + the 4-way assembly = later tides.)
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior
-- The ∀M achiever-chart M-CLASSIFIER bedrock (for the `nodeChartGeneral` 3-way+L1 assembly):
-- `BoundaryClean` (`r=m1`) / `BoundarySmeared` (`r<m1`) complementing `InteriorDrop`, with the
-- INTERIOR/CLEAN/SMEARED trichotomy (pairwise-exclusive + exhaustive, given the validated bottleneck
-- `r ≤ m1` carried as a hypothesis — the argmin widths are noncomputable).
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryClass
-- CLEAN/SMEARED-reusable boundary bedrock: `RouteMBoundaryCleanMinAdm` — the chain↔Aoyagi bridge +
-- the boundary `minAdm M = deepRows·M_last` identity (clean: `m1·M_L`; reused for smeared `r·M_L`).
-- `RouteMBoundaryCleanChart` — `deepestCoords M` (layer-(L−1) flat coords) + `deepestCoords_card_eq_minAdm`
-- (the `active.card = minAdm` fact the radial blow-up's det exponent `minAdm−1` consumes).
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanMinAdm
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanChart
-- BOUNDARY-CLEAN branch (WALL 2): the clean radial chart `pivotBlowupOn deepestCoords` discharges the
-- achiever atom ∀ M with `NoInteriorBothDrop` — `RouteMBoundaryCleanRate` (`routeMCore_cleanPhi`, the
-- loss factorization via the once-paid `paramsEquivFlat_symm_decode`), `RouteMBoundaryCleanU`
-- (`UPolyClean_ne_zero`/`cleanUbound`, U≢0 a.e.), `RouteMBoundaryCleanChartFull` (`cleanNodeChart` +
-- `routeMCore_box_diverges_clean`, a.e. `leaf_integrand` via `Eventually.of_forall`, det/cov via the
-- GENERIC `pivotBlowupOn` lemmas — the easy polynomial branch). Reviewer-PASS, validated on (4,4,2,2).
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanRate
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanU
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanChartFull
-- R1-general achiever SMEARED branch — (1,2,1) validate-small. The boundary-SMEARED M (r < m1) use a
-- RATIONAL single-pivot chart whose pole makes `image_subset` fail, so the reusable
-- `routeMCore_box_diverges_of_MPChart` discharges the atom via a MeasurePreserving final step
-- (`∫_{cubeBox}=∫_{φ⁻¹(cubeBox)}`, no image-containment) — the polynomial interior/clean charts keep
-- `image_subset` untouched. The (1,2,1) atom `routeM121sm_box_diverges` is S2-FREE (divergence from the 1D
-- `abs_rpow_lintegral_Ioo_eq_top` first principle, NOT `monomial_rlct`). Banks the ∀M-smeared lift shape.
-- (Foundations CoreShearMP/ParamsReshapeMP already imported transitively.) RouteM121Smeared now also
-- carries the REUSABLE minAdm≥2 assembly `routeMCore_box_diverges_of_MPChart`'s radial sibling
-- `routeMCore_box_diverges_of_RadialMPChart` (φ=ψ∘R, ψ MP-embedding + R polynomial radial |det|=|u_p|^{minAdm−1};
-- WEIGHTED hsrc absorbs the radial Jacobian into the binding-axis divergence at c≥minAdm/2). 46/46 det-validated.
import DLNFibre.DLN.RLCT.Validate.RouteM121Smeared
-- SMEARED minAdm≥2 validate-small — (2,3,1) (minAdm=2). The radial-MP chart `φ=ψ∘R` instantiated: rate via
-- `P1_lam231` (the 2×2 shear cancellation `P₁·Λ₀=P₂` off the pole), MP factorization at Fin 9, weighted hsrc
-- (subBox231 bounded away from det P₁=0 + the pole). Atom `routeM231sm_box_diverges` S2-FREE (|u_p|^{minAdm−1−2c'}
-- over (0,δ), exp ≤ −1 ⟺ c≥minAdm/2=1, via the 1D abs_rpow first principle). Exercises the radial leg.
import DLNFibre.DLN.RLCT.Validate.RouteM231Smeared
-- SMEARED minAdm≥2 validate-small — (1,3,2) (minAdm=2), the THIRD (r,c) family shape (1,2): scalar Gram
-- (`lam132=[u1/u0,u2/u0]`, NO matrix inverse, the (1,2,1) pattern) + multi-column radial (the (2,3,1) pattern,
-- `R132=pivotBlowupOn{3,4}`, `|det|=|u3|¹`). Atom `routeM132sm_box_diverges` via the reusable RadialMPChart,
-- S2-FREE. The 46 smeared M reduce to exactly 3 (r,c) families (all r·c≤2) — (1,1)/(2,1)/(1,2) — now all
-- templated: RouteM121Smeared/RouteM231Smeared/RouteM132Smeared. ∀M-smeared lift = parametrize each family.
import DLNFibre.DLN.RLCT.Validate.RouteM132Smeared
import DLNFibre.DLN.RLCT.Foundations.S1RadialMorse
import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteM4422Hfin
-- R1 (3,3,3,3) achiever box-divergence anchor — the decisive multi-pivot L=3 node; the THIRD
-- concrete R1 instance (det/cov/atom on the RouteM3333 chart). The det/cov/injOn lemmas are S2-free;
-- the atom matches the (4,4,2,2)/(3,3,4) siblings (cites `monomial_rlct`, the S2 divergence leaf).
import DLNFibre.DLN.RLCT.Validate.RouteM3333
import DLNFibre.DLN.RLCT.Validate.RouteM3333Atom
-- R1-general achiever ENGINES (toward the (A) general lower-atom). Two reusable, axiom-clean pieces:
-- the composed-det telescoping (`general_composed_clm_abs_det` — the variable-length Jacobian det via
-- the det monoid-hom, promoted from the spike) + the chained-product telescope
-- (`Chain.chain_telescope`, the algebraic heart of the chart identity `prod M (φ_M u) = u·H`).
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverTelescope
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverGeneralDet
-- Reusable bricks toward the `suffix 0 = prod M A` bridge (`reindex_finCongr_mul` cast-killer, `Mtail`/
-- `Atail`), then the `prod` front-peel `prod M A = A_0 · (reindex)(prod (Mtail M)(Atail M A))` (the
-- deferred-twice `prodAux` reassociation XL-cast, CRACKED + axiom-clean; `prodAux_succ` now lives in
-- `Foundations/Loss`, so this no longer pulls the `Deepest*` clash), then the chain↔DLN-product bridge
-- `Chain.suffix 0 = prod M A` (`RouteMSuffixBridge`). Shared with L2/D1's `endpoint_telescoping`.
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverBridge
import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSuffixBridge
-- R1-general achiever CHART (∀M): the abstract chain engine (`FactoredChain` + `step_of_factor` +
-- `chain_block` + `chainQ_mul_chainA` — M-agnostic block algebra) + the per-M achiever chain `chainOfMt`
-- (a structural recursion over opaque `t`-widths) → the ∀M chart identity `routeMCore_phiGen : F∘φ = u²·V`
-- (path-agnostic rate), validated to specialize to (3,3,3,3). Sorry-free + axiom-clean.
import DLNFibre.DLN.RLCT.Validate.RouteMChainFactor
import DLNFibre.DLN.RLCT.Validate.RouteMChainBlock
import DLNFibre.DLN.RLCT.Validate.RouteMChainBlockValid
import DLNFibre.DLN.RLCT.Validate.RouteMFactoredChain
import DLNFibre.DLN.RLCT.Validate.RouteMChainRate
import DLNFibre.DLN.RLCT.Validate.RouteMChainRateValid
import DLNFibre.DLN.RLCT.Validate.RouteMGenChain
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId3333
-- The det-INDEPENDENT `NodeAchieverChart M` fields ∀M from the rate identity: `leaf_integrand_of_rate`
-- (the leaf-integrand field, pure algebra in `F∘φ = u_p²·V`, no determinant) + `VvalGen_nonneg` (the unit
-- `V = ‖Hr‖²` ≥ 0). Isolates the atom's residual to the achiever-`t` Jacobian det + cov + a.e.-positivity.
import DLNFibre.DLN.RLCT.Validate.RouteMGenLeafIntegrand
-- Phase A of the general achiever Jacobian det (network-free, pure matrix algebra): the parametric
-- Schur-frame det `schurFrame_abs_det : |det DS| = |det K|^{r+c}` (via an abstract `lowerTri` block-
-- triangular nest — the `frameB`-free replacement for the (3,3,3,3) hand det), + the A1 `det_mulLeft/Right`
-- blocks. Validated to reproduce `Frame3333Deriv_det`'s K-blocks. The det-engine keystone for the ∀M atom.
import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet
-- Phase B (toward the ∀M achiever atom): the general flat-frame chart `chartParamsFlat := chartParamsGen ∘
-- genBlkFlat` with the ∀M general C1 keystone `chartParamsFlat_eq_chartParamsGen` (definitional `rfl`) —
-- so `routeMCore_chartParamsFlat = u²·V` (the RATE side complete ∀M) — + the opaque-width chain↔frame
-- entry-law bricks (`chainA/Q_apply_castAdd/natAdd`, `chainUnit_det`) bridging the abstract chart to the
-- Phase-A Schur/LDU factors. (`phiFlat_abs_det` — the det telescope — is the next multi-pass build.)
import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatChart
-- The B3 prefix-fold det SPINE (the det algebra fully assembled): `ChartFactor` + `composeFold`
-- (chain rule folded over a factor list, with the prefix-evaluation `Frame3333Deriv (Kparam3333 u)`
-- pattern) + `composeFold_abs_det` (the det telescope via `general_composed_clm_abs_det`). Consumes the
-- per-factor dets (Schur/LDU/chain/radial). `phiFlat_abs_det` (the opaque-width chart reconciliation) is next.
import DLNFibre.DLN.RLCT.Validate.RouteMChartFactorFold
-- Item-1 of the ∀M achiever Jacobian det: the det-ready bijective coordinatization. `RouteMChartIdxCard`
-- (the per-role cardinality bricks) + `RouteMChartIdx` (`chartDim_eq_flatDim` — the chart-coord count
-- = `flatDim M`, ∀M) + `RouteMChartIdxEquiv` (`chartIdxEquiv : Fin (routeMAmbient M) ≃ ChartIdx M t`).
-- + `RouteMRadialFactor` (the radial `ChartFactor` + its det `|u_p|^{card−1}`, item-2 first factor).
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction
import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxCard
import DLNFibre.DLN.RLCT.Validate.RouteMChartIdx
import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxEquiv
import DLNFibre.DLN.RLCT.Validate.RouteMRadialFactor
-- Item-2 of the ∀M achiever Jacobian det (the factor conjugates, DONE ∀M) + the item-3 slot-reader
-- foundation: `RouteMConjBlock` (det-preserving block conjugation), `RouteMFactorFDeriv`
-- (`HasFDerivAt.matMul`), `RouteMFactorMaps` (the Schur/LDU/chain `ChartFactor` conjugates + dets),
-- `RouteMChartSlots` (the DISJOINT role-slot reader API on `chartIdxEquiv`), `RouteMPhiFlatDet`
-- (`phiFlat_abs_det_of_factored` — the det telescope, conditional on the item-3 map equality + leafH).
import DLNFibre.DLN.RLCT.Validate.RouteMConjBlock
import DLNFibre.DLN.RLCT.Validate.RouteMFactorFDeriv
import DLNFibre.DLN.RLCT.Validate.RouteMFactorMaps
import DLNFibre.DLN.RLCT.Validate.RouteMChartSlots
-- `RouteMGenFlatStruct`: the STRUCTURED disjoint-slot decoder `genBlkFlatStruct`
-- (derived Schur-frame blocks), the identity boundary `C0_eq_one`, and the
-- UNCONDITIONAL rate `routeMCore (phiFlatStruct u) = u²·V` ∀M (`routeMCore_phiFlatStruct`).
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct
import DLNFibre.DLN.RLCT.Validate.RouteMPhiFlatDet
-- The general-M achiever chart, RATE side ∀M + the bridge bricks (thread 36):
-- `RouteMFlatStructV` — the vector chart `phiFlatStructV` + the RATE ∀M with NO bridge
-- (`routeMCore_phiFlatStructV : routeMCore M (phiFlatStructV x) = (x p)²·U`); `RouteMPhiTargetDet`
-- (`phiTarget_abs_det_of_factored`, det for ANY target given `composeFold fs = φ`); `RouteMCLEConj`
-- (`composeFold_eq_cleConj_foldr` — the OPTION-1 collapse to a Params-level `funext s`);
-- `RouteMLinearFactor` / `RouteMChainVar` (the reusable + variable-N chain factor bricks, det 1);
-- `RouteM4422Bridge` (validate-small: the (4,4,2,2) chart AS a fold, det via the generic machinery).
import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV
import DLNFibre.DLN.RLCT.Validate.RouteMPhiTargetDet
import DLNFibre.DLN.RLCT.Validate.RouteMCLEConj
import DLNFibre.DLN.RLCT.Validate.RouteMLinearFactor
import DLNFibre.DLN.RLCT.Validate.RouteMChainVar
import DLNFibre.DLN.RLCT.Validate.RouteM4422Bridge
-- Brick (a) of the coordinate-alignment bridge (ARCH-1): the single collapse CLE
-- `bridgeCLE M := (paramsEquivFlatCLE M).symm` absorbs the chartIdxEquiv-slot ↔ Params
-- alignment by CLE CANCELLATION (`genBlkParamsStruct_bridgeCLE`), reducing the bridge to a
-- Params-level `funext s` (`composeFold_bridge_eq`). `RouteM222StructAdm` — the LAYERED
-- validate-small anchor ((2,2,2), t=(2,1,1)); `RouteMRoleCLE` — the per-role Params-split CLE engine.
import DLNFibre.DLN.RLCT.Validate.RouteM222StructAdm
import DLNFibre.DLN.RLCT.Validate.RouteMBridgeCLE
import DLNFibre.DLN.RLCT.Validate.RouteMRoleCLE
-- Axiom-hygiene check: emits `#print axioms` for the load-bearing results on every build.
import DLNFibre.DLN.RLCT.AxCheck
