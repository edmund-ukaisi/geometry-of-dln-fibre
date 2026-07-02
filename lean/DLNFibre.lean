-- DLNFibre — single-writer aggregator. Add new module imports at the end; do not reorder existing
-- imports. Core = the network-free engine; DLN = the application (depends on Core).
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
import DLNFibre.Core.Dimension.Basic
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.Dimension.Catenary
import DLNFibre.Core.Dimension.AffineDomain
import DLNFibre.Core.Dimension.Codimension
import DLNFibre.Core.Dimension.Smooth
import DLNFibre.Core.Dimension.Regular
import DLNFibre.Core.PolynomialDimension
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.PolynomialCurveLimit
import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.BoxMoveDegeneration
import DLNFibre.Core.RankLocusClosed
import DLNFibre.Core.BoxMoveGeneral
import DLNFibre.Core.BoxMoveGeneration
import DLNFibre.Core.OrbitClosure
import DLNFibre.Core.OrbitPullbackDim
import DLNFibre.Core.OrbitSmooth
import DLNFibre.Core.AffineNoetherRank
import DLNFibre.Core.RingTheory.Kaehler.GenericRank
import DLNFibre.Core.Dimension.Trdeg
import DLNFibre.Core.OrbitImageDim
import DLNFibre.Core.OrbitDifferential
import DLNFibre.Core.LinearAlgebra.BaseChange
import DLNFibre.Core.RingTheory.Derivation.Matrix
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
import DLNFibre.DLN.Aoyagi.BlockElimination
import DLNFibre.DLN.Aoyagi.ProductReduction
import DLNFibre.DLN.Aoyagi.EntryIdeal
import DLNFibre.DLN.Aoyagi.ThroughLayerBasis
import DLNFibre.DLN.Aoyagi.ThroughLayerMatrix
import DLNFibre.DLN.Aoyagi.ChartTopology
import DLNFibre.DLN.Aoyagi.ProductReductionStepJacobian
import DLNFibre.DLN.Aoyagi.ProductReductionStepDerivative
import DLNFibre.DLN.Aoyagi.BasepointCertificate
import DLNFibre.DLN.Aoyagi.FixedBasepointChart
import DLNFibre.DLN.Aoyagi.ProductReductionBoundary
import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
import DLNFibre.DLN.Aoyagi.MatrixChain
import DLNFibre.DLN.Aoyagi.ArithmeticTail
import DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic
import DLNFibre.DLN.Aoyagi.Lemma4CountArithmetic
import DLNFibre.DLN.Aoyagi.HtildeChainArithmetic
import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily
import DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
import DLNFibre.DLN.Aoyagi.Lemma5TerminalSourceBridge
import DLNFibre.DLN.Aoyagi.Lemma5Eq5CountDatumBridge
import DLNFibre.DLN.Aoyagi.Lemma5Eq5EndpointProfile
import DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalClassifier
import DLNFibre.DLN.Aoyagi.Lemma5Eq5SuppliedCoverage
import DLNFibre.DLN.Aoyagi.FinalFormula
import DLNFibre.DLN.Aoyagi.Definition3Bridge
import DLNFibre.DLN.Aoyagi.Definition3RankWidthBridge
import DLNFibre.DLN.Aoyagi.NormalCrossingInterface
import DLNFibre.DLN.Aoyagi.Theorem2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Theorem2FinalAssembly
import DLNFibre.DLN.Aoyagi.Lemma5TerminalOrderBridge
import DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
import DLNFibre.DLN.Aoyagi.Case2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Case2Theorem2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Case2Theorem2ChartFinalBridge
import DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasFinalBridge
import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasCase2FinalBridge
import DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Case1Theorem2FiniteExponentBridge
import DLNFibre.DLN.Aoyagi.Case1Theorem2ChartFinalBridge
import DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
import DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderBridge
import DLNFibre.DLN.Aoyagi.Lemma5Eq5TerminalOrderDefinition3Bridge
import DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderEqualityBridge
import DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge
import DLNFibre.DLN.Aoyagi.Theorem2SourceRankFinalBridge
import DLNFibre.DLN.Aoyagi.Theorem2SourceRankEq5Bridge
import DLNFibre.DLN.Aoyagi.RegularVariableShift
import DLNFibre.DLN.Aoyagi.Theorem2RankWidthRegularShiftBridge
import DLNFibre.DLN.Aoyagi.Theorem2SourceRankRegularShiftBridge
import DLNFibre.DLN.Aoyagi.RegularSuspensionInterface
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.Case2ResidualIndex
import DLNFibre.DLN.Aoyagi.RegularSuspensionAlgebraicSource
import DLNFibre.DLN.Aoyagi.Theorem2RegularSuspensionFinalBridge
import DLNFibre.DLN.Aoyagi.RegularSuspensionIntegrability
import DLNFibre.DLN.Aoyagi.MonomialChartIntegrability
import DLNFibre.DLN.Aoyagi.RegularSuspensionSquareSumIntegrability
import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
import DLNFibre.DLN.Aoyagi.ChainMapTupleBridge
import DLNFibre.DLN.Aoyagi.ChainMapLossBridge
import DLNFibre.DLN.Aoyagi.EndpointLossComparison
import DLNFibre.DLN.Aoyagi.OriginalLossSourceMeasure
import DLNFibre.DLN.Aoyagi.OriginalLossLocalMeasure
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxMeasure
import DLNFibre.DLN.Aoyagi.Case2ResidualSelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
import DLNFibre.DLN.Aoyagi.SelectedEntryOriginalLossLocalMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
-- Determinantal-stratum dimension (fibre-codim AG build, rung 1): dim Mat^{rk≤r}_{m×n} = r(n+m−r),
-- via the N=1 specialisation of the quiver engine (productRankLocusLE ![n,m] r = the determinantal
-- variety).
import DLNFibre.Core.DeterminantalStratumDim
-- Generic tuple over the coordinate ring (shared, CommRing): genericTuple + eval_genericTuple,
-- reused by RankLocusClosed (minor polys) and MultComorphism (the coordinate-ring map of mult).
import DLNFibre.Core.GenericTuple
-- Comorphism keystone (fibre-codim AG build, F1): the coordinate-ring map of `mult` (generic
-- product entries multPoly = mult over MvPolynomial), the bridge eval_multPoly, the fibre as a
-- zero-locus, and fibreGenIdeal = Ideal.map multComap (maxIdealOfPoint B) — the fibre-ring quotient
-- F2 consumes.
import DLNFibre.Core.MultComorphism
-- Fibre-codim LOWER bound (partial Lemma 4.6): codimRepCanonical Σ̄^r ≤ codimRepCanonical (mult⁻¹
-- B) from mult⁻¹B ⊆ Σ̄^r. The +r(d_0+d_N−r) shift (the full identity) is now PROVED in
-- FibreCodimFinal (route-β chart build); this module supplies the lower-bound half it anticipated.
import DLNFibre.Core.FibreCodim
-- Fibre-codim G1 (rank-chart build): same rank ⟹ same fibre codim (N≥1), via the GL×GL end-factor
-- action + mult-equivariance + height-comap codim-invariance + rank normal form. Reduces Lemma 4.6
-- to a single normal-form fibre.
import DLNFibre.Core.FibreNormalForm
-- Bordered Schur minor (G2-2 sub-rung 1): det [[Δ,u],[v,d]] = d·detΔ − v·adjΔ·u over ANY CommRing
-- (universal-coefficient route, no invertible pivot), and the Schur expression = an (r+1)-minor ⟹
-- vanishes on Mat^{rk≤r}. The generator-free handle for the localized base presentation (dodges
-- determinantal-ideal theory, absent at v4.29).
import DLNFibre.Core.DeterminantalChartRing
-- ker of a multivariate aeval = the graph ideal (reusable, arbitrary index type), + the elimination
-- quotient equiv + graph-ideal primality. The generator-free elimination engine (G2-2).
import DLNFibre.Core.MvPolynomial.GraphIdeal
-- Height of a block graph ideal over a field = #eliminated vars (catenary). The `height J = C`
-- engine (G2-2).
import DLNFibre.Core.MvPolynomial.GraphIdealHeight
-- Reindex + detΔ-localization bridge for the determinantal base: repCoordReindex, blockAlgEquiv
-- (A_eng ≃ MvPolynomial B22block (MvPolynomial SchurVar k)), blockAlgEquiv_detPivot (detΔ ↦ C
-- detSchurS). The reindex/detΔ infra feeding the final localized-base presentation (G2-2 D2).
import DLNFibre.Core.DeterminantalBaseElimination
-- G2-2 COMPLETE: the localized base presentation `basePresentationEquiv : A_loc/Iad ≅ₐ[k] Sd` (free
-- Schur localization, regular dim δ), via the bordered-minor identity (*) + the height squeeze Iad
-- = J (earned honestly, not assumed). Feeds G2-3 (the total presentation + flatness).
import DLNFibre.Core.DeterminantalBasePresentation
-- Route-(b) reducedness chain for G2-3 (R2-3a): the tensor-with-a-field reducedness descent
-- (PROVED), CONDITIONAL on a deep product iso `e : S ≃ₐ[k] R ⊗ F_B` + `IsReduced S`. SUPERSEDED:
-- codim=C+δ was instead closed by the route-β localized chart AlgEquiv (ChartLocalizedAlgEquiv) +
-- FibreCodimFinal; this conditional R2-3b chain is off the critical path (retained as record).
import DLNFibre.Core.FibreReducedTrivialization
-- Deep chart ring (R2-3b-1+2, an early R2-3b-route module): `Sred = Localization.Away(ΔPdeep) ⧸
-- IadDeep` for general d (the engine's base presentation is N=1 only), the
-- RepCoord↔stratum/endpoint bridges, and the localized base→total map `schurToSred : SchurLoc →
-- Sred` giving Sred its SchurLoc-algebra structure (R2-3a's R = SchurLoc, S = Sred). The crux
-- containments (det transport, base→deep sigmaIdeal, NON-circular) proved. OFF the critical path:
-- route-β (ChartLocalizedAlgEquiv) built `e` instead; a self-contained component of the superseded
-- R2-3b route.
import DLNFibre.Core.DeepChartRing
-- Endpoint-normalization gauge AlgEquiv (R2-3b-3): the vertex-unit conjugation `Aᵢ ↦
-- P_{i+1}·Aᵢ·P_i⁻¹` (= landed `BaseChange.baseChange`) on the generic tuple, `gaugeEquiv d P`, over
-- arbitrary CommRing R, + the transport `gaugeEquiv (multPoly) = P_last·M·P_0⁻¹` (endpoint gauge
-- P_0=H, P_last=L⁻¹ ⟹ L⁻¹·M·H⁻¹). The coordinate change `mult(A)=LEH` ↦ `mult(Ã)=E`. Its
-- `gaugeEquiv` is reused by route-β's seams.
import DLNFibre.Core.EndpointNormalization
-- HEIGHT-DIRECT route, rung H1 (radical-insensitive retarget): `Ideal.height_radical`
-- (height(radical I) = height I, no hypotheses) + `codimRepCanonical_fibre_eq_height_fibreGenIdeal`
-- (codim of the fibre = height of the cut ideal, [IsAlgClosed k] only — NO radicality). Decouples
-- the codim from the (off-path) radicality wall: the RLCT payoff needs only this height.
import DLNFibre.Core.FibreHeightDirect
-- HEIGHT-DIRECT rung H2 (the differential of mult): `multSuffix` (suffix product, mirror of
-- multPrefix) + `pderiv_multPoly`/`eval_pderiv_multPoly` — d(mult) entry = (suffix column
-- s)·(prefix row t), the rank-one outer product per factor. The Jacobian-entry brick H3 (generic
-- Jacobian rank) consumes.
import DLNFibre.Core.MultDifferential
-- HEIGHT-DIRECT rung H3a (assemble the fibre Jacobian):
-- `fibreGen`/`fibreJacobianMatrix`/`fibreJacobian` (entry = eval_pderiv_multPoly =
-- multSuffix·multPrefix), the UNCONDITIONAL tangent = ker(Jacobian) identity
-- (`finrank_cotangentSpace_fibre_eq_finrank_ker`) + the card-rank reading
-- (`finrank_ker_add_rank_fibreJacobianMatrix`: finrank ker + rank = card). H3b supplies rank = C+δ
-- at a generic point; H3c supplies generic smoothness ⟹ ker finrank = local fibre dim.
import DLNFibre.Core.FibreJacobian
-- Route-c sweep structure (homogeneous sweep): `Σ^r = H·F`
-- (`productRankLocus_eq_iUnion_smul_fibre`) via `mult_smul` + `exists_baseChange_of_rank_eq`; every
-- translate same codim (G1). The reachable part of the bundle-shift; the sweep dim-identity `dim
-- Σ^r = δ + dim F` (hSweep) is the residual (= the generic-freeness build, thread 29).
import DLNFibre.Core.EndBaseChangeSweep
-- Reducible-locus catenary: `height I + ringKrullDim(R⧸I) = card` for ANY proper I (no radicality),
-- and `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of
-- RouteCAssembly.
import DLNFibre.Core.RadicalCatenary
-- H5 per-component→codim closer (reusable): `height_eq_of_minimalPrimes_bounds` (height I = v from
-- the per-minimal-prime bounds) + the codim retarget at v = C+δ + G1-transport (one rank-r witness
-- ⟹ all B). NOTE: parallel route-B (minimal-primes) CONDITIONAL bank, superseded by the
-- unconditional FibreCodimFinal route; retained (honestly named `…_of_height_bounds`), not on the
-- critical path.
import DLNFibre.Core.FibreCodimMinPrimes
-- Route-c assembly (conditional bank): `codimRepCanonical(fibre d B) = C + δ` for rank-r B,
-- carrying the sweep dim-identity `hSweep` + the density `hClosure` as named hypotheses (both since
-- discharged in-repo: hSweep in FibreCodimFinal, hClosure in ClosureBridge); catenary hyps via
-- RadicalCatenary.
import DLNFibre.Core.RouteCAssembly
-- (b)-build rung 1 — generic freeness (Grothendieck's lemma, MODULE case): a f.g. module over a
-- (Noetherian) domain is free/flat after inverting one nonzero element (via the Mathlib substrate
-- `exists_free_localizedModule_powers` + FractionRing-is-a-field). Reusable general lemma + a
-- stepping stone for the finite-type-ALGEBRA case (EGA IV 6.9.1, the positive-relative-dim case the
-- fibre needs).
import DLNFibre.Core.GenericFreeness
-- (b)-build route-c foundation: `VarietyDimRadical` — the non-circularity SHIELD
-- `ringKrullDim_quotient_radical` (Krull dim radical-insensitive ⟹ the varietyDim build never
-- re-enters the R2-3b-4 reducedness circularity) + `varietyDim_eq_of_coordRingAlgEquiv` (transport
-- varietyDim across a coordinate-ring AlgEquiv). `SchurGauge` — the Schur pivot block is a
-- SchurLoc-unit (det = the inverted detSchurS), the unit the gauge L/H blocks use.
import DLNFibre.Core.VarietyDimRadical
import DLNFibre.Core.SchurGauge
-- (b)-build route-c: generator-free varietyDim transport. `varietyDim_baseChange_image` (varietyDim
-- invariant under the GL×GL base-change image, no determinantal-ideal theorem) +
-- `varietyDim_fibre_endpoint_conj_eq` (constant fibre dim along the endpoint orbit).
import DLNFibre.Core.VarietyDimBaseChange
-- hClosure PROVED (thread-32 codim sandwich, zero-cite): varietyDim Σ^r = varietyDim Σ̄^r via codim
-- Σ^r = codim Σ̄^r = C (irreducibility-free catenary + ONE corner-r witness orbit), wired into
-- RouteCAssembly so codim(fibre)=C+δ now carries ONLY hSweep.
import DLNFibre.Core.ClosureBridge
-- hSweep build (chart-trivialization): general matrix-rank helpers (diag(I_r,0) rank; rank=0 iff 0;
-- block-diagonal rank-additivity).
import DLNFibre.Core.RankNormalFormDim
-- rung-3 +δ: varietyDim W = varietyDim F + card ι from a coordinate-ring AlgEquiv (domain-free).
import DLNFibre.Core.VarietyDimPolyExtension
-- rung-2a chart normalization: L⁻¹·M·H⁻¹ = diag(I_r,0) over k + factor_chart_matrix (L·E·H = M).
import DLNFibre.Core.ChartSection
-- rung-2b tuple retraction: chartGauge(mult A)•A ∈ fibre E — the regular φ→F via mult_smul.
import DLNFibre.Core.ChartRetraction
-- rung-2 set-level chart bijection Σ^r∩U_Δ ≅ base × F, both directions (round-trip).
import DLNFibre.Core.ChartBijection
-- step-3a: gauge-conjugation transport at endpointGauge over SchurLoc
-- (gaugeEquiv(endpointGauge)(multPoly) = L⁻¹·multPoly·H⁻¹).
import DLNFibre.Core.ChartGaugeNormalize
-- no-drop machinery (shared by step-4/5) re-homed to Core.Dimension.Localization (P1-R3):
-- affine-domain dim(D[1/g])=dim D + the abstract no-drop dim(R[1/g])=dim R when g avoids a top
-- prime of a reducible Noetherian R.
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
-- THE CENTRAL RESULT: codim(fibre d B) = C + δ = cCodim + r·(d_N+d_0−r), unconditional (k : Type
-- 0).
import DLNFibre.Core.FibreCodimFinal
-- THE PAYOFF (destination): BundleShiftInterface discharged from Core — rlct(K^DLN_B)=(C+δ)/2 rests
-- on the thin honest RlctRealInterface: 2 named atomic Cited facts (Watanabe ≤, Aoyagi ≥); the
-- real↔complex transfer T is now PROVED (codimRealFibre_eq_codimRepCanonical_baseChange — both
-- sides = field-indep C+δ), as are the connector, the catenary reduction, and codim_K=C (k : Type
-- 0). [#52/G4, capstone]
import DLNFibre.DLN.BundleShiftDischarge
-- Source-shaped Aoyagi formula surface: her λ formula, with cValue/codim bridge stubs.
import DLNFibre.DLN.Aoyagi.ClosedForm
-- θ-components (Route-A fibre entry): detΔ ≡ 1 on the fibre ⟹ localizing O(fibre) at detΔ is an iso
-- (reducedness-free); + the shifted count numTop d r = cTheta(d−r) = C(m,|δ|).
import DLNFibre.Core.FibreDetUnit
import DLNFibre.Core.CThetaShiftCount
-- θ-components (fibre-count transport, thread 06): the TopDimMinPrimes framework (core +
-- general transport rungs in `Core.MinimalPrime.*`, appended below) + the Σ̄^r / fibre count
-- endpoints.
import DLNFibre.Core.TopComponentsTopDim
import DLNFibre.Core.FibreTopDimDetUnit
-- θ-components (fibre-count wiring, thread 08): the chart-e count carry and the W2 avoidance (the
-- general localization-survival / radical-insensitivity rungs live in `Core.MinimalPrime.*`).
import DLNFibre.Core.TopDimMinPrimesChartE
import DLNFibre.Core.TopDimMinPrimesGfibAvoid
-- θ-components (W0 indexing bridge): TopDimMinPrimes(O(Σ̄^r)) = TopDimMinPrimes(O(Σ^r)) (closed ≤r
-- ↔ exact =r at the top-dim minimal-prime level), via unconditional recovery + corner-monotonicity.
import DLNFibre.Core.TopDimMinPrimesW0
-- θ-components (count composition): W1 survival + avoidances, the W2 survival, and the headline
-- numTop(fibre d E_r) = cTheta(d−r) composing the count chain (the `_of` form; hW2 supplied by W2).
import DLNFibre.Core.TopDimMinPrimesW1W2
import DLNFibre.Core.TopDimMinPrimesW2
import DLNFibre.Core.FibreThetaCount
-- Scope-3 (Tier-R bundle, thread 11): the reduced-fibre product trivialization — the reusable B1
-- tensor-package `Away (map f) ≃ₐ Away f ⊗ F`, its chart specializations, rank-r base-change
-- homogeneity, and the single-chart triviality headline (on the REDUCED variety, not the scheme
-- cut; a full per-minor open cover is NOT built — see the module's B3 disclaimer).
import DLNFibre.Core.FibreBundleReduced
-- Scope-3 (smoothness rungs S2+S3, thread 15): the reusable, reducedness-free submersive plumbing —
-- a chart where a chosen `(C+δ)`-square Jacobian minor is a unit is `Smooth k` (and standard-smooth
-- of relative dimension `n − c`), via Mathlib `SubmersivePresentation → IsStandardSmooth → Smooth`,
-- with `…of_algEquiv…` transport hooks the θ-chart atlas consumes. Conditional on the minor-unit
-- input (discharged by the rank=C+δ tide), NOT a fibre-is-smooth claim.
import DLNFibre.Core.FibreSmoothPlumbing
-- Scope-3 (generic smoothness, thread 16): reusable unconditional bricks — `Smooth (A ⊗ B)`,
-- `SchurLoc` smooth, the basic-open `IsSmoothAt` bridge — plus the CONDITIONAL headline: given
-- `IsSmoothAt` of the reduced-fibre factor at a top-component generic prime (= thread-14 fact (C),
-- NOT discharged), the chart product `SchurLoc ⊗ Away g` is `Smooth k`. The fibre is reducible for
-- θ≥2, so the honest object is `IsSmoothAt` (generic), never a global `Smooth k`.
import DLNFibre.Core.FibreGenericSmooth
-- P1.c (det-atlas): rank strata + the pivot-minor cover + the ideal↔rank-locus connective. Bare
-- `Matrix` namespace (Mathlib-mirror, L7). Re-homed verbatim from `RankMinorCover`: `rankEqLocus`
-- (rank-`= r` open), `minorChart`, the keystone `exists_invertible_minor_of_rank` (a rank-`r`
-- matrix has some invertible `r×r` minor — a Mathlib v4.29 gap), and the cover theorem
-- `rankEqLocus_subset_iUnion_minorChart`. NEW: `rankLeLocus` (rank-`≤ r` closed) + the connective
-- `rankLeLocus_eq_vanishingLocus` / `mem_rankLeLocus_iff_determinantalIdeal_le_ker` tying the
-- closed locus to the vanishing locus of `determinantalIdeal (r+1)` (P1.b), at the field level.
import DLNFibre.Core.RingTheory.Determinantal.Strata
import DLNFibre.Core.FibreBundlePerMinor
-- P1.a (det-atlas): the abstract transition cocycle for a principal-open cover of `Spec R` over an
-- arbitrary `CommRing R` — `awayOverlap`/`awayOverlapTransition` + the three pairwise cocycle laws,
-- the single-chart restriction (`chartToSwappedOverlap`), and the triple-overlap cocycle
-- `awayTriple_cocycle`, all via localization initiality. Network-free, bare `Localization` namespace
-- (Mathlib-mirror, L7). Re-homed verbatim from `FibreBundleTransition` §Abstract+§TripleOverlap.
import DLNFibre.Core.RingTheory.Localization.Overlap
-- P1.b (det-atlas): matrix coordinate ring + the determinantal `(r+1)`-minor ideal. The
-- minor-determinant polynomial `Matrix.detMinorPoly s t` (det of the `(s,t)` minor of the generic
-- matrix `Matrix.mvPolynomialX`; `eval_detMinorPoly` evaluates it to `(M.submatrix s t).det`,
-- re-homed verbatim from `FibreBundleTransition` §MinorChart, generalized `Field → CommRing`), and the
-- genuinely-new (absent-in-Mathlib) `Matrix.determinantalIdeal p q R N` — the ideal generated by all
-- order-`N` minors, whose vanishing locus is rank `< N`. Bare `Matrix` namespace (Mathlib-mirror, L7).
import DLNFibre.Core.RingTheory.Determinantal.Basic
-- P1.d (det-atlas): Schur-complement coordinates on the pivot rank chart. Block-diagonal rank
-- additivity `Matrix.rank_fromBlocks_zero` (general index, absent in Mathlib v4.29), the pivot
-- Schur rank criterion `rank_fromBlocks_eq_card_iff_schur{,_inv}` + the `Fin`-indexed
-- chart-membership iffs `rank_le_iff_schur_eq` / `rank_eq_iff_schur_eq` (via
-- `rank_fromBlocks_invertible₁₁`), the explicit chart parametrization
-- `pivotRankChart`/`pivotRankChartEquiv` (Mat^{rk=r}∩U ≅ GL_r×Mat×Mat, `finrank = δ`), and the
-- `CommRing` normal form `schurComplement_normal_form`. Bare `Matrix` namespace (Mathlib-mirror,
-- L7). Re-homed from `DeterminantalChart`/`SchurChartIff` (deleted) + `SchurGauge`'s normal form;
-- aligns with `Strata`'s `minorChart`/`rankEqLocus`.
import DLNFibre.Core.RingTheory.Determinantal.Schur
-- P1.e (det-atlas, rank-stratum dimension/codim): the closed-form rank-stratum dimension
-- `rankStratumDim r p q = r(p+q−r)` and codimension `rankStratumCodim r p q = (p−r)(q−r)` with the
-- "codim + dim = ambient `p·q`" identity (pure `Nat`), plus the anchoring of `rankStratumDim` to
-- the pivot-chart parameter-space `finrank` (`finrank_pivotRankChart_params_eq_rankStratumDim`). Bare
-- `Matrix` namespace (Mathlib-mirror, L7); the matrix-general dimension content only. The GEOMETRIC
-- statement that `Σ̄^r` has this variety dimension is Proved (not cited) in
-- `Core.DeterminantalStratumDim`, via the Proved zero-cited Brick A (`Core.SigmaCodim`); this file
-- supplies only the arithmetic those theorems consume.
import DLNFibre.Core.RingTheory.Determinantal.Dimension
-- P2.a (Phase 2): the abstract pivot-chart atlas datum + standard fibre model
-- (`Algebra.StandardFibreChart`, bare `Algebra` ns); the DLN bundle instantiates it. Direct import
-- (was transitive-only via `FibreBundleHeadline`).
import DLNFibre.Core.RingTheory.Determinantal.Atlas
-- Scope-3 (bundle transition cocycle, thread 19): the per-minor instantiation — the per-minor
-- principal-open overlaps `D(f)∩D(g)` of `Mat^{=r}` with their `minorChartTransition` (= the
-- abstract `Localization.awayOverlapTransition` at the two minor polynomials). DISCLAIMER: this
-- cocycle is on the AMBIENT `O(Mat)` cover — NOT yet bridged to the deep Schur chart `e_β`, so the
-- bundle is NOT `locallyTrivial`.
-- (Now LANDED — per-pivot Schur trivializations (S4b) + target-side cocycle (P2.c/f/g): the
-- family IS Zariski-locally-trivial (`IsZariskiLocallyTrivialAffineProduct`); only the
-- GLOBAL `Flat π` stays R1. Above = period-accurate provenance for this module's own content.)
import DLNFibre.Core.FibreBundleTransition
-- Scope-3 (fact-C unconditional, thread 17): generic smoothness reduced to ONE named geometric
-- fact. C1 `LocalizationAtComponent` — reusable CA: localizing a reduced Noetherian ring at a prime
-- meeting one minimal prime recovers that component's local ring (sub-walls (a)+(b) of thread-16,
-- banked). C3 `FibreGenericSmoothUncond` — `S ⊗ Away g ≃ Away (1⊗g)` transport ⟹ `IsSmoothAt` of
-- the fibre chart from `IsSmoothAt` of `sweepFibreRing`. (The thread-17 C2(a) framing — "sole
-- remaining input" — is SUPERSEDED: smoothness is fully unconditional via
-- FibreComponentOrbitTransport's fp-domain route, no C2(a) needed; that bare-orbit iso was
-- dimensionally impossible. See FibreComponentOrbitTransport below.)
import DLNFibre.Core.LocalizationAtComponent
import DLNFibre.Core.FibreGenericSmoothUncond
-- Scope-3 (bundle bridge B3-4, thread 21): the genuine TOP-LEFT `e_β`↔ambient identification — the
-- seam `detMinorPoly_topLeft_rename`, the bridge AlgHom `topLeftBaseToChartAway` (identifies the
-- inverted denominators, load-bearing), and a genuinely-instantiated `LocalTrivializationDatum` at
-- the top-left chart (the real e_β+tensor composite). PARTIAL: this does NOT earn `locallyTrivial`
-- — the per-pivot trivialization `e_{s,t}` (the conjugation skeleton) + cocycle transport onto it
-- remain (#123).
-- (Both now LANDED — per-pivot trivialization (S4b) + target-side cocycle transport (P2.c/f/g): the
-- family IS Zariski-locally-trivial (`IsZariskiLocallyTrivialAffineProduct`); only the
-- GLOBAL `Flat π` stays R1. Above = period-accurate provenance for this module's own content.)
import DLNFibre.Core.FibreBundleLocallyTrivial
-- Scope-3 (C2(a) dimension finding + sigma labeling, thread 20): thread-17's bare iso
-- `sweepFibreRing⧸I ≃ orbitRing M` is DIMENSIONALLY IMPOSSIBLE (fibre component = orbit closure ×
-- Aᵟ, δ=r(d_last+d_0−r)>0), and the dimension-corrected `…_of_component_orbitPolyEquiv` shape is
-- ALSO globally false (thread 24) — both orbit-iso consumers are now `@[deprecated]` dead
-- scaffolding. The LIVE contribution is the UNCONDITIONAL sigma-side labeling
-- `exists_sigma_topComponent_orbitRingEquiv` (every top component of O(Σ̄^r) IS `orbitRing
-- (realizerD m)`). NB smoothness is fully unconditional WITHOUT any orbit iso — via the direct
-- fp-domain route in the next import (FibreComponentOrbitTransport), NOT modulo any fibre≅orbit
-- iso.
import DLNFibre.Core.FibreComponentOrbit
-- Scope-3 (smoothness FULLY UNCONDITIONAL, thread 20 #128): the orbit-iso detour proved UNNECESSARY
-- — a fibre top component `sweepFibreRing⧸I` is a finitely-presented DOMAIN over an alg-closed
-- field, hence generically smooth (`IsSmoothAt k ⊥`); the C1 bridge lifts that to `IsSmoothAt k I`.
-- Headlines `isSmoothAt_sweepFibre_topComponent` + `exists_isSmoothAt_chartDsig_unconditional`:
-- generic smoothness of the DLN fibre, NO open hypothesis remaining.
import DLNFibre.Core.FibreComponentOrbitTransport
-- Scope-3 (per-pivot conjugation skeleton, thread 22 #123): the endpoint-permutation gauge carries
-- the top-left deep chart `e_β` to a genuine `LocalTrivializationDatum` at EVERY pivot `(s,t)` of
-- the cover (the seam `gaugeEquiv_ΔPdeep_eq_ΔPdeepAt`, descent `gaugeEquivSigma`, per-pivot
-- `chartLocalizedAlgEquivAt`). PARTIAL: still NOT `locallyTrivial` — the cocycle transport ON the
-- per-pivot trivializations remains (#133).
-- (Now LANDED — that per-pivot cocycle transport is the target-side cocycle P2.c/f/g: the
-- family IS Zariski-locally-trivial (`IsZariskiLocallyTrivialAffineProduct`); only the
-- GLOBAL `Flat π` stays R1. Above = period-accurate provenance for this module's own content.)
import DLNFibre.Core.FibreChartConjugation
-- Scope-3 (per-pivot local-product atlas, thread 23 B3-6/7): the assembled atlas with PAIRWISE
-- base-side overlap data over the rank-`=r` open — scheme open-cover
-- (`iSup_pivot_basicOpen_eq_rankROpen`) + per-pivot trivializations into `SchurLoc ⊗
-- sweepFibreRing` + the base-side overlap transition (`chartOverlapTransition` over
-- `sweepSigmaRing`, pairwise laws) + the intertwining (`e_β` cancels → base-algebraic). Headline
-- `reducedFibre_pivotLocalProductAtlasOnRankOpen` — honestly NOT `locallyTrivial`: the rank-tie
-- `rankROpen={rank=r}` is now landed (S1, set-of-primes), the LOCAL target-side overlap cocycle is
-- landed (P2.c/f/g, below) and projection compatibility is CLOSED (R5), so the residual to a bare
-- scheme-theoretic name is the GLOBAL gluing of the per-chart data into one fibration morphism
-- (R1).
import DLNFibre.Core.FibreBundleLocallyTrivialFull
-- Scope-3 (variety-level fibre-component↔orbit iso, thread 24 #138): rung 1 of the honest LOCALIZED
-- `e` — `schurComponent_chartQuotientEquiv : SchurLoc ⊗ (sweepFibreRing⧸I) ≃ₐ[k] (Away
-- chartDsig)⧸chartComponentIdeal` (the chart-localization component transport). The consumer-shaped
-- global/shifted-orbit `e` is FALSE (chart is intrinsically localized); only the LOCALIZED
-- full-d-orbit form is reachable — the orbit descent (rung 2) is a precisely-costed residual, NOT
-- built. Off-critical-path geometric enrichment.
import DLNFibre.Core.FibreComponentOrbitIso
-- Review round 1 fix (owner PR #11, C3): the same-rank component-count transport — for ANY `B` with
-- `B.rank = r`, `numTop(mult⁻¹ B) = cTheta(d−r)` (arbitrary `B`, not just the normal form `E_r`):
-- `mult⁻¹ B` a `GL×GL` translate of `mult⁻¹ E_r` ⟹ iso ⟹ equal TopDimMinPrimes count, proved
-- directly via `exists_baseChange_of_rank_eq` + `image_smul_fibre` + `vanishingIdeal_image_smul` +
-- quotient-equiv + radical-insensitivity (NOT literally `reducedFibre_baseChangeHomogeneous`).
-- Closes the C3 overclaim.
import DLNFibre.Core.FibreThetaCountArbitrary
-- θ-invariants DISTINCTION capstone (PR #11 follow-up): the order-side companion to the
-- codim/Aoyagi capstone. `aoyagiPoleOrder ell a := a*(ell−a)+1` (an ANALYTIC pole order, NOT a
-- component count) — (1) the live mismatch `numTop_d22222_ne_aoyagiPoleOrder` (L&R count 6 ≠ 5 =
-- Aoyagi order at (2,2,2,2,2) r=0), (2) the agreement regime `choose_eq_aoyagiPoleOrder_iff :
-- choose ell a = a(ell−a)+1 ↔ min a (ell−a) ≤ 1`. Proves the two θ's DIFFER + pins exactly when
-- they agree; asserts NO (false) equality of them.
import DLNFibre.DLN.Aoyagi.ThetaOrderDistinction
-- Aoyagi p. 13 product-step weighted additive-Haar change-of-variables adapter.
import DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
-- Aoyagi p. 13 regular-coordinate tuple feeding the product-step inverse density handoff.
import DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
-- Aoyagi suffix-state product-step tuples feeding the inverse density handoff.
import DLNFibre.DLN.Aoyagi.ProductReductionStepSuffixDensity
import DLNFibre.DLN.Aoyagi.Lemma5FirstNonbaseOrderBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesMeasure
import DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant
import DLNFibre.DLN.Aoyagi.RetainedPassiveFormalLinearDeterminant
import DLNFibre.DLN.Aoyagi.RetainedPassiveFormalRawOrder
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian
-- fibration-geometry expedition (spine): S1 rank-bridge keystone + S2 smooth-block certificate.
-- `FibreRankBridge` — the prime/residue-field rank bridge `P ∈ rankROpen ↔ rank over κ(P) = r`,
-- closing the scheme-level set-of-primes identity `rankROpen = {rank = r}` (gates flatness + the
-- honest locallyTrivial). `FibreSmoothBlock` — the standard-smooth local model at a smooth closed
-- point of a top component: Ω free, `rank(Ω) + codim = ambient` (the RLCT-runway's first slab; the
-- Kähler/relative-dimension side, NOT the conormal rank-=-codim).
import DLNFibre.Core.FibreRankBridge
import DLNFibre.Core.FibreSmoothBlock
-- S4: honest per-chart local PRODUCT over the rank-=r open (`RankROpenPerPivotLocalProduct`,
-- `reducedFibre_existsProductChartAt_rankEq`). Folds in S1 to certify rankROpen genuinely IS the
-- residue-field rank-=r locus; the pivot charts cover it; each chart's localized ring is a
-- k-algebra product SchurLoc ⊗ sweepFibreRing. Deliberately NOT `locallyTrivial`:
-- per-chart (the LOCAL target-side overlap cocycle is landed, P2.c/f/g; only the GLOBAL gluing into
-- one fibration morphism = R1) and k-algebra-only (the over-base SchurLoc-linear trivialization =
-- S4b, LANDED below; it is over SchurLoc; projection-compatibility with mult is CLOSED (R5,
-- FibreProjectionCompat), the GLOBAL-gluing R1 is the remaining residual).
import DLNFibre.Core.FibreLocallyTrivial
-- S2c: closes S2's top-component residual — `topDimMinPrimes_nonempty` (generic: nontrivial
-- Noetherian ⟹ TopDimMinPrimes nonempty) → `exists_topComponent_smoothBlock_certificate`, the
-- smooth-block existence with NO `I, hI` hypotheses (hypothesis-free under the kostant gate).
import DLNFibre.Core.FibreSmoothBlockExists
-- S3: flatness facts around the atlas (HONEST scope — NOT the `Flat π` payoff).
-- `chartInclusion_flat` (localization), `standardFibreModel_free`/`_flat` over the auxiliary
-- SchurLoc (generic base change), scheme-level `flat_specMap_…` + `universallyOpen_specMap_…`. NB
-- S4b (below) DELIVERS the chartwise `Module.Flat SchurLoc (Away(chartDsigAt …))`; projection
-- compatibility (schurToDsigAt vs mult's projection) is now CLOSED (R5, FibreProjectionCompat);
-- what stays open is R1/global gluing — NOT S4b.
import DLNFibre.Core.FibreFlatness
-- S4b (the convergent keystone): the SchurLoc-linear (over-base) trivialization
-- `chartDsigAt_schurLocTensorEquiv : Away (chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗ sweepFibreRing`
-- (SchurLoc acting via the HONEST banked structure map schurToDsig, not by pullback) ⟹ chartwise
-- flatness over the in-chart base direction SchurLoc `chartDsigAt_flat_over_schurLoc` AND the
-- genuine over-base local triviality (S4's load-bearing completion). NB this is over SchurLoc;
-- projection-compatibility with the geometric `mult` projection is CLOSED (R5,
-- FibreProjectionCompat), so R1's global overlap gluing is the remaining open item toward a single
-- GLOBAL Flat π / FiberBundle.
import DLNFibre.Core.FibreOverBaseTriv
-- S5 (capstone): the over-base local-product-with-flatness headline.
-- `RankROpenOverBaseLocalProduct` (S1 rank-locus + cover + per-pivot OverBaseChartDatum) + the
-- pointwise headline `reducedFibre_existsOverBaseProductChartAt_rankEq` — every rank-=r prime sits
-- in a pivot chart I over the GEOMETRIC structure `chartDsigAtSchurLocAlgebra` (= schurToDsigAt,
-- named in the TYPE, not an existential φ a degenerate pullback could satisfy) under which the
-- total ring is `≃ₐ[SchurLoc] SchurLoc ⊗ sweepFibreRing` AND flat over SchurLoc. Base = SchurLoc,
-- the in-chart base DIRECTION (Spec(sweepSigmaRing) is the SOURCE/TOTAL, NOT the base); reading
-- this as fibre-family flatness over the genuine base needs projection compatibility (schurToDsigAt
-- = mult's projection pullback) — CLOSED by R5 in FibreProjectionCompat (below); global Flat π /
-- FiberBundle still R1.
import DLNFibre.Core.FibreBundleHeadline
-- R5 projection compatibility (S5/S4b item (i) CLOSED): the in-chart base map schurToDsigAt AGREES
-- with mult's comorphism multComap after precomposition with localizeSchur (on Schur generators) —
-- schurToDsigAt_comp_localizeSchur, every pivot; + ProjCompatOverBaseChart (projection-compat +
-- over-base triv + flatness). Closes the S5/S4b "projection compatibility" item; the LOCAL
-- target-side cocycle is landed (P2.c/f/g), only the GLOBAL gluing / `Flat π` stays residual (R1).
import DLNFibre.Core.FibreProjectionCompat
-- R5 target-side overlap: awayCongr' (generalized localization transport) +
-- targetProductOverlapTransition (the double-localized pairwise transition OBJECT, the DLN instance
-- of the abstract `Algebra.AtlasChart.overlapTransition`). The cocycle ROUND-TRIP is now PROVED
-- abstractly (P2.c `overlapTransition_trans_symm`, via the `AlgEquiv` groupoid laws off the heavy
-- double-localized type) and inherited on the DLN instance; triple cocycle (P2.f) + naturality
-- (P2.g) likewise. Only the GLOBAL gluing / `Flat π` stays residual (R1).
import DLNFibre.Core.FibreTargetOverlap
-- L7 (rlct-bridge): finrank (range deformationδ) is base-change invariant along a field extension
-- K/k — the orbit-tangent dimension is the SAME integer over ℝ and K. General conjugacy lemma
-- finrank_range_eq_of_baseChange_conj + the deformationδ commuting square + the banked
-- LinearAlgebra.BaseChange.finrank_range_baseChange brick. The dimension-side of the real↔complex
-- transfer.
import DLNFibre.Core.DeformationBaseChange
-- foundation-lift P1-R1: the minimal-primes-of-`sInf`-of-a-finite-prime-family SPIKE, extracted
-- from SigmaComponents to a clean Mathlib-grade home (ns `Ideal`, mirrors
-- `Mathlib.RingTheory.Ideal.MinimalPrime`); `Ideal.minimalPrimes_sInf_of_finite_of_isPrime`.
import DLNFibre.Core.MinimalPrime.Finite
-- foundation-lift P1-R2: the localization `≤`-half `ringKrullDim S ≤ ringKrullDim R` for any
-- localization `S = M⁻¹R`, re-homed from `LocalizationKrullDim` into the `Core.Dimension` family
-- (ns `DLNFibre.Core.Dimension`, mirrors a would-be `Mathlib.RingTheory.KrullDimension.Localization`);
-- `DLNFibre.Core.Dimension.ringKrullDim_localization_le`.
import DLNFibre.Core.Dimension.Localization
-- foundation-lift P1-R4: the `TopDimMinPrimes` count-engine core (top-dimensional minimal primes
-- + `comap`-transport along a `RingEquiv` ⟹ `ncard` invariance), re-homed from `TopDimMinPrimes`
-- into the `Core.MinimalPrime` family (ns `Ideal`, mirrors
-- `Mathlib.RingTheory.Ideal.MinimalPrime`); `Ideal.TopDimMinPrimes`,
-- `Ideal.topDimMinPrimes_ncard_eq_of_ringEquiv`.
import DLNFibre.Core.MinimalPrime.TopDimensional
-- foundation-lift P1-R5: the four general count-transport rungs built on the R4 core, re-homed from
-- `TopDimMinPrimes{Localization,Poly,Radical,Bridge}` into the `Core.MinimalPrime` family (ns
-- `Ideal`, mirrors `Mathlib.RingTheory.Ideal.MinimalPrime`): away-localization survival
-- (`Ideal.topDimMinPrimes_ncard_away_eq`, the per-prime no-drop keystone), polynomial-extension
-- descent (`Ideal.topDimMinPrimes_mvPolynomial_ncard_eq`), radical-insensitivity
-- (`Ideal.topDimMinPrimes_quotient_radical_ncard_eq`), and the height ↔ dimension bridge
-- (`Ideal.ringKrullDim_quotient_eq_iff_height_eq`).
import DLNFibre.Core.MinimalPrime.Localization
import DLNFibre.Core.MinimalPrime.Polynomial
import DLNFibre.Core.MinimalPrime.Radical
import DLNFibre.Core.MinimalPrime.Bridge
-- foundation-lift P2-R2: the matrix minor-rank core, extracted from `Core.RankLocusClosed` into the
-- network-free `Core.Matrix.RankMinors` (ns `Matrix`, mirrors `Mathlib.LinearAlgebra.Matrix.Rank`):
-- the determinantal-rank criterion `Matrix.rank_le_iff_forall_submatrix_det_eq_zero` (over a field,
-- `A.rank ≤ r ↔` every `(r+1)`-minor's det = 0) + the supports
-- (`rank_submatrix_le_rank`, `det_eq_zero_of_rank_lt`, `submatrix_det_eq_zero_of_rank_le`,
-- `exists_injective_linearIndependent_rows`, `exists_submatrix_det_ne_zero_of_le_rank`) and the
-- injective-field-hom rank invariance `Matrix.rank_map_eq_of_injective`.
import DLNFibre.Core.Matrix.RankMinors
-- foundation-lift P3-R1: the cotangent-dimension = Jacobian-kernel dimension formula (cotangent =
-- `coker Jᵀ`, tangent = `ker J`; finite dims agree), extracted from
-- `Core.CotangentJacobian` into two network-free libraries. The localize-the-cotangent-space
-- comparison `Ideal.finrank_cotangentSpace_localization_eq_cotangent` (ns `Ideal`, mirrors
-- `Mathlib.RingTheory.Ideal.Cotangent`; `[CommRing k]`, no `Field`); and the rectangular point-
-- Jacobian cotangent-dimension headline `MvPolynomial.finrank_cotangentSpace_eq_finrank_ker_jacobian`
-- (ns `MvPolynomial`, mirrors `Mathlib.RingTheory.Kaehler.Polynomial`) — no smoothness, more general
-- than Mathlib's smooth/square submersive Jacobian.
import DLNFibre.Core.RingTheory.Ideal.CotangentLocalization
import DLNFibre.Core.RingTheory.MvPolynomial.CotangentJacobian
-- det-atlas P2.b′: the `AlgEquiv` groupoid laws absent in Mathlib v4.29 — `trans_assoc`,
-- `trans_refl`, `refl_trans` (each `ext x; rfl`; Mathlib has only the inverse laws
-- `self_trans_symm`/`symm_trans_self`). Bare Mathlib-mirror namespace `AlgEquiv`. The cocycle
-- unblocker for the P2.c target-side round-trip (rearrange `trans` at the abstract `AlgEquiv`
-- level, off the heavy double-localized chart type).
import DLNFibre.Core.Algebra.AlgEquiv.Groupoid
-- det-atlas P2.b: the abstract overlap transition maps of a constructive pivot-chart atlas
-- (`Algebra.AtlasChart` = chart-element + bare-`k` trivialization; `overlapElt`/`targetChartLoc`/
-- `overlapTriv`/`chartOverlapTransitionK`(+ round-trip)/`overlapTransition`; `AtlasFibreChart`
-- stores `chartElt` + the over-base `StandardFibreChart` as the SINGLE trivialization, with a
-- DERIVED `toAtlasChart` whose `trivK = fibreModel.triv.restrictScalars k` — the product tie is
-- definitional). Built from the P1.a overlap API
-- (`awayOverlap`/`awayOverlapTransition`/`awayCongr'`) + the P2.a atlas datum; bare `Algebra` ns
-- (L7). The DLN target-side transition (`FibreTargetOverlap`) is the instance. LANDED: pairwise
-- round-trip (P2.c), canonical triple cocycle (P2.f), naturality + restricted-2-fold cocycle
-- (P2.g), product-trivialization coherence (`AtlasFibreChart.overlapTransition_isProduct`).
-- Roadmapped: GLOBAL gluing only (R1).
import DLNFibre.Core.RingTheory.Determinantal.AtlasTransition
-- det-atlas P2.d: the bespoke Zariski local-triviality capstone. The abstract network-free
-- predicate `Algebra.IsZariskiLocallyTrivialAffineProduct k Base BaseLoc Fibre U` (chart family of
-- `AtlasFibreChart` — over-base PRODUCT trivialization, model FIXED to `BaseLoc ⊗_k Fibre` — + a
-- principal-open cover of the open `U`; the cocycle compatibilities are DERIVED theorems, NOT
-- fields: `overlapTransition_trans_symm` (P2.c), `tripleTransition_cocycle` (P2.f), the naturality
-- tie + restricted-2-fold cocycle (P2.g)). NOT a Mathlib `FiberBundle` (that is topological; there
-- is no Zariski local-triviality class at this pin). Bare `Algebra` ns (L7).
import DLNFibre.Core.RingTheory.Determinantal.LocalTriviality
-- det-atlas P2.d (DLN instance): the DLN reduced-fibre bundle is a non-vacuous instance of the
-- abstract predicate over the rank-`= r` open `rankROpen` —
-- `reducedFibre_isZariskiLocallyTrivialAffineProduct` (ι = pivots, chart = `pivotAtlasFibreChart` =
-- chartElt `pivotElt` + `standardFibreChartOfPivot` fibre model, cover = the PivotDatum-indexed
-- scheme cover). Axiom-clean ⟹ the non-vacuity proof. The open is load-bearing (a bundle over the
-- closure Σ̄^r is false).
import DLNFibre.Core.FibreZariskiLocalTriviality
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2LocalJacobianMeasure
import DLNFibre.DLN.Aoyagi.SelectedEntryAnalyticAtlasProducer
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff
import DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge
import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartJacobianVolumeData
import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartRegularData
import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartAnalyticPredicateData
import DLNFibre.DLN.Aoyagi.SelectedEntryOneChartSourceCoverageObstruction
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotSourceCoverageData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotRegularData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotJacobianVolumeData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotTransitionRegularData
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducerShell
import DLNFibre.DLN.Aoyagi.BlowupBranchProgress
import DLNFibre.DLN.Aoyagi.SelectedEntryBranchProgressBridge
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducerTermination
import DLNFibre.DLN.Aoyagi.SelectedEntryCase2ProducedGuards
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducedSourceData
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaProductMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge
import DLNFibre.DLN.Aoyagi.RegularSuspensionSourceReadback
import DLNFibre.DLN.Aoyagi.OriginalPrior
import DLNFibre.DLN.Aoyagi.OriginalPriorHaar
import DLNFibre.DLN.Aoyagi.MatrixMeasurable
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPrior
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPriorHaar
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13Coordinates
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderBridge
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyRawOrderMeasureBridge
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeBridge
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadback
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13FormalProductSourceImageFiniteIntegral
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaFormalProductSourceReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawImageHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaRawOrderReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotProducedPayloads
import DLNFibre.DLN.Aoyagi.SelectedEntryAllPivotBranchIndexedPayloads
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaFormalProductSourceImageContract
