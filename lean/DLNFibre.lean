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
-- θ-components (Route-A fibre entry): detΔ ≡ 1 on the fibre ⟹ localizing O(fibre) at detΔ is an iso
-- (reducedness-free); + the shifted count numTop d r = cTheta(d−r) = C(m,|δ|).
import DLNFibre.Core.FibreDetUnit
import DLNFibre.Core.CThetaShiftCount
-- θ-components (fibre-count transport, thread 06): the TopDimMinPrimes framework + the
-- polynomial-extension minimal-prime descent + the Σ̄^r / fibre count endpoints.
import DLNFibre.Core.TopDimMinPrimes
import DLNFibre.Core.TopDimMinPrimesPoly
import DLNFibre.Core.TopDimMinPrimesBridge
import DLNFibre.Core.TopComponentsTopDim
import DLNFibre.Core.FibreTopDimDetUnit
-- θ-components (fibre-count wiring, thread 08): the keystone localization-survival of the top-dim
-- minimal-prime count, + radical-insensitivity (W3), the chart-e count carry, and the W2 avoidance.
import DLNFibre.Core.TopDimMinPrimesLocalization
import DLNFibre.Core.TopDimMinPrimesRadical
import DLNFibre.Core.TopDimMinPrimesChartE
import DLNFibre.Core.TopDimMinPrimesGfibAvoid
-- θ-components (W0 indexing bridge): TopDimMinPrimes(O(Σ̄^r)) = TopDimMinPrimes(O(Σ^r)) (closed ≤r ↔
-- exact =r at the top-dim minimal-prime level), via unconditional recovery + corner-monotonicity.
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
