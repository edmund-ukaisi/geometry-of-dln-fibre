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
-- from mult⁻¹B ⊆ Σ̄^r. The +r(d_0+d_N−r) shift (the identity) stays Cited — it needs the exact-rank
-- chart trivialization (absent at v4.29); the naïve sandwich is a NO-GO (see the module docstring).
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
-- and — CONDITIONAL on the trivialization `e : S ≃ₐ[k] R ⊗ F_B` + `IsReduced S` (explicit hypotheses,
-- the open R2-3b wall) — `fibreGenIdeal` radical + the radical-collapse of MultComorphism pt4. The
-- final BundleShiftInterface discharge WAITS for R2-3b to prove `e`.
import DLNFibre.Core.FibreReducedTrivialization
-- Deep chart ring (R2-3b-1+2, the residual G2-3 wall foundation): `Sred = Localization.Away(ΔPdeep) ⧸
-- IadDeep` for general d (the engine's base presentation is N=1 only), the RepCoord↔stratum/endpoint
-- bridges, and the localized base→total map `schurToSred : SchurLoc → Sred` giving Sred its
-- SchurLoc-algebra structure (R2-3a's R = SchurLoc, S = Sred). The crux containments (det transport,
-- base→deep sigmaIdeal, NON-circular) proved. Feeds R2-3b-3 (endpoint AlgEquiv) + R2-3b-4 (the iso e).
import DLNFibre.Core.DeepChartRing
-- Endpoint-normalization gauge AlgEquiv (R2-3b-3): the vertex-unit conjugation `Aᵢ ↦ P_{i+1}·Aᵢ·P_i⁻¹`
-- (= landed `BaseChange.baseChange`) on the generic tuple, `gaugeEquiv d P`, over arbitrary CommRing R,
-- + the transport `gaugeEquiv (multPoly) = P_last·M·P_0⁻¹` (endpoint gauge P_0=H, P_last=L⁻¹ ⟹ L⁻¹·M·H⁻¹).
-- The coordinate change that turns `mult(A)=LEH` into `mult(Ã)=E`. Feeds R2-3b-4 (instantiate + descend).
import DLNFibre.Core.EndpointNormalization
