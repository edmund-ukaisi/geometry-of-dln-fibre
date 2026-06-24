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
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.DLN.RLCT.Validate.DeepestBaseL1
-- Axiom-hygiene check: emits `#print axioms` for the load-bearing results on every build.
import DLNFibre.DLN.RLCT.AxCheck
