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
-- (C,θ) extraction (perm-invariance M5/L1): cCodim/numTop recovered from Qseries; the symmetry bridge.
import DLNFibre.Core.QSeriesExtraction
-- Permutation invariance prep (perm-invariance M6): Pmult is multiset-symmetric.
import DLNFibre.Core.CThetaPermInvariance
-- Thm 5.6 (the "fivegon", perm-invariance M3b): fivegonSum d = Pmult d, via the last-column transfer.
import DLNFibre.Core.QSeriesFivegon
-- Thm 5.5 (M4) chain: corner shift (S1'/S2), inverse-Pochhammer orthogonality, the per-r Poincaré product.
import DLNFibre.Core.QSeriesShift
import DLNFibre.Core.QSeriesOrth
import DLNFibre.Core.QSeriesThm55
-- Geometric transfer of Cor 5.10: the variety's (C,θ) of Σ̄^r is permutation-invariant (unconditional).
import DLNFibre.Core.CThetaGeometricPerm
