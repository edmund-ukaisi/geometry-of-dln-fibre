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
import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.Lambda
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
-- Axiom-hygiene check: emits `#print axioms` for the load-bearing results on every build.
import DLNFibre.DLN.RLCT.AxCheck
