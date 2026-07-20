import DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup
import DLNFibre.DLN.RLCT.Engine.GeoInvVal

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInvValWalk` — the value walk `Inv_val` (loss-t15, PHASE 3b build)

The value instance of t14's fold walk (`GeoFoldRegroup.geoAtlas_cocycle`): threading the
prod-diagonalization invariant `Inv_val(acc, s): prod M (acc w) = partialDiag s w` down `buildTree`,
mirroring t14's skeleton (`conOracle` re-dispatch, `mem_edgesLeaves_fanned_charted/_chartless`, the
four per-case maintenance) with the VALUE payload. The terminal case gives `prod = diagonal(b)` and
plugs into the PROVEN `GeoInvVal.leafDiagFrob_of_prodDiag`, closing `leafDiagFrob_geoAtlasNorm`.

**Import foundation (this file's first job):** confirm t14's reusable reads (`geoChartMap_flat_*`,
`geoChartMapNorm_apply_oncone`), the fan-decomposition helpers, and this seat's consumer side
(`leafDiagFrob_of_prodDiag`, `frobSq_of_diagonal`) compose into one module — the DAG the build
stands on. The `partialDiag` payload + base + four matrix-maintenance identities + walk
instantiation land here incrementally (statement-first; `partialDiag` encoding pinned per rider 2).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The value invariant `Inv_val`** (abstract in the partial-diagonal family `partialDiag`, per
rider 2 — the concrete block encoding `diag(b(s))·[[E_J,O],[O,D_J]]` is pinned during the build): the
acc-threaded prod-diagonalization. `prod M (acc w) = partialDiag s w` at the state `s` the fold
reaches. Base `partialDiag conRoot w = prod M w` (raw product); the four per-`stepUpdate`-case
maintenance advances one clearing step (the α Schur clears one residual column/block); the terminal
case is `partialDiag s w = diagonal(b)` — fed to `leafDiagFrob_of_prodDiag`. -/
def InvVal (partialDiag : ConState L → Params M → Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ)
    (acc : Params M → Params M) (s : ConState L) : Prop :=
  ∀ w, prod M (acc w) = partialDiag s w

end DLNFibre.DLN.RLCT.Engine
