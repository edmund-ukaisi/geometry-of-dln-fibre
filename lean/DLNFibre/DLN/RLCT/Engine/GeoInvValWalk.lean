import DLNFibre.DLN.RLCT.Engine.GeoFoldRegroup
import DLNFibre.DLN.RLCT.Engine.GeoInvVal

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoInvValWalk` — the value walk `Inv_val` (loss-t15, PHASE 3b build)

The value instance of t14's fold walk (`GeoFoldRegroup.geoAtlas_cocycle`): threading the
prod-diagonalization invariant `Inv_val(acc, s)` down `buildTree`, mirroring t14's skeleton
(`conOracle` re-dispatch, `mem_edgesLeaves_fanned_*`, the four per-case maintenance) with the VALUE
payload. The terminal case gives `prod = diagonal(b)` and plugs into the PROVEN
`GeoInvVal.leafDiagFrob_of_prodDiag`, closing `leafDiagFrob_geoAtlasNorm`.

**Encoding = ENTRY-WISE** (team-lead steer (b), 2026-07-20): the invariant is per prod-entry,
matching the per-entry (α) reads (`geoChartMap_flat_*`) and the cert's entry-wise value battery, and
sidestepping matrix-block instance friction. A `cleared s i` diagonal position carries its
`b`-monomial `bmon s w i` (the `z_{birthFlatCoord}` product per chain level); a cleared off-diagonal
cell is `0`; an uncleared cell is the residual read `resid s w i j`. At terminal `s` every position
is cleared ⟹ `prod = diagonal(bmon)` ⟹ `leafDiagFrob_of_prodDiag` (the block form
`diag(b)·[[E,O],[O,D]]` is a presentational corollary, not built — the bridge is the only consumer).

**STAGING (t14 discipline):** scaffold (elaborating, sorried) → the ends (base + leaf-discharge) +
reused reads → the four matrix-maintenance cases as SEPARATE banked greens, pushed each. Reusable
t14 reads + fan helpers + this seat's `leafDiagFrob_of_prodDiag`/`frobSq_of_diagonal` compose
(import foundation confirmed).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The value invariant `Inv_val`** (ENTRY-WISE, team-lead steer (b)): the acc-threaded
prod-diagonalization, per prod-entry. `cleared s i` marks the diagonal positions the fold to `s` has
resolved; a cleared diagonal cell carries its `b`-monomial `bmon s w i`, a cleared off-diagonal cell
is `0`, an uncleared cell is the residual read `resid s w i j`. The three payload fields
(`cleared`/`bmon`/`resid`) are pinned during the build (`bmon` = the `z_{birthFlatCoord}` chain
product; `cleared`/`resid` from the ledger + the residual-coord reads). Base (`conRoot`): nothing
cleared, `resid = prod M w` (raw); maintenance: each step clears one diagonal position (α Schur);
terminal: all cleared ⟹ `prod = diagonal(bmon)`. -/
def InvVal (cleared : ConState L → Fin (M 0) → Prop) [∀ s i, Decidable (cleared s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resid : ConState L → Params M → Fin (M 0) → Fin (M (Fin.last L)) → ℝ)
    (acc : Params M → Params M) (s : ConState L) : Prop :=
  ∀ (w : Params M) (i : Fin (M 0)) (j : Fin (M (Fin.last L))),
    prod M (acc w) i j
      = if cleared s i then (if (i : ℕ) = (j : ℕ) then bmon s w i else 0) else resid s w i j

/-- **Leaf discharge** (the terminal case → `LeafDiagFrob`, PROVEN structure): at a leaf `l` whose
state `s_leaf` has EVERY diagonal position cleared (`hall`), `InvVal` collapses to
`prod M (l.chartMap w) i j = if (i:ℕ)=(j:ℕ) then bmon s_leaf w i else 0` — the exact input of PROVEN
`leafDiagFrob_of_prodDiag`. Given the `b`-monomial factorization (`hbmon`: `bmon = (∏ divCoord)·ρ`,
counted) and the ratio properties (`hone`/`hbd`), this yields `LeafDiagFrob l`. The residual `resid`
is unused here (vacuous once all cleared), matching team-lead's leaf-assembly reason (iv). -/
theorem leafDiagFrob_of_invVal_leaf
    (cleared : ConState L → Fin (M 0) → Prop) [∀ s i, Decidable (cleared s i)]
    (bmon : ConState L → Params M → Fin (M 0) → ℝ)
    (resid : ConState L → Params M → Fin (M 0) → Fin (M (Fin.last L)) → ℝ)
    (l : LeafData M) (s_leaf : ConState L)
    (hinv : InvVal cleared bmon resid l.chartMap s_leaf)
    (hall : ∀ i : Fin (M 0), cleared s_leaf i)
    (ρ : Params M → Fin (M 0) → ℝ) (hi : ℝ)
    (hbmon : ∀ w ∈ l.srcBox, ∀ i : Fin (M 0),
      (if (i : ℕ) < M (Fin.last L) then bmon s_leaf w i else 0)
        = (∏ k : Fin l.numDiv, paramsEquivFlat M w (l.divCoord k)) * ρ w i)
    (hone : ∀ w ∈ l.srcBox, ∃ i : Fin (M 0), ρ w i = 1)
    (hbd : ∀ w ∈ l.srcBox, ∑ i : Fin (M 0), (ρ w i) ^ 2 ≤ hi) :
    LeafDiagFrob l := by
  refine leafDiagFrob_of_prodDiag l (fun w i => bmon s_leaf w i) ρ hi ?_ hbmon hone hbd
  intro w _ i j
  have := hinv w i j
  rwa [if_pos (hall i)] at this

end DLNFibre.DLN.RLCT.Engine
