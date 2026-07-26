import DLNFibre.DLN.RLCT.Engine.GeoLeafLedger
import DLNFibre.DLN.RLCT.Engine.EngineConstruction

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoResRankZero` — STEP 0: `resRank = 0` on every geoAtlas leaf

The gate atom of the reroute V-lower discharge. The build (`buildTree M (conOracle M) s`) emits only
`leafOfState` leaves, whose Morse-residual rank is `0` (both `dite` branches — `leaves_resRank_zero`),
and `geoAtlas` only rewrites `chartMap` (`geoAtlas_leaf_update`), inheriting the ledger `resRank`
verbatim. Hence the residual side of the atlas is EMPTY: no Morse term, `terminalExponents` reads only
the divisor exponents.

This is the LEDGER precondition of the born-α survivor route: `resRank = 0` means the leaf's baseForm
carries no residual recursion, so the geometric residual `∑ⱼ residⱼ²` in the born-α pullback is a
pure UNIT-plus-recoord (the pnp "no deep {R=0}" fact F2). The GEOMETRIC survivor-on-domain (`hpos`
of `DomainSandwich.sandwich_on_domain_of_survivor`) is the born-α image of this ledger fact — that
bridge is the per-leaf concrete algebra, DISTINCT from this ledger-level atom.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **STEP 0 — every geoAtlas leaf has `resRank = 0`** (general `M`, `s`). Composition of the two
banked trunk lemmas: `geoAtlas_leaf_update` (each geoAtlas piece is a built-tree leaf with only
`chartMap` overwritten) ∘ `leaves_resRank_zero` (every built-tree leaf has `resRank = 0`). The
`chartMap` overwrite leaves the ledger `resRank` untouched, so it is `0` on every atlas piece. -/
theorem geoAtlas_resRank_zero (s : ConState L) :
    ∀ c ∈ geoAtlas (buildTree M (conOracle M) s), c.resRank = 0 := by
  intro c hc
  obtain ⟨l, hl, f, hf⟩ := geoAtlas_leaf_update _ c hc
  subst hf
  exact leaves_resRank_zero s l hl

-- Forced axiom gate: the STEP 0 ledger atom rests only on `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [geoAtlas_resRank_zero]

end DLNFibre.DLN.RLCT.Engine
