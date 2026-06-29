import DLNFibre.DLN.RLCT.Validate.RouteMRadialComp
import DLNFibre.DLN.RLCT.Validate.RouteMBFactorsDet
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive

/-!
# `RouteMBInterface` — the frozen B-interface: the boundary factor `B` + its map-identity contract

The FROZEN interface between the BFactors construction (the formaliser's (a)+(b): the per-bdy CLEs
`ρ`/`E` + the `BFactors` list) and the headline wiring (the controller's (c): the map identity + the
final `det_comp`). Route #1 (`φ = B ∘ pivotBlowupOn(active,p)`, 2nd-eye-cleared): the chart factors
through the radial arrow, and the boundary factor `B = composeFold BFactors` is a `ChartFactor`-fold
of the per-boundary Schur/chain/LDU factors, each conjugated by a `chartIdxEquiv`-derived CLE
(`RouteMRoleCLE.flatBlockSplitCLE` + the engine-reshape `RouteMEngineReshape`).

This module FREEZES that interface as a `structure BData` bundling:
- `B` — the boundary factor map (the formaliser's `composeFold BFactors`);
- `DB` — its fderiv (`(foldDerivList BFactors u).prod`, FREE via `composeFold_hasFDerivAt`);
- `hasDB` — `HasFDerivAt B DB` (obligation (2));
- `hmap` — the MAP identity `φ = B ∘ pivotBlowupOn active structPivot` (obligation (1), discharged
  per-block via `schurFrameProd_block_*` + `pivotBlowupOn_apply`);
- `hdet` — `|det DB| = ∏ engine` (obligation (3), banked `foldDerivList_abs_det_perBoundary`).

Given a `BData`, the headline follows by `radialComp_abs_det` (the banked wiring) —
`interiorDet_headline_of_BData` below; the formaliser builds the `BData` instance. The interface
decouples the two: each side builds against `BData`'s fields without waiting on the other.

* `BData` — the frozen interface structure.
* `interiorDet_headline_of_BData` — the unconditional interior-det headline from a `BData` (WIRING:
  `radialComp_abs_det` + the bundled obligations). The LAST step once a `BData` is constructed.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked wiring; no analysis beyond it).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The frozen B-interface.** Bundles the boundary factor `B` (= `composeFold BFactors`), its
fderiv `DB`, obligation (2) `HasFDerivAt B DB`, obligation (1) map identity `φ = B ∘ pivotBlowupOn`,
and obligation (3) boundary det `|det DB| = ∏ engine` — at the achiever radial active set
(`p ∈ active`, `active.card = minAdm`). The formaliser constructs an instance (the (a)+(b) work);
headline is read off it by `interiorDet_headline_of_BData`. `engine s` is the per-boundary value
`|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`. -/
structure BData (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ) where
  /-- The radial active set (the pivot + the `u`-scaled `R`/`Rfin` free coords). -/
  active : Finset (Fin (routeMAmbient M))
  /-- The pivot is in the active set. -/
  hp_mem : structPivot M hN ∈ active
  /-- The active set has cardinality `minAdm` (the banked count). -/
  hcard : active.card = minAdm M
  /-- The boundary factor map `B = composeFold BFactors`. -/
  B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- `B`'s fderiv at the blown-up point (`(foldDerivList BFactors _).prod`). -/
  DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ)
  /-- Obligation (2): `B` has fderiv `DB` at the blown-up point. -/
  hasDB : HasFDerivAt B DB (pivotBlowupOn active (structPivot M hN) u)
  /-- Obligation (1): the MAP identity `φ = B ∘ pivotBlowupOn active structPivot`. -/
  hmap : phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
    = B ∘ pivotBlowupOn active (structPivot M hN)
  /-- The per-boundary engine values `|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`. -/
  engine : Fin L → ℝ
  /-- Obligation (3): the boundary factor's det is the engine product. -/
  hdet : |LinearMap.det DB.toLinearMap| = ∏ s : Fin L, engine s

/-- **The unconditional interior-det headline from a `BData`** (the WIRING, obligation (c)). Given
frozen `BData` (the formaliser's instance), the chart's Jacobian abs-det factorizes as
`|u_p|^{minAdm−1} · ∏_s engine s`. Reads off `radialComp_abs_det` (the banked route-#1 wiring) + the
bundled obligations (2)/(1)/(3). The LAST step of the interior-det leg. -/
theorem interiorDet_headline_of_BData (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ) (d : BData M t ha hN p hp1 hp2 rfin u) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u).toLinearMap|
      = |u (structPivot M hN)| ^ (minAdm M - 1) * ∏ s : Fin L, d.engine s := by
  rw [radialComp_abs_det M hN d.active d.hp_mem d.hcard d.B
      (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u d.DB d.hmap d.hasDB, d.hdet]

/-- **The pivot-generic frozen B-interface** (`BData` at an ARBITRARY radial slot `p₀ ∈ active`).
Identical to `BData` but the radial axis lives at the supplied `p₀ : Fin (routeMAmbient M)` (rather
than the hard-wired `structPivot M hN`), and the map identity is against the `p₀`-radial chart
`phiFlatLiveR1At … p₀`. Frees the achiever node to put the radial axis on a reader-complement slot,
dissolving `PivotNotReader` by membership. The headline reads `|u p₀|^{minAdm−1}·∏engine`. -/
structure BDataAt (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (p₀ : Fin (routeMAmbient M))
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ) where
  /-- The radial active set (the pivot `p₀` + the `u`-scaled free coords). -/
  active : Finset (Fin (routeMAmbient M))
  /-- The radial pivot `p₀` is in the active set. -/
  hp_mem : p₀ ∈ active
  /-- The active set has cardinality `minAdm` (the banked count). -/
  hcard : active.card = minAdm M
  /-- The boundary factor map `B = composeFold BFactors`. -/
  B : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- `B`'s fderiv at the blown-up point. -/
  DB : (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ)
  /-- Obligation (2): `B` has fderiv `DB` at the blown-up point. -/
  hasDB : HasFDerivAt B DB (pivotBlowupOn active p₀ u)
  /-- Obligation (1): the MAP identity `φ = B ∘ pivotBlowupOn active p₀`. -/
  hmap : phiFlatLiveR1At M t ha p hp1 hp2 p₀ rfin
    = B ∘ pivotBlowupOn active p₀
  /-- The per-boundary engine values `|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)}`. -/
  engine : Fin L → ℝ
  /-- Obligation (3): the boundary factor's det is the engine product. -/
  hdet : |LinearMap.det DB.toLinearMap| = ∏ s : Fin L, engine s

/-- **The unconditional interior-det headline from a `BDataAt`** (pivot-generic wiring). Given a
frozen `BDataAt` at radial slot `p₀`, the `p₀`-radial chart's Jacobian abs-det factorizes as
`|u p₀|^{minAdm−1} · ∏_s engine s`. Reads off `radialComp_abs_det_at` (pivot-generic wiring) + the
bundled obligations. -/
theorem interiorDet_headline_of_BDataAt (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (p : ℕ) (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (p₀ : Fin (routeMAmbient M))
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (u : Fin (routeMAmbient M) → ℝ) (d : BDataAt M t ha p hp1 hp2 p₀ rfin u) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveR1At M t ha p hp1 hp2 p₀ rfin) u).toLinearMap|
      = |u p₀| ^ (minAdm M - 1) * ∏ s : Fin L, d.engine s := by
  rw [radialComp_abs_det_at M d.active p₀ d.hp_mem d.hcard d.B
      (phiFlatLiveR1At M t ha p hp1 hp2 p₀ rfin) u d.DB d.hmap d.hasDB, d.hdet]

end DLNFibre.DLN.RLCT

end
