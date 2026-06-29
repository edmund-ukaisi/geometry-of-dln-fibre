import DLNFibre.DLN.RLCT.Validate.RouteMLeafSlot
import DLNFibre.DLN.RLCT.Validate.RouteMHmapGen

/-!
# `RouteMLeafChart` — the `genBlkFlatLive` + leaf-pivot chart `phiFlatLiveAt` (∀M-L2)

The achiever chart for the ∀M-L2 interior-det headline, built on the LIVE-leaf decoder
`genBlkFlatLive` (NOT `genBlkFlatLiveR1` — the R1 override zeroes the interior E-block angular
coords, valid only for a `1×1` E-block; the named bug). The radial axis is read at an arbitrary slot
`p₀` (here `p₀ = leafSlot … 0 0`, a leaf slot), and the fixed-`1` pivot lives in the leaf
(`rfinFixedPivot … (0,0) = 1`) rather than in an E-block override.

* `rfinFixedPivot` — the leaf reader: `(0,0) ↦ 1` (the fixed radial pivot), and off `(0,0)` the leaf
  coordinate `(i,j) ↦ x (leafSlot i j)`.
* `phiFlatLiveAt` — `phiGen (x p₀) M tach (genBlkFlatLive … (rfinFixedPivot x) x) hle`.
* `phiFlatLiveAt_rate` — the decoder-agnostic rate `routeMCore M (phiFlatLiveAt … x) = (x p₀)²·V`
  (via `routeMCore_phiGen` + the live identity-boundary `hC0_live`).
* `p₀_mem_activeM` — the radial pivot `p₀ = leafSlot … 0 0` lies in `activeM`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the live decoder + the banked rate engine; no
analysis beyond it).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-! ## The fixed-pivot leaf reader -/

/-- **The fixed-pivot leaf reader** — the leaf residual with the `(0,0)` entry pinned to the fixed
`1` (the radial-pivot axis) and the other entries read from the leaf flat slots. The radial pivot is
`p₀ = leafSlot … 0 0`; `Cgen … L = (x p₀)·rfinFixedPivot`, so `(0,0)` is the bare radial `x p₀·1`
and the rest are leaf coordinates. -/
noncomputable def rfinFixedPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (Text M (tach M) L)) (Fin (Wext M L)) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1 else x (leafSlot M (tach M) ha hL i j)

/-- The fixed-pivot leaf reader is the constant `1` at `(0,0)`. -/
theorem rfinFixedPivot_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    rfinFixedPivot M ha hL x ⟨0, h0r⟩ ⟨0, h0c⟩ = 1 := by
  simp [rfinFixedPivot]

/-- The fixed-pivot leaf reader is the leaf coordinate off `(0,0)`. -/
theorem rfinFixedPivot_off (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (x : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) L)) (j : Fin (Wext M L)) (hne : ¬ (i.val = 0 ∧ j.val = 0)) :
    rfinFixedPivot M ha hL x i j = x (leafSlot M (tach M) ha hL i j) := by
  simp [rfinFixedPivot, hne]

/-! ## The radial pivot slot `p₀ = leafSlot … 0 0` -/

/-- **The radial pivot slot** `p₀ = leafSlot … 0 0` (the leaf `(0,0)` flat coordinate, the fixed-`1`
radial axis). -/
noncomputable def leafPivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) : Fin (routeMAmbient M) :=
  leafSlot M (tach M) ha hL ⟨0, h0r⟩ ⟨0, h0c⟩

/-! ## The `genBlkFlatLive` + leaf-pivot chart -/

/-- **The `genBlkFlatLive` + leaf-pivot chart** `phiFlatLiveAt … p₀ x := phiGen (x p₀) M tach
(genBlkFlatLive … (rfinFixedPivot x) x) hle`. The radial scalar is read at the supplied slot `p₀`
(here `leafPivot`); the live leaf carries the fixed-`1` pivot at `(0,0)` plus the leaf coordinates.
No E-block override (unlike the R1 chart): the interior E-block reads `readE` from `x`. -/
noncomputable def phiFlatLiveAt (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (p₀ : Fin (routeMAmbient M))
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x p₀) M (tach M) (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x)
    (hleStruct M (tach M) ha)

/-- **The decoder-agnostic rate** `routeMCore M (phiFlatLiveAt … x) = (x p₀)²·V`, via
`routeMCore_phiGen` + the live identity-boundary `hC0_live` (the identity boundary is unchanged from
the structured decoder, so the rate transfers verbatim). -/
theorem phiFlatLiveAt_rate (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (p₀ : Fin (routeMAmbient M)) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLiveAt M ha hL p₀ x)
      = (x p₀) ^ 2
        * VvalGen (x p₀) M (tach M)
            (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x)
            (hleStruct M (tach M) ha) :=
  routeMCore_phiGen (x p₀) M (tach M)
    (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x) (hleStruct M (tach M) ha)
    (hC0_live M (tach M) ha (rfinFixedPivot M ha hL x) (x p₀) x)

/-! ## The radial pivot lies in `activeM` (L = 2) -/

variable {M : Fin (2 + 1) → ℕ}

/-- **`leafPivot ∈ activeM`** (`L = 2`): the radial pivot `p₀ = leafSlot … 0 0` lies in the leaf
image, hence in `activeM = activeEImg ∪ activeLeafImg`. -/
theorem leafPivot_mem_activeM (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    leafPivot M ha (by norm_num) h0r h0c ∈ activeM M ha := by
  rw [activeM]
  refine Finset.mem_union_right _ ?_
  rw [activeLeafImg, Finset.mem_image]
  exact ⟨(⟨0, h0r⟩, ⟨0, h0c⟩), Finset.mem_univ _, rfl⟩

end DLNFibre.DLN.RLCT
