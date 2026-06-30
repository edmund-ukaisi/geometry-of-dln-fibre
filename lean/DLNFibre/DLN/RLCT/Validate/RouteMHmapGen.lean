import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive
import DLNFibre.DLN.RLCT.Validate.RouteMSchurValue

/-!
# `RouteMHmapGen` — the general per-boundary `Cgen = schurFrameProd` identity (∀M-L2 hmap brick)

The load-bearing per-boundary link for the ∀M interior-det headline's map identity (`hmap`): the
live achiever decoder's compressed transition `Cgen v … (genBlkFlatLiveR1 M t ha p …) (k+1)` at an
INTERIOR boundary `k+1 < L` is the Schur frame `schurFrameProd … (readK)(readX)(readN)(E)` —
`[[K, K·N],[X·K, X·K·N + v·E]]` — with `E = pivotEIndicator` at the pivot boundary `p = k+1` (the
fixed `1`-carrier) and `E = readE` at the other interior boundaries.

This is the ∀-opaque-boundary generalization of the (2,2,2)-specific `Cgen1_Glr`/`Cgen2_Glr`
(`RouteMBData222`), reusing the banked opaque-width Schur-frame value `schurFrameProd`
(`RouteMSchurValue`) — whose `castAdd`/`natAdd` reindexing kernel is already discharged. No new
dependent-`Fin` engineering: the interior `Cgen` and `schurFrameProd` are the SAME
`bmatStack · chainQ + v • rmatPad` expression once the decoder's block-readers are unfolded.

* `Cgen_live_interior_eq_schurFrameProd` — non-pivot interior boundary (`E = readE`).
* `Cgen_liveR1_interior_pivot_eq_schurFrameProd` — the pivot interior boundary
  (`E = pivotEIndicator`, the fixed `1`-carrier).
* `Cgen_liveR1_leaf` — the leaf boundary (`Cgen … L = v • rfin`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the decoder unfold + the banked frame value).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- The live decoder's interior `Bmat (k+1) = bmatStack(readK,readX)` (`k < L`), unchanged from the
structured decoder. -/
theorem genBlkFlatLive_Bmat_succ (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ)
    (k : ℕ) (hk : k < L) :
    (genBlkFlatLive M t ha rfin x).Bmat (k + 1)
      = bmatStack M t (k + 1) (ha.hdesc k hk)
          (readK M t ha x ⟨k, hk⟩) (readX M t ha x ⟨k, hk⟩) := by
  show (genBlkFlatStruct M t ha x).Bmat (k + 1) = _
  simp only [genBlkFlatStruct, dif_pos hk]

/-- The live decoder's interior `Nblk (k+1) = readN ⟨k⟩` (`k < L`). -/
theorem genBlkFlatLive_Nblk_succ (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ)
    (k : ℕ) (hk : k < L) :
    (genBlkFlatLive M t ha rfin x).Nblk (k + 1) = readN M t ha x ⟨k, hk⟩ := by
  show (genBlkFlatStruct M t ha x).Nblk (k + 1) = _
  simp only [genBlkFlatStruct, dif_pos hk]

/-- The live decoder's interior `Rmat (k+1) = rmatPad(readE ⟨k⟩)` (`k < L`). -/
theorem genBlkFlatLive_Rmat_succ (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ)
    (k : ℕ) (hk : k < L) :
    (genBlkFlatLive M t ha rfin x).Rmat (k + 1)
      = rmatPad M t (k + 1) (ha.hdesc k hk) (ha.hub k) (readE M t ha x ⟨k, hk⟩) := by
  show (genBlkFlatStruct M t ha x).Rmat (k + 1) = _
  simp only [genBlkFlatStruct, dif_pos hk]

/-- **The non-pivot interior `Cgen = schurFrameProd`** (`k+1 < L`): the live decoder's compressed
transition at interior boundary `k+1` is the Schur frame with `E = readE`. The opaque-width
generalization of `Cgen1_Glr`'s non-pivot case. -/
theorem Cgen_live_interior_eq_schurFrameProd (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (v : ℝ)
    (x : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hk1 : k + 1 < L) :
    Cgen v M t (genBlkFlatLive M t ha rfin x) (hleStruct M t ha) (k + 1)
      = schurFrameProd M t (k + 1) (ha.hdesc k (by omega)) (ha.hub k) v
          (readK M t ha x ⟨k, by omega⟩) (readX M t ha x ⟨k, by omega⟩)
          (readN M t ha x ⟨k, by omega⟩) (readE M t ha x ⟨k, by omega⟩) := by
  rw [Cgen, dif_pos hk1,
    genBlkFlatLive_Bmat_succ M t ha rfin x k (by omega),
    genBlkFlatLive_Nblk_succ M t ha rfin x k (by omega),
    genBlkFlatLive_Rmat_succ M t ha rfin x k (by omega), schurFrameProd]

/-- **The pivot interior `Cgen = schurFrameProd`** (`k+1 < L`, pivot at `p = k+1`): the R1 live
decoder's transition at the pivot boundary is the Schur frame with `E = pivotEIndicator` (the fixed
`1`-carrier the radial `v` scales). The opaque-width generalization of `Cgen1_Glr`. `Bmat`/`Nblk`
are inherited from `genBlkFlatLive` (the R1 override hits only `Rmat p`); `Rmat (k+1) =
rmatPad (pivotEIndicator)` via `genBlkFlatLiveR1_Rmat_pivot`. -/
theorem Cgen_liveR1_interior_pivot_eq_schurFrameProd (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (k : ℕ) (hk1 : k + 1 < L)
    (hp1 : Text M t (k + 1 + 1) ≤ Text M t (k + 1)) (hp2 : Text M t (k + 1 + 1) ≤ Wext M (k + 1))
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (v : ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M t (genBlkFlatLiveR1 M t ha (k + 1) hp1 hp2 rfin x) (hleStruct M t ha) (k + 1)
      = schurFrameProd M t (k + 1) (ha.hdesc k (by omega)) (ha.hub k) v
          (readK M t ha x ⟨k, by omega⟩) (readX M t ha x ⟨k, by omega⟩)
          (readN M t ha x ⟨k, by omega⟩) (pivotEIndicator M t (k + 1)) := by
  have hB : (genBlkFlatLiveR1 M t ha (k + 1) hp1 hp2 rfin x).Bmat (k + 1)
      = bmatStack M t (k + 1) (ha.hdesc k (by omega))
          (readK M t ha x ⟨k, by omega⟩) (readX M t ha x ⟨k, by omega⟩) :=
    genBlkFlatLive_Bmat_succ M t ha rfin x k (by omega)
  have hN : (genBlkFlatLiveR1 M t ha (k + 1) hp1 hp2 rfin x).Nblk (k + 1)
      = readN M t ha x ⟨k, by omega⟩ :=
    genBlkFlatLive_Nblk_succ M t ha rfin x k (by omega)
  have hR : (genBlkFlatLiveR1 M t ha (k + 1) hp1 hp2 rfin x).Rmat (k + 1)
      = rmatPad M t (k + 1) hp1 hp2 (pivotEIndicator M t (k + 1)) :=
    genBlkFlatLiveR1_Rmat_pivot M t ha (k + 1) hp1 hp2 rfin x
  rw [Cgen, dif_pos hk1, hB, hN, hR, schurFrameProd]

/-- **The leaf `Cgen … L = v • rfin`** (`dif_neg`; the live leaf residual `Rfin L = rfin`). The
opaque-width generalization of `Cgen2_Glr`. -/
theorem Cgen_liveR1_leaf (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (v : ℝ)
    (x : Fin (routeMAmbient M) → ℝ) :
    Cgen v M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x) (hleStruct M t ha) L = v • rfin := by
  rw [Cgen, dif_neg (lt_irrefl L)]
  congr 1
  exact dif_pos rfl

end DLNFibre.DLN.RLCT
