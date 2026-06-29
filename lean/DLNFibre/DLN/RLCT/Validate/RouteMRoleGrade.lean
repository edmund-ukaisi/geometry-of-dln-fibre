import DLNFibre.DLN.RLCT.Validate.RouteMLayerGrade

/-!
# `RouteMRoleGrade` — the role-refinement of `bLayer`: Schur-role vs lift-role grading

The **fine role-grading** the interior-det headline's block-triangularity (`hbt`) ultimately needs is
a BOUNDED REFINEMENT of the proven `bLayer` grading (`RouteMLayerGrade`): within each boundary layer
`k`, split the coordinates into the **Schur role** (the `K/X/N/E` frame coords, `chartIdxEquiv ↦
⟨k, Sum.inl ·⟩`) and the **lift role** (the `W` chain-lift coords, `chartIdxEquiv ↦ ⟨k, Sum.inr ·⟩`).
This module supplies that refinement, at the VALUE level only (no fderiv, no `paramsEquivFlat`
flattening) — the de-risked "heart" of route α (`item3-frameM-buildspec.md` b-FrameM-3).

## What this is (and is NOT)

* `bRole` — the role grading `2·bLayer + (1 if lift-role else 0)`: a strict refinement of `bLayer`
  (`bRole / 2 = bLayer`, `bRole` separates the two roles of one layer by parity).
* `isSchurRole` / `isLiftRole` — the role predicate, read off `chartIdxEquiv`'s `Sum.inl`/`Sum.inr`.
* `readK/X/N/E_indep_of_role` — each Schur reader of boundary `k` is invariant under changing `x`
  away from the SCHUR ROLE of layer `k` (a strengthening of `RouteMLayerGrade.read*_indep_of`, which
  used the whole layer `k`): the reader's slot is a `Sum.inl`, so a change confined to lift-role
  (`Sum.inr`) coords — or to any other role/layer — leaves it fixed.
* `readW_indep_of_role` — dually, the lift reader is invariant under changes away from the LIFT ROLE.

The genuine new content is the role PARITY refinement and its one-sidedness: the readers' slot-roles
are disjoint (`Sum.inl ≠ Sum.inr`), so the role grading has zero within-layer 2-cycles at the readers.

## Scope honesty (the route-α recalibration)

This is the INPUT-side value-locality, role-refined. It does NOT, on its own, give the fderiv
block-triangularity of the real chart frame: that additionally needs (i) `paramsPack_layer` —
aligning the chart's OUTPUT grading (`paramsEquivFlat`'s `FlatIdx` layer, where layer `s` carries the
whole `M_s · M_{s+1}` weight block) with this INPUT grading (`chartIdxEquiv`'s `ChartIdx` layer, where
layer `k` carries `schurDim k + liftDim k` coords), a separate alignment construction, since
`Matrix.BlockTriangular` consumes a SINGLE grading on rows and columns. The two per-layer block sizes
differ in general, so a RAW-layer-preserving `FlatIdx ≃ ChartIdx` need not exist — the honest common
grading is the COARSE boundary-level one (radial grade `0` + one grade per boundary), which is also the
route-decision (the fine role grading here is then optional input-side infrastructure). And (ii) the
per-block-det `toSquareBlock` reindex (the deferred cast-surface b-1). Those are tracked separately;
this module banks the bounded refinement.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-! ## The role predicate and the role grading -/

/-- **The Schur-role predicate**: a flat coordinate `q` is a Schur-frame (`K/X/N/E`) coordinate iff its
`chartIdxEquiv` image is a `Sum.inl` (a `schurDim` slot). -/
noncomputable def isSchurRole (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (q : Fin (routeMAmbient M)) : Prop :=
  ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) q).snd.isLeft

/-- **The lift-role predicate**: a flat coordinate `q` is a chain-lift (`W`) coordinate iff its
`chartIdxEquiv` image is a `Sum.inr` (a `liftDim` slot). -/
noncomputable def isLiftRole (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (q : Fin (routeMAmbient M)) : Prop :=
  ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) q).snd.isRight

/-- **The role grading** `bRole = 2·bLayer + (1 if lift-role, else 0)`. A strict refinement of `bLayer`:
the parity bit separates the two roles of a single layer, while `bRole / 2 = bLayer` recovers the layer.
The fine grading the interior-det headline's `hbt` consumes once aligned to the output side. -/
noncomputable def bRole (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (q : Fin (routeMAmbient M)) : ℕ :=
  2 * bLayer M t ha q +
    (if ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) q).snd.isRight then 1 else 0)

variable (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)

/-- **`bRole` refines `bLayer`**: `bRole q / 2 = bLayer q` — the role grading recovers the layer by
dropping the parity bit. Confirms `bRole` is a genuine refinement, not a re-encoding that loses the
layer filtration. -/
theorem bRole_div_two (q : Fin (routeMAmbient M)) : bRole M t ha q / 2 = bLayer M t ha q := by
  rw [bRole]
  split_ifs <;> omega

/-- **`bLayer` is monotone in `bRole`**: `bRole i < bRole j → bLayer i ≤ bLayer j`. The role grading's
order extends the layer order (a finer grading whose `<` only adds within-layer role splits, never
reverses the layer order). The bridge from a `bRole`-block-triangularity back to the `bLayer`
filtration. -/
theorem bLayer_le_of_bRole_lt {i j : Fin (routeMAmbient M)}
    (h : bRole M t ha i < bRole M t ha j) : bLayer M t ha i ≤ bLayer M t ha j := by
  rw [bRole, bRole] at h
  split_ifs at h <;> omega

/-! ## The role-refined reader locality (the strengthening of `RouteMLayerGrade.read*_indep_of`)

Each Schur reader reads a `Sum.inl` slot of layer `k`; each lift reader a `Sum.inr` slot. So a change
of `x` confined away from the reader's OWN role (at its layer) leaves it fixed — strictly stronger than
the `bLayer`-level `read*_indep_of` (which required agreement on the whole layer `k`). The slot's role
is read off `chartIdxEquiv (… .symm ⟨k, Sum.inl/inr ·⟩) = ⟨k, Sum.inl/inr ·⟩` (`apply_symm_apply`). -/

omit [CommRing 𝕜] in
/-- **The `K`-reader is invariant under changing `x` away from the Schur role of layer `k`.** The
reader's slot is a `Sum.inl` at layer `k`; agreement on every Schur-role coord of layer `k` fixes it. -/
theorem readK_indep_of_role (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → isSchurRole M t ha q → x q = y q)
    (i j : Fin (Text M t (k.val + 2))) :
    readK M t ha x k i j = readK M t ha y k i j := by
  rw [readK, readK]
  apply h
  · rw [bLayer, Equiv.apply_symm_apply]
  · rw [isSchurRole, Equiv.apply_symm_apply]; rfl

omit [CommRing 𝕜] in
/-- **The `X`-reader is invariant under changing `x` away from the Schur role of layer `k`.** -/
theorem readX_indep_of_role (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → isSchurRole M t ha q → x q = y q)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Text M t (k.val + 2))) :
    readX M t ha x k i j = readX M t ha y k i j := by
  rw [readX, readX]
  apply h
  · rw [bLayer, Equiv.apply_symm_apply]
  · rw [isSchurRole, Equiv.apply_symm_apply]; rfl

omit [CommRing 𝕜] in
/-- **The `N`-reader is invariant under changing `x` away from the Schur role of layer `k`.** -/
theorem readN_indep_of_role (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → isSchurRole M t ha q → x q = y q)
    (i : Fin (Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    readN M t ha x k i j = readN M t ha y k i j := by
  rw [readN, readN]
  apply h
  · rw [bLayer, Equiv.apply_symm_apply]
  · rw [isSchurRole, Equiv.apply_symm_apply]; rfl

omit [CommRing 𝕜] in
/-- **The `E`-reader is invariant under changing `x` away from the Schur role of layer `k`.** -/
theorem readE_indep_of_role (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → isSchurRole M t ha q → x q = y q)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    readE M t ha x k i j = readE M t ha y k i j := by
  rw [readE, readE]
  apply h
  · rw [bLayer, Equiv.apply_symm_apply]
  · rw [isSchurRole, Equiv.apply_symm_apply]; rfl

omit [CommRing 𝕜] in
/-- **The lift `W`-reader is invariant under changing `x` away from the lift role of layer `k`.**
Dually to the Schur readers: the lift reader's slot is a `Sum.inr` at layer `k`. -/
theorem readW_indep_of_role (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L) (hk : k.val + 1 < L)
    (h : ∀ q, bLayer M t ha q = k.val → isLiftRole M t ha q → x q = y q)
    (i : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M t ha x k hk i j = readW M t ha y k hk i j := by
  rw [readW, readW]
  apply h
  · rw [bLayer, Equiv.apply_symm_apply]
  · rw [isLiftRole, Equiv.apply_symm_apply]; rfl

/-! ## Non-vacuity: the roles are genuinely disjoint (zero within-layer 2-cycles at the reader level)

The role refinement is sound precisely because a coordinate is Schur-role XOR lift-role (the
`Sum.inl`/`Sum.inr` exclusivity). So the Schur readers and the lift reader of one layer read DISJOINT
coordinate sets, and the role grading has no within-layer back-edge between them. -/

omit [CommRing 𝕜] in
/-- **A coordinate is Schur-role XOR lift-role.** `Sum.isLeft`/`Sum.isRight` are exclusive, so no
coordinate is both — the within-layer role split is a genuine partition (no 2-cycle between the Schur
and lift roles). -/
theorem not_schur_and_lift (q : Fin (routeMAmbient M)) :
    ¬ (isSchurRole M t ha q ∧ isLiftRole M t ha q) := by
  rintro ⟨hs, hl⟩
  rw [isSchurRole] at hs
  rw [isLiftRole] at hl
  cases hc : ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) q).snd <;> simp_all

end DLNFibre.DLN.RLCT
