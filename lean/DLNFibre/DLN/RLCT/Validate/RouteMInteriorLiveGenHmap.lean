import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenChart

/-!
# `RouteMInteriorLiveGenHmap` — the general-`L` chart map identity `hmap` + differentiability + diffGen

The map-identity layer of the general-`L` interior-chart lift (`genm-glift`), generalizing the
`Fin (2 + 1)`-pinned `RouteMLeafBData.hmap_leaf` / `RouteMInteriorLiveContract.interiorLive_diff` to
arbitrary depth `L`. Uses this thread's chart-layer boundary factor `BparamsLeafGenC` / `BchartLeafGenC`
(`RouteMInteriorLiveGenChart`, `rfl`-equal to factor1's `RouteMInteriorLiveGenDet.BchartLeafGen`, kept
local so the chart layer is decoupled from that actively-churning module) and this thread's
`interiorLive_commuteGen` / `readX_pbo_all` / `readN_pbo_all` / `readW_pbo_all` / `readE_pbo_all`.

## The map identity

`phiFlatLiveAt M ha hL leafPivot = BchartLeafGenC ha ∘ pivotBlowupOn activeMGen leafPivot`. Both sides are
`paramsEquivFlat ∘ chartParamsGen`; the work is the per-layer chart-parameter match
`chartParamsGen_matchGen` (via `Agen_congr`, reducing each layer to the `Nblk`/`Wblk`/`Cgen(s+1)`
matches):

* interior boundary `s+1 < L`: `Cgen = schurFrameProd` (`Cgen_live_interior_eq_schurFrameProd`), the
  K/X/N blocks read spectator slots (fixed by `readK/X/N_pbo_all`), and the radial `u` of the E-term
  moves into the residual coordinate (`schurFrameProd_u_to_E` + `readE_pbo_all`);
* leaf boundary `s+1 = L`: `Cgen = v • rfin` (`Cgen_live_leaf`), the pivot `(0,0)` fixed and the rest
  scaled (`rfinFixedPivot`/`rfinDirectGenC` match under `pbo`).

The `Nblk (s)`/`Wblk (s)` at layer `s ≥ 1` read the INTERIOR boundary `s−1` (`≠ L−1`), fixed by
`readN/W_pbo_all`; at `s = 0` they are `0` (identity boundary).

* `Cgen_interior_matchGen` — the interior `Cgen (s+1 < L)` match.
* `Cgen_leaf_matchGen` — the leaf `Cgen (s+1 = L)` match.
* `chartParamsGen_matchGen` — the per-layer chart-parameter match.
* `hmap_leafGen` — the map identity.
* `Bchart_differentiableAtGen` — `BchartLeafGenC` differentiable (the polynomial chain).
* `interiorLive_diffGen` — `Differentiable (interiorLivePhiGen)` via the factorization + commute.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra + the banked wiring; only the
chain-rule differentiability, no other analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The leaf-slot scaling facts under `pbo` (general `L`) -/

/-- A leaf slot `(i, j) ≠ (0, 0)` is `≠ leafPivot` (`leafSlot` injective in `(i, j)`) — general `L`. -/
theorem leafSlot_ne_leafPivotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (i : Fin (Text M (tach M) L)) (j : Fin (Wext M L)) (hij : ¬ (i.val = 0 ∧ j.val = 0)) :
    leafSlot M (tach M) ha hL i j ≠ leafPivot M ha hL h0r h0c := by
  rw [← leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c]
  intro h
  obtain ⟨hi, hj⟩ := leafSlot_inj M (tach M) ha hL h
  exact hij ⟨by simp [hi], by simp [hj]⟩

/-! ## The interior + leaf `Cgen` matches (per layer) -/

/-- **The interior `Cgen (s+1 < L)` match** at general `L`: the chart's interior transition (radial
`u = x p₀`, leaf `rfinFixedPivot x`) equals the `B`-decoder's (radial `1`, leaf
`rfinDirectGenC (pbo x)`) at every interior boundary `s+1 < L`. Both are the Schur frame
(`Cgen_live_interior_eq_schurFrameProd`); the K/X/N blocks read spectator slots (fixed via
`readK/X/N_pbo_all`), and the radial `u` of the E-term moves into the residual coordinate
(`schurFrameProd_u_to_E` + `readE_pbo_all`). The general-`L` lift of `RouteMLeafBData.Cgen1_match`. -/
theorem Cgen_interior_matchGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (s : ℕ) (hs1 : s + 1 < L) :
    Cgen (x (leafPivot M ha hL h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinFixedPivot M ha hL x) x) (hleStruct M (tach M) ha) (s + 1)
      = Cgen 1 M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinDirectGenC M ha (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x))
          (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x))
        (hleStruct M (tach M) ha) (s + 1) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  have hsL : s < L := by omega
  have hsne : (⟨s, hsL⟩ : Fin L).val ≠ L - 1 := by simp only [Fin.val_mk]; omega
  rw [Cgen_live_interior_eq_schurFrameProd M (tach M) ha _ _ x s (by omega),
    Cgen_live_interior_eq_schurFrameProd M (tach M) ha _ _ (pbo x) s (by omega),
    schurFrameProd_u_to_E M (tach M) (s + 1) _ _ (x p₀)]
  congr 1
  · funext i j; exact (readK_pbo_all M ha hL h0r h0c x ⟨s, hsL⟩ i j).symm
  · funext i j; exact (readX_pbo_all M ha hL h0r h0c x ⟨s, hsL⟩ hsne i j).symm
  · funext i j; exact (readN_pbo_all M ha hL h0r h0c x ⟨s, hsL⟩ hsne i j).symm
  · funext i j
    rw [Matrix.smul_apply, smul_eq_mul, readE_pbo_all M ha hL h0r h0c x ⟨s, hsL⟩ hsne i j]

/-- **The leaf `Cgen L` match** at general `L`: `(x p₀) • rfinFixedPivot x = 1 • rfinDirectGenC (pbo x)`
(boundary `L`). At the pivot `(0,0)`: `(x p₀)·1 = (pbo x) p₀ = x p₀` (pivot fixed); off `(0,0)`:
`(x p₀)·x(leafSlot i j) = (pbo x)(leafSlot i j)` (a leaf slot in `activeMGen`, `≠ p₀`, scaled). The
general-`L` lift of `RouteMLeafBData.Cgen2_match`. -/
theorem Cgen_leaf_matchGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    Cgen (x (leafPivot M ha hL h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinFixedPivot M ha hL x) x) (hleStruct M (tach M) ha) L
      = Cgen 1 M (tach M)
        (genBlkFlatLive M (tach M) ha
          (rfinDirectGenC M ha (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x))
          (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x))
        (hleStruct M (tach M) ha) L := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  rw [Cgen_live_leaf M (tach M) ha (rfinFixedPivot M ha hL x) (x p₀) x,
    Cgen_live_leaf M (tach M) ha (rfinDirectGenC M ha (pbo x)) (1 : ℝ) (pbo x), one_smul]
  funext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · -- the pivot entry: both sides are `x p₀`
    obtain ⟨hi, hj⟩ := hij
    have hi' : i = ⟨0, h0r⟩ := Fin.ext hi
    have hj' : j = ⟨0, h0c⟩ := Fin.ext hj
    subst hi' hj'
    rw [rfinFixedPivot_pivot M ha hL h0r h0c, mul_one]
    show x p₀ = pbo x (leafSlot M (tach M) ha hL ⟨0, h0r⟩ ⟨0, h0c⟩)
    rw [show leafSlot M (tach M) ha hL ⟨0, h0r⟩ ⟨0, h0c⟩ = p₀ from
        leafSlot_zero_eq_leafPivotGen M ha hL h0r h0c, hpbo, pivotBlowupOn, if_pos rfl]
  · -- a non-pivot leaf entry: `(x p₀)·x(leafSlot i j) = pbo x (leafSlot i j)`
    rw [rfinFixedPivot_off M ha hL x i j hij]
    show x p₀ * x (leafSlot M (tach M) ha hL i j)
      = pbo x (leafSlot M (tach M) ha hL i j)
    rw [hpbo, pivotBlowupOn, if_neg (leafSlot_ne_leafPivotGen M ha hL h0r h0c i j hij),
      if_pos (leafSlot_mem_activeMGen M ha i j)]

/-! ## The `Nblk` / `Wblk` matches (spectator, at the interior boundary `s−1`) -/

/-- The genBlkFlatLive `Nblk (s)` reads `readN ⟨s−1⟩` (`s = j+1`, `j < L`); the spectator match under
`pbo` (`readN_pbo_all`, at the interior boundary `⟨j⟩ ≠ L−1`). -/
theorem live_Nblk_matchGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (j : ℕ) (hj1 : j + 1 < L) :
    (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x).Nblk (j + 1)
      = (genBlkFlatLive M (tach M) ha
          (rfinDirectGenC M ha (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x))
          (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x)).Nblk (j + 1) := by
  have hjL : j < L := by omega
  have hjne : (⟨j, hjL⟩ : Fin L).val ≠ L - 1 := by simp only [Fin.val_mk]; omega
  rw [genBlkFlatLive_Nblk_succ M (tach M) ha _ x j hjL,
    genBlkFlatLive_Nblk_succ M (tach M) ha _ _ j hjL]
  funext i k; exact (readN_pbo_all M ha hL h0r h0c x ⟨j, hjL⟩ hjne i k).symm

/-- The genBlkFlatLive `Wblk (s)` is the structured decoder's `Wblk`; the spectator match under `pbo`
(`readW_pbo_all`, at the interior boundary `⟨j⟩` with a lift `j+1 < L`). -/
theorem live_Wblk_matchGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ)
    (j : ℕ) (hj1 : j + 1 < L) :
    (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x).Wblk (j + 1)
      = (genBlkFlatLive M (tach M) ha
          (rfinDirectGenC M ha (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x))
          (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x)).Wblk (j + 1) := by
  have hjL : j < L := by omega
  show (genBlkFlatStruct M (tach M) ha x).Wblk (j + 1)
    = (genBlkFlatStruct M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x)).Wblk (j + 1)
  simp only [genBlkFlatStruct, dif_pos hjL, dif_pos hj1]
  funext i k; exact (readW_pbo_all M ha hL h0r h0c x ⟨j, hjL⟩ hj1 i k).symm

/-! ## The chart-parameter match + `hmap` -/

/-- **The chart-parameter match at general `L`** `chartParamsGen (x p₀) … (chart decoder) =
BparamsLeafGenC (pbo x)` — the genuine content of `hmap`, per layer `s : Fin L`. Both are `reindex (Agen
… s.val)`; `Agen_congr` reduces each to the `Nblk`/`Wblk`/`Cgen(s+1)` matches. Layer `0` reads
`Nblk 0 = 0` (`rfl`) and the interior `Cgen 1`; layer `s ≥ 1` reads the interior boundary `s−1`'s
`Nblk`/`Wblk`; the `Cgen (s+1)` is interior when `s+1 < L`, the leaf when `s+1 = L`. The general-`L`
lift of `RouteMLeafBData.chartParamsGen_match`. -/
theorem chartParamsGen_matchGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (x : Fin (routeMAmbient M) → ℝ) :
    chartParamsGen (x (leafPivot M ha hL h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x)
        (hleStruct M (tach M) ha)
      = BparamsLeafGenC M ha (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  rw [BparamsLeafGenC]
  funext s
  show Matrix.reindex _ _ (Agen (x p₀) M (tach M) _ (hleStruct M (tach M) ha) s.val)
    = Matrix.reindex _ _ (Agen 1 M (tach M) _ (hleStruct M (tach M) ha) s.val)
  congr 1
  -- the `Nblk`/`Wblk`/`Cgen(s+1)` matches per layer `s`.
  -- Nblk s: `0` at `s = 0`, `readN ⟨s−1⟩` at `s ≥ 1` (interior, `≠ L−1`).
  have hN : (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x).Nblk s.val
      = (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha (pbo x)) (pbo x)).Nblk s.val := by
    match hsv : s.val with
    | 0 => rfl
    | (j + 1) =>
      have hj1 : j + 1 < L := by have := s.isLt; omega
      exact live_Nblk_matchGen M ha hL h0r h0c x j hj1
  have hW : (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x).Wblk s.val
      = (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha (pbo x)) (pbo x)).Wblk s.val := by
    match hsv : s.val with
    | 0 => rfl
    | (j + 1) =>
      have hj1 : j + 1 < L := by have := s.isLt; omega
      exact live_Wblk_matchGen M ha hL h0r h0c x j hj1
  have hC : Cgen (x p₀) M (tach M) (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x)
        (hleStruct M (tach M) ha) (s.val + 1)
      = Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha (pbo x)) (pbo x))
        (hleStruct M (tach M) ha) (s.val + 1) := by
    by_cases hsL : s.val + 1 < L
    · exact Cgen_interior_matchGen M ha hL h0r h0c x s.val hsL
    · -- `s.val + 1 = L` (since `s.val < L`): the leaf boundary.
      have hsL' : s.val + 1 = L := by have := s.isLt; omega
      rw [hsL']
      exact Cgen_leaf_matchGen M ha hL h0r h0c x
  exact Agen_congr M (tach M) (hleStruct M (tach M) ha) (x p₀) 1 _ _ s.val hN hW hC

/-- **`hmap_leafGen`**: `phiFlatLiveAt M ha hL p₀ = BchartLeafGenC ha ∘ pivotBlowupOn activeMGen p₀` at
general `L` — the map id, discharged from the per-layer match (`chartParamsGen_matchGen`; NO explicit
`chainA` reindexing). Both sides are `paramsEquivFlat ∘ chartParamsGen`. The general-`L` lift of
`RouteMLeafBData.hmap_leaf`. -/
theorem hmap_leafGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    phiFlatLiveAt M ha hL (leafPivot M ha hL h0r h0c)
      = BchartLeafGenC M ha ∘ pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) := by
  funext x
  show phiGen (x (leafPivot M ha hL h0r h0c)) M (tach M)
      (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x)
      (hleStruct M (tach M) ha) = _
  show paramsEquivFlat M
      (chartParamsGen (x (leafPivot M ha hL h0r h0c)) M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha hL x) x)
        (hleStruct M (tach M) ha)) = _
  rw [chartParamsGen_matchGen M ha hL h0r h0c x]
  rfl

/-! ## `BchartLeafGenC` differentiability (the polynomial chain, general `L`) -/

/-- `rfinDirectGenC ha` is differentiable (a linear matrix coordinate read) — general `L`. -/
theorem diffAt_rfinDirectGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (u : Fin (routeMAmbient M) → ℝ) :
    DifferentiableAt ℝ (fun y => rfinDirectGenC M ha y) u := by
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  exact differentiableAt_apply _ u

/-- The `genBlkFlatLive` decoder's `Cgen` (radial `1`, leaf `rfinDirectGenC`) is differentiable at each
`k` — general `L`. The general-`L` lift of `RouteMLeafBData.diffAt_Cgen_live` (`by_cases hk : k < L`,
not `< 2`). -/
theorem diffAt_Cgen_liveGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) :
    DifferentiableAt ℝ
      (fun y => Cgen (1 : ℝ) M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y) (hleStruct M (tach M) ha) k) u := by
  by_cases hk : k < L
  · rw [show (fun y => Cgen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y) (hleStruct M (tach M) ha) k)
        = fun y => (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Bmat k
            * chainQ (genWidthEq M (tach M) (hleStruct M (tach M) ha) k hk)
              ((genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Nblk k)
            + (1 : ℝ) • (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Rmat k from by
      funext y; rw [Cgen, dif_pos hk]]
    refine (DifferentiableAt.matMul ?_ (diffAt_chainQ _ _ u ?_)).add
      (DifferentiableAt.const_smul ?_ (1 : ℝ))
    · match k with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < L
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Bmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]
          exact diffAt_bmatStack M (tach M) (j + 1) (ha.hdesc j hj) _ _ u
            (diffAt_readK M (tach M) ha ⟨j, hj⟩ u) (diffAt_readX M (tach M) ha ⟨j, hj⟩ u)
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Bmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
    · match k with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < L
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]; exact diffAt_readN M (tach M) ha ⟨j, hj⟩ u
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
    · match k with
      | 0 =>
        show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Rmat 0) u
        exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < L
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Rmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]
          exact diffAt_rmatPad M (tach M) (j + 1) (ha.hdesc j hj) (ha.hub j) _ u
            (diffAt_readE M (tach M) ha ⟨j, hj⟩ u)
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Rmat (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
  · rw [show (fun y => Cgen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y) (hleStruct M (tach M) ha) k)
        = fun y => (1 : ℝ) • (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Rfin k from by
      funext y; rw [Cgen, dif_neg hk]]
    refine DifferentiableAt.const_smul ?_ (1 : ℝ)
    by_cases hkL : k = L
    · subst hkL
      rw [show (fun y => (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Rfin k)
          = fun y => rfinDirectGenC M ha y from by funext y; simp [genBlkFlatLive]]
      exact diffAt_rfinDirectGen M ha u
    · rw [show (fun y => (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Rfin k)
          = fun _ => 0 from by funext y; simp only [genBlkFlatLive, dif_neg hkL]]
      exact differentiableAt_const _

/-- The `genBlkFlatLive` decoder's `Agen` (radial `1`) is differentiable at each `s` — general `L`. -/
theorem diffAt_Agen_liveGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (u : Fin (routeMAmbient M) → ℝ) (s : ℕ) :
    DifferentiableAt ℝ
      (fun y => Agen (1 : ℝ) M (tach M)
        (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y) (hleStruct M (tach M) ha) s) u := by
  by_cases hs : s < L
  · rw [show (fun y => Agen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y) (hleStruct M (tach M) ha) s)
        = fun y => chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s hs)
            ((genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Nblk s)
            ((genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y).Wblk s)
            (Cgen (1 : ℝ) M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y)
              (hleStruct M (tach M) ha) (s + 1)) from by funext y; rw [Agen, dif_pos hs]]
    refine diffAt_chainA _ _ _ _ u ?_ ?_ (diffAt_Cgen_liveGen M ha u (s + 1))
    · match s with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < L
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_pos hj]; exact diffAt_readN M (tach M) ha ⟨j, hj⟩ u
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Nblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
    · match s with
      | 0 => exact differentiableAt_const _
      | (j + 1) =>
        by_cases hj : j < L
        · by_cases hj2 : j + 1 < L
          · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Wblk (j + 1)) u
            simp only [genBlkFlatStruct, dif_pos hj, dif_pos hj2]
            exact diffAt_readW M (tach M) ha ⟨j, hj⟩ hj2 u
          · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Wblk (j + 1)) u
            simp only [genBlkFlatStruct, dif_pos hj, dif_neg hj2]; exact differentiableAt_const _
        · show DifferentiableAt ℝ (fun y => (genBlkFlatStruct M (tach M) ha y).Wblk (j + 1)) u
          simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _
  · rw [show (fun y => Agen (1 : ℝ) M (tach M)
          (genBlkFlatLive M (tach M) ha (rfinDirectGenC M ha y) y) (hleStruct M (tach M) ha) s)
        = fun _ => 0 from by funext y; rw [Agen, dif_neg hs]]
    exact differentiableAt_const _

/-- **`BchartLeafGenC` is differentiable** at general `L` — the chain is polynomial in `y` (radial `1`,
linear reads). Mirrors `RouteMLeafBData.Bchart_differentiableAt`: reduce through the linear CLE
`paramsEquivFlat`, the `Params` Pi, and the per-component `reindex`, leaving the per-layer
`diffAt_Agen_liveGen`. -/
theorem Bchart_differentiableAtGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (u : Fin (routeMAmbient M) → ℝ) :
    DifferentiableAt ℝ (BchartLeafGenC M ha) u := by
  have hchart : DifferentiableAt ℝ (fun y => BparamsLeafGenC M ha y) u := by
    apply differentiableAt_pi.mpr
    intro s
    exact diffAt_reindex_finCongr _ _ _ u (diffAt_Agen_liveGen M ha u s.val)
  have hlin : DifferentiableAt ℝ (fun P => paramsEquivFlat M P) (BparamsLeafGenC M ha u) := by
    have hd := (paramsEquivFlatCLE M).differentiableAt (x := BparamsLeafGenC M ha u)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards with P; rw [paramsEquivFlatCLE_coe]
  exact hlin.comp u hchart

/-! ## Differentiability of `kLDU` / `pivotBlowupOn` (generic, `_gen`-named to avoid the L=2 clash) -/

/-- **`kLens` is differentiable** — `matrixSplit.symm ∘ lduCoreMap ∘ matrixSplit`. (Generic; a `_gen`
copy of `RouteMInteriorLiveContract.differentiable_kLens` to keep this general-`L` module free of the
L=2 contract import.) -/
theorem differentiable_kLensGen {t : ℕ} : Differentiable ℝ (kLens (t := t)) := by
  have hlduc : Differentiable ℝ (lduCoreMap (t := t)) :=
    fun z => (lduCoreMap_hasFDerivAt z).differentiableAt
  intro K
  unfold kLens
  exact (matrixSplit.symm.toContinuousLinearEquiv.differentiable _).comp K
    ((hlduc _).comp K (matrixSplit.toContinuousLinearEquiv.differentiable K))

/-- **`kLDU` is differentiable** (generic; a `_gen` copy). -/
theorem differentiable_kLDUGen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) :
    Differentiable ℝ (kLDU M t ha) := by
  apply differentiable_pi.mpr
  intro q
  unfold kLDU
  split
  · rename_i k s heq
    split
    · rename_i qK hfeq
      have hrk : Differentiable ℝ
          (fun x : Fin (routeMAmbient M) → ℝ => Matrix.of (readK M t ha x k)) := by
        apply differentiable_pi.mpr; intro i; apply differentiable_pi.mpr; intro j
        exact differentiable_apply _
      have hcomp : Differentiable ℝ
          (fun x : Fin (routeMAmbient M) → ℝ => kLens (Matrix.of (readK M t ha x k))) :=
        fun x => (differentiable_kLensGen _).comp x (hrk x)
      exact differentiable_pi.mp (differentiable_pi.mp hcomp (finProdFinEquiv.symm qK).1)
        (finProdFinEquiv.symm qK).2
    · exact differentiable_apply _
  · exact differentiable_apply _

/-- **`pivotBlowupOn` is differentiable** (generic; a `_gen` copy). -/
theorem differentiable_pivotBlowupOnGen {N : ℕ} (active : Finset (Fin N)) (p : Fin N) :
    Differentiable ℝ (pivotBlowupOn active p) :=
  fun x => (hasFDerivWithinAt_univ.mp
    (pivotBlowupOn_hasFDerivWithinAt active p Set.univ x)).differentiableAt

/-! ## `interiorLive_diffGen` — the full chart is differentiable -/

/-- **`interiorLive_diffGen`** — `interiorLivePhiGen` is a polynomial chain, differentiable everywhere.
Via the factorization `interiorLivePhiGen = (BchartLeafGenC ∘ kLDU) ∘ pbo` (from `hmap_leafGen` at
`kLDU x` + the commute `interiorLive_commuteGen`), each factor differentiable
(`Bchart_differentiableAtGen`, `differentiable_kLDU`, `differentiable_pivotBlowupOn`). The general-`L`
lift of `RouteMInteriorLiveContract.interiorLive_diff`. -/
theorem interiorLive_diffGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Differentiable ℝ (interiorLivePhiGen M ha hL h0r h0c) := by
  have hfact : interiorLivePhiGen M ha hL h0r h0c
      = (fun y => BchartLeafGenC M ha (kLDU M (tach M) ha y))
        ∘ pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) := by
    funext x
    rw [interiorLivePhiGen, hmap_leafGen M ha hL h0r h0c]
    show BchartLeafGenC M ha (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c)
      (kLDU M (tach M) ha x)) = _
    rw [interiorLive_commuteGen M ha hL h0r h0c x]; rfl
  rw [hfact]
  refine Differentiable.comp ?_ (differentiable_pivotBlowupOnGen (activeMGen M ha) _)
  exact fun y => ((fun u => Bchart_differentiableAtGen M ha u) _).comp y
    (differentiable_kLDUGen M (tach M) ha y)

end DLNFibre.DLN.RLCT
