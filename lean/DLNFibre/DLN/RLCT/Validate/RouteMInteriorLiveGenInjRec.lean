import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenInj

/-!
# `RouteMInteriorLiveGenInjRec` — the general-`L` `BchartLeafGen`-recovery (closes `injOnGen`'s residual)

The value-map injectivity side of the shared per-boundary Schur-frame object (parallel to Factor 1's
`eihd_hD_gen`, which is the fderiv/det side). Closes `interiorLive_BchartLeaf_injOnGen` — the last sorry
of the general-`L` interior-chart lift — by the BOUNDED triangular forward-substitution the verify-first
verdict identified.

## The recovery (route (a), eInGen-assembled)

On the all-coords-nonzero `kLDU ∘ pbo` image `y = kLDU(pbo x)` (so `det (readK y k) ≠ 0` at every
interior `k`, banked-adjacent), from `BchartLeafGen y = BchartLeafGen y'`:

1. `paramsEquivFlat` injective + `reindexLs_BparamsLeafGen` (banked) ⟹ `Agen 1 (…y) s = Agen 1 (…y') s`
   at every `s : Fin L`.
2. Per boundary `s`, `Agen … s = chainA(Nblk s, Wblk s, Cgen(s+1)) = [Cgen(s+1) − Nblk s·Wblk s ; Wblk s]`
   (`chainA_apply_castAdd`/`_natAdd`): the lift rows give `Wblk s = readW`, and — with `Nblk s = readN
   ⟨s-1⟩` recovered at the strictly-earlier layer `s-1` — the kept rows give `Cgen(s+1)`, which is
   `schurFrameProd(K,X,N,E)_s` (interior) / `rfin` (leaf), inverted by `schurFrameMap_inj_of_det_ne_zero`
   with `det K_s ≠ 0`. This is TRIANGULAR forward-substitution (acyclic `layer s ← layer s-1`).
3. The per-boundary reader equality is reassembled to `y = y'` via `eInGen` (Factor 1's banked
   layer-collecting `LinearEquiv`, injective by construction) — the eInGen-reuse closer.

Shares the per-boundary Schur-frame OBJECT (`frameToSchurIncGen`, `schurFrameMap`) + the `det K ≠ 0`
GATE with Factor 1's `eihd_hD_gen`; this is the DISTINCT value-map assembly (Factor 1's is the fderiv
block-form). Coordinated via genm-glift: this thread edits here; Factor 1's replacement edits GenDet.

Axiom-clean target `[propext, Classical.choice, Quot.sound]` (matrix algebra + banked equivs; no
analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## SPECIFY skeleton — signatures first, `sorry` bodies (validate the interfaces, then fill) -/

/-- **det-K gate** — on the `kLDU ∘ pbo` all-nonzero image, `det (readK y k) ≠ 0` at every `k : Fin L`.
The banked-adjacent `readK_kLDU_det = ∏ pivots`, each pivot `= (pbo x)(diagAxis) ≠ 0` via
`readK_pbo_all` on the all-nonzero domain. -/
theorem detK_ne_zero_of_mem (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    {y : Fin (routeMAmbient M) → ℝ}
    (hy : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (k : Fin L) :
    (Matrix.of (readK M (tach M) ha y k)).det ≠ 0 := by
  obtain ⟨z, ⟨x₀, hx₀, rfl⟩, rfl⟩ := hy
  have hpbo_ne : ∀ q, pivotBlowupOn (activeMGen M ha)
      (leafPivot M ha hL h0r h0c) x₀ q ≠ 0 := by
    intro q
    have hall : ∀ j, x₀ j ≠ 0 := hx₀.2
    rw [pivotBlowupOn]
    split
    · exact hall _
    · split
      · exact mul_ne_zero (hall _) (hall _)
      · exact hall _
  rw [readK_kLDU_det M (tach M) ha _ k, Finset.prod_ne_zero_iff]
  intro i _
  -- `(matrixSplit (readK (pbo x₀) k)).2.1 i` is the diagonal `readK (pbo x₀) k i i = (pbo x₀)(slot) ≠ 0`
  show (Matrix.of (readK M (tach M) ha
    (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x₀) k)) i i ≠ 0
  rw [Matrix.of_apply, readK]
  exact hpbo_ne _

/-- **`BchartLeafGen`-equality ⟹ `Agen`-equality** at every layer `s : Fin L` — `paramsEquivFlat`
injective + the banked per-layer bridge `reindexLs_BparamsLeafGen` (a reindex, injective). -/
theorem Agen_eq_of_BchartLeafGen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    {y y' : Fin (routeMAmbient M) → ℝ}
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') (s : Fin L) :
    Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
        (hleStruct M (tach M) ha) s.val
      = Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y')
        (hleStruct M (tach M) ha) s.val := by
  -- `BchartLeafGen = paramsEquivFlat ∘ BparamsLeafGen`; peel the equiv, take the `s`-component,
  -- then `reindexLs_BparamsLeafGen` (a `reindex`, injective) recovers the `Agen` layer.
  have hP : BparamsLeafGen M ha y = BparamsLeafGen M ha y' :=
    (paramsEquivFlat M).injective heq
  have hPs := congrFun hP s
  rw [← reindexLs_BparamsLeafGen M ha y s, ← reindexLs_BparamsLeafGen M ha y' s] at hPs
  exact (Matrix.reindex _ _).injective hPs

/-- **`Wblk` recovery** (the lift rows of `Agen … s`): from `Agen … s`-equality, `readW y ⟨s⟩ = readW y'
⟨s⟩` at an interior `s+1 < L`. The `chainA_apply_natAdd` lift-block read. -/
theorem readW_eq_of_Agen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    {y y' : Fin (routeMAmbient M) → ℝ} (s : Fin L) (hs : s.val + 1 < L)
    (hA : Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
        (hleStruct M (tach M) ha) s.val
      = Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y')
        (hleStruct M (tach M) ha) s.val) :
    readW M (tach M) ha y s hs = readW M (tach M) ha y' s hs := by
  sorry

/-- **`Cgen(s+1)` recovery** (the kept rows of `Agen … s`): from `Agen … s`-equality + `readN ⟨s-1⟩`
equality (giving `Nblk s`-equality) + `readW` equality (`Wblk s`), the interior transition
`Cgen(s+1) = schurFrameProd(K,X,N,E)_s` agrees for `y`, `y'`. The `chainA_apply_castAdd` kept-block read
+ the `− Nblk s·Wblk s` subtraction. -/
theorem Cgen_eq_of_Agen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    {y y' : Fin (routeMAmbient M) → ℝ} (s : Fin L) (hs : s.val + 1 < L)
    (hA : Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
        (hleStruct M (tach M) ha) s.val
      = Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y')
        (hleStruct M (tach M) ha) s.val)
    (hN : (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y).Nblk s.val
      = (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y').Nblk s.val)
    (hW : (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y).Wblk s.val
      = (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y').Wblk s.val) :
    Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
        (hleStruct M (tach M) ha) (s.val + 1)
      = Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y')
        (hleStruct M (tach M) ha) (s.val + 1) := by
  sorry

/-- **Interior frame recovery `frameRecoverGen`** — at an interior `s+1 < L`, from the `Cgen(s+1)`
equality (`= schurFrameProd`) + `det K_s ≠ 0`, the four readers `readK/X/N/E ⟨s⟩` agree for `y`, `y'`.
Via `Cgen_live_interior_eq_schurFrameProd` + `schurFrameMap_inj_of_det_ne_zero` (through the general-`s`
`flatBlock_schurFrameMap_eq` bridge). -/
theorem frameRecoverGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    {y y' : Fin (routeMAmbient M) → ℝ} (s : Fin L) (hs : s.val + 1 < L)
    (hK : (Matrix.of (readK M (tach M) ha y s)).det ≠ 0)
    (hC : Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
        (hleStruct M (tach M) ha) (s.val + 1)
      = Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y')
        (hleStruct M (tach M) ha) (s.val + 1)) :
    readK M (tach M) ha y s = readK M (tach M) ha y' s
      ∧ readX M (tach M) ha y s = readX M (tach M) ha y' s
      ∧ readN M (tach M) ha y s = readN M (tach M) ha y' s
      ∧ readE M (tach M) ha y s = readE M (tach M) ha y' s := by
  sorry

/-- **The recovery capstone** — `BchartLeafGen` injective on the `kLDU ∘ pbo` image. The forward
induction over `s : Fin L` (frameRecover, `Nblk s = readN⟨s-1⟩` from the prior step) + the eInGen-reuse
closer. Closes `interiorLive_BchartLeaf_injOnGen`. -/
theorem BchartLeafGen_injOn_recover (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Set.InjOn (BchartLeafGen M ha)
      (kLDU M (tach M) ha
        '' (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c)
          '' interiorLiveInjDomGen M ha hL h0r h0c)) := by
  sorry

end DLNFibre.DLN.RLCT
