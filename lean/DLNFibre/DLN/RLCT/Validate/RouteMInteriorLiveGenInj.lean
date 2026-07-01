import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenHmap
import DLNFibre.DLN.RLCT.Validate.RouteMLDUUniqueness

/-!
# `RouteMInteriorLiveGenInj` — the general-`L` interior-chart injectivity `interiorLive_injOnGen`

The injectivity layer of the general-`L` interior-chart lift (`genm-glift`), generalizing the
`Fin (2 + 1)`-pinned `RouteMInteriorLiveContract.interiorLive_injOn`. The GENERIC kLDU-injectivity
chain (`kLens_injOn_qneGen` / `readK_eq_of_kLDU_eqGen` / `kLDU_injStep2Gen` / `kLDU_inj_of_nonzeroGen`
/ `interiorLive_kLDU_injOnGen`) is fully general-`L` and lands here. The `BchartLeafGen`-recovery half
(the per-boundary Schur-frame inversion, the L=2 `slotReadV0` / `rsL1` / `schurFrameMap_inj` chain) is
the SAME per-boundary geometry factor1's `eihd_hD_gen` builds — it is the load-bearing residual, left
as an isolated `sorry` (`interiorLive_BchartLeaf_injOnGen`) with a precise note; everything else is
sorry-free.

The injectivity factorization is `interiorLivePhiGen = (BchartLeafGen ∘ kLDU) ∘ pbo` (`hmap_leafGen` +
`interiorLive_commuteGen`); `pbo` injective off `{u leafPivot = 0}` (banked `pivotBlowupOn_injOn`);
`kLDU` injective on the blown-up all-nonzero image (`interiorLive_kLDU_injOnGen`, general-`L`, DONE);
`BchartLeafGen` injective on the kLDU-image (`interiorLive_BchartLeaf_injOnGen`, the residual).

Axiom-clean for the kLDU chain `[propext, Classical.choice, Quot.sound]`; the `BchartLeafGen`-recovery
sorry is isolated in `interiorLive_BchartLeaf_injOnGen` (hence `interiorLive_injOnGen`).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The generic kLDU-injectivity chain (fully general-`L`) -/

/-- **`kLens` injective off the q-pivots** (generic; a `_gen` copy of
`RouteMInteriorLiveContract.kLens_injOn_qne`) — peel the two `matrixSplit` LinearEquivs, then
`lduCore_unique` recovers `(l,q,u)` when the diagonal pivots `q` are nonzero. -/
theorem kLens_injOn_qneGen {t : ℕ} (K K' : Matrix (Fin t) (Fin t) ℝ)
    (hq : ∀ i, (matrixSplit K).2.1 i ≠ 0) (hk : kLens K = kLens K') : K = K' := by
  rw [kLens, kLens] at hk
  have hldu : lduCoreMap (matrixSplit K) = lduCoreMap (matrixSplit K') :=
    matrixSplit.symm.injective hk
  rw [lduCoreMap, lduCoreMap] at hldu
  obtain ⟨hl, hqq, hu⟩ :=
    RouteMLDUUniqueness.lduCore_unique _ _ _ _ _ _ hq (matrixSplit.injective hldu)
  exact matrixSplit.injective (Prod.ext hl (Prod.ext hqq hu))

/-- **Step 1 of kLDU injectivity — `readK` is recovered at EVERY boundary `k : Fin L`.** The general-`L`
lift of `readK_eq_of_kLDU_eq` (the `Fin 2` bound loosened to `Fin L`). -/
theorem readK_eq_of_kLDU_eqGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ) (hqy : ∀ q, y q ≠ 0)
    (hkeq : kLDU M (tach M) ha y = kLDU M (tach M) ha y') (k : Fin L) :
    Matrix.of (readK M (tach M) ha y k) = Matrix.of (readK M (tach M) ha y' k) := by
  have hkl : kLens (Matrix.of (readK M (tach M) ha y k))
      = kLens (Matrix.of (readK M (tach M) ha y' k)) := by
    have hbridge : ∀ (z : Fin (routeMAmbient M) → ℝ),
        Matrix.of (readK M (tach M) ha (kLDU M (tach M) ha z) k)
          = kLens (Matrix.of (readK M (tach M) ha z k)) := by
      intro z; ext i j; exact readK_kLDU M (tach M) ha z k i j
    rw [← hbridge y, ← hbridge y', hkeq]
  refine kLens_injOn_qneGen _ _ (fun i => ?_) hkl
  show (Matrix.of (readK M (tach M) ha y k)) i i ≠ 0
  rw [Matrix.of_apply, readK]; exact hqy _

/-- **Step 2 of kLDU injectivity — the per-coordinate recovery at general `L`.** The general-`L` lift of
`kLDU_injStep2` (`hRKall : ∀ k : Fin L`). -/
theorem kLDU_injStep2Gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ)
    (hRKall : ∀ k : Fin L,
      Matrix.of (readK M (tach M) ha y k) = Matrix.of (readK M (tach M) ha y' k))
    (hkeq : kLDU M (tach M) ha y = kLDU M (tach M) ha y') (q : Fin (routeMAmbient M)) :
    y q = y' q := by
  have hq := congrFun hkeq q
  rw [kLDU, kLDU] at hq
  match hc : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with
  | ⟨k, Sum.inl s⟩ =>
    rw [hc] at hq; simp only at hq
    match heqf : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      have hslot : ∀ z : Fin (routeMAmbient M) → ℝ,
          z q = readK M (tach M) ha z k (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 := by
        intro z; rw [readK, Prod.mk.eta, finProdFinEquiv.apply_symm_apply qK,
          ← heqf, Equiv.symm_apply_apply, ← hc, Equiv.symm_apply_apply]
      rw [hslot y, hslot y']
      exact congrFun (congrFun (Matrix.of.injective (hRKall k))
        (finProdFinEquiv.symm qK).1) (finProdFinEquiv.symm qK).2
    | Sum.inl (Sum.inl (Sum.inr e)) => rw [heqf] at hq; exact hq
    | Sum.inl (Sum.inr e) => rw [heqf] at hq; exact hq
    | Sum.inr e => rw [heqf] at hq; exact hq
  | ⟨k, Sum.inr s⟩ => rw [hc] at hq; simp only at hq; exact hq

/-- **`kLDU` injective off the zero locus at general `L`** — the general-`L` lift of
`kLDU_inj_of_nonzero`. -/
theorem kLDU_inj_of_nonzeroGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ)
    (hqy : ∀ q, y q ≠ 0) (hkeq : kLDU M (tach M) ha y = kLDU M (tach M) ha y') : y = y' := by
  funext q
  exact kLDU_injStep2Gen M ha y y' (fun k => readK_eq_of_kLDU_eqGen M ha y y' hqy hkeq k) hkeq q

/-! ## The injectivity domain (all coords nonzero) -/

/-- The general-`L` injectivity domain — `{u | u leafPivot ≠ 0 ∧ ∀ j, u j ≠ 0}` (the L=2 `E = univ`
choice: all coords nonzero, exactly what `kLens_injOn_qneGen` needs). -/
def interiorLiveInjDomGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) : Set (Fin (routeMAmbient M) → ℝ) :=
  {u | u (leafPivot M ha hL h0r h0c) ≠ 0 ∧ ∀ j, u j ≠ 0}

/-- **kLDU injective on `pbo '' injDom`** (general-`L`) — the `injDom` forces ALL coords nonzero;
`pivotBlowupOn` preserves that (scales by `x₀ leafPivot ≠ 0`), so `kLDU_inj_of_nonzeroGen` recovers the
blown-up point, then `pivotBlowupOn_injOn` recovers the source. The general-`L` lift of
`interiorLive_kLDU_injOn`. -/
theorem interiorLive_kLDU_injOnGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Set.InjOn (kLDU M (tach M) ha)
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c)
        '' interiorLiveInjDomGen M ha hL h0r h0c) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  have hpbo_ne : ∀ x₀ : Fin (routeMAmbient M) → ℝ, x₀ ∈ interiorLiveInjDomGen M ha hL h0r h0c →
      ∀ q, pivotBlowupOn (activeMGen M ha) p₀ x₀ q ≠ 0 := by
    intro x₀ hx₀ q
    have hall : ∀ j, x₀ j ≠ 0 := hx₀.2
    rw [pivotBlowupOn]
    split
    · exact hall _
    · split
      · exact mul_ne_zero (hall _) (hall _)
      · exact hall _
  rintro x ⟨x₀, hx₀, rfl⟩ x' ⟨x₀', hx₀', rfl⟩ hkeq
  have hpb : pivotBlowupOn (activeMGen M ha) p₀ x₀ = pivotBlowupOn (activeMGen M ha) p₀ x₀' :=
    kLDU_inj_of_nonzeroGen M ha _ _ (hpbo_ne x₀ hx₀) hkeq
  have hsub : interiorLiveInjDomGen M ha hL h0r h0c
      ⊆ interiorLiveInjDomGen M ha hL h0r h0c \ {x | x p₀ = 0} := fun u hu => ⟨hu, hu.1⟩
  exact congrArg _ ((pivotBlowupOn_injOn (activeMGen M ha) p₀ _).mono hsub hx₀ hx₀' hpb)

/-! ## The `BchartLeafGen`-recovery half (the load-bearing residual — BOUNDED, not a wall)

BOUNDED-vs-WALL VERDICT (verify-first, machine-checked against the defs): **BOUNDED-LABOUR, not a wall.**
The recovery is a TRIANGULAR forward-substitution over boundaries, acyclic (`layer s ← layer s-1`), of
which the L=2 `interiorLive_BchartLeaf_injOn` is the 2-node instance. From `BchartLeafGen y =
BchartLeafGen y'`: `paramsEquivFlat` injective + `reindexLs_BparamsLeafGen` (banked) give `Agen 1 (…y) s
= Agen 1 (…y') s` at every `s : Fin L`. Then per boundary `s`, `Agen … s = chainA(Nblk s, Wblk s,
Cgen(s+1)) = [Cgen(s+1) − Nblk s·Wblk s ; Wblk s]` (via `chainA_apply_castAdd`/`_natAdd`): the lift rows
give `Wblk s`, and — with `Nblk s = readN ⟨s-1⟩` already recovered at layer `s-1` — the kept rows give
`Cgen(s+1)`, which is `schurFrameProd(K,X,N,E)_s` (interior, via `Cgen_live_interior_eq_schurFrameProd`)
or `rfin` (leaf), inverted by `schurFrameMap_inj_of_det_ne_zero` with `det K_s ≠ 0` (banked-adjacent:
`readK_kLDU_det = ∏ pivots`, each `= (pbo x)(diagAxis) ≠ 0` on the all-nonzero domain via
`readK_pbo_all`). A final `funext q; cases chartIdxEquiv q` (mirroring `kLDU_injStep2Gen`) upgrades the
per-boundary reader equality to `y = y'` — eInGen-FREE (does not need Factor 1's `eInGen`).

REMAINING BRICKS (bounded, ~250 LoC, no new proof class, a focused follow-on tide):
  (1) a per-boundary `frameRecoverGen s`: `Agen … s`-equality + `readN ⟨s-1⟩`-equality + `det K_s ≠ 0`
      ⟹ raw K/X/N/E-slot equality at boundary `s` (the L=2 `slotReadV0_eq_of_BparamsLeaf0_eq` +
      `flatBlock_schurFrameMap_eq`, generalized off boundary 1; the interior `s≥1` adds the
      `− Nblk s·Wblk s` subtraction the L=2 `c0=0` collapse skipped);
  (2) the forward induction over `s : Fin L`;
  (3) the `funext q`-coverage closer, whose one fiddly step is reconciling the leaf/frame decode of the
      shared `Sum.inl` `schurDim` slot at boundary `L-1` (`schurSlotEquiv` vs `frameSplitEquiv`).
Left as an isolated `sorry` pending that follow-on; the MATH (slot-disjoint faithful decode + nonzero
monomial det, genm-l3interior) supports injectivity ∀L. -/

/-- **`BchartLeafGen` injective on the kLDU-image of `pbo '' injDom`** (general-`L`). The per-boundary
Schur-frame VALUE recovery — triangular forward-substitution over boundaries (see the module verdict
above: BOUNDED, eInGen-free, ~250 LoC of `frameRecoverGen` + induction + coverage-closer). SORRY pending
that focused follow-on tide; not a wall. -/
theorem interiorLive_BchartLeaf_injOnGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Set.InjOn (BchartLeafGen M ha)
      (kLDU M (tach M) ha
        '' (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c)
          '' interiorLiveInjDomGen M ha hL h0r h0c)) := by
  sorry

/-- **`interiorLive_injOnGen` — `InjOn` off the pivot ∪ q-axes** (general-`L`) — the `Set.InjOn.comp`
glue: from the factorization `interiorLivePhiGen = (BchartLeafGen ∘ kLDU) ∘ pbo` (`hmap_leafGen` at
`kLDU x` + `interiorLive_commuteGen`), `pbo` injective off `{u leafPivot = 0}`, then `BchartLeafGen ∘
kLDU` injective via the two atoms (`interiorLive_kLDU_injOnGen` DONE + `interiorLive_BchartLeaf_injOnGen`
[the Schur-recovery residual]). The general-`L` lift of `interiorLive_injOn`. -/
theorem interiorLive_injOnGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Set.InjOn (interiorLivePhiGen M ha hL h0r h0c) (interiorLiveInjDomGen M ha hL h0r h0c) := by
  set p₀ := leafPivot M ha hL h0r h0c with hp₀
  set pbo := pivotBlowupOn (activeMGen M ha) p₀ with hpbo
  have hfact : interiorLivePhiGen M ha hL h0r h0c
      = (BchartLeafGen M ha ∘ kLDU M (tach M) ha) ∘ pbo := by
    funext x
    rw [interiorLivePhiGen, hmap_leafGen M ha hL h0r h0c]
    show BchartLeafGen M ha (pbo (kLDU M (tach M) ha x)) = _
    rw [hpbo, interiorLive_commuteGen M ha hL h0r h0c x]; rfl
  rw [hfact]
  have hpbo_inj : Set.InjOn pbo (interiorLiveInjDomGen M ha hL h0r h0c) := by
    have hsub : interiorLiveInjDomGen M ha hL h0r h0c
        ⊆ interiorLiveInjDomGen M ha hL h0r h0c \ {x | x p₀ = 0} := by
      intro u hu; exact ⟨hu, hu.1⟩
    exact (pivotBlowupOn_injOn (activeMGen M ha) p₀ _).mono hsub
  exact (interiorLive_BchartLeaf_injOnGen M ha hL h0r h0c).comp
    (interiorLive_kLDU_injOnGen M ha hL h0r h0c) (Set.mapsTo_image _ _)
    |>.comp hpbo_inj (Set.mapsTo_image _ _)

end DLNFibre.DLN.RLCT
