import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2Conj
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestLeadingBlock

/-! # Scratch: L2 leg-close pieces (route-b), verified before wiring into `deepest_gauge_construction`.

**Status (genm-l2close).** Step (c) of the route-b close is COMPLETE + sorry-free here, as `example`
contracts pinning the exact signatures the wire consumes (local `have`s in `deepest_gauge_construction`'s
L=2 branch):
- `hDA-0`   : `IsUnit (deepBlkA 0)` — `deepestPoint_leadingBlock_isUnit` + inline submatrix↔toBlocks₁₁
              (`rThresholdSplit_symm_inl`).
- `hDA-last`: `IsUnit (deepBlkA last)` — corner identity `(reindex(dP·Qf))₁₁ = 1` + `Qf₂₁ = 0`
              (`reindex_mul_fromBlocks`) ⟹ `deepBlkA_last · M = 1` ⟹ det unit; column equiv collapsed
              by `pivotThresholdSplit_pivotJSucc_frontEmbed`.
- `hDA ∀ s` : the two layers assembled at `L = 2`.
- `hY`/`hZ` : `deepBlkY_layer0_zero` / `deepBlkZ_layerLast_zero`.
- `hbdy`    : `deepBlk_boundary_of_L2`.
- conj spectator: `(conjAbsorb q).2.2 = q.2.2` via `coreShearHomeo_spectator`.
- `psiSplitRawL2CoreConj` continuous-at-0 (for the `hsub4core` closedBall germ).

## Conj `hsub3reg` (the long pole) — CLOSED, sorry-free + axiom-clean `[propext, Classical.choice, Quot.sound]`.

The 2 opaque-width gluing sorries are discharged (genm-l2fin): `conj_he2_raw` (the he2 raw↔dict
connector) and the hm-triple assembly inside `deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ`. Routes:
- `conj_he2_raw`: `show`-unfold the lets to literal-index `(paramsEquivFlat).symm` form; obtain the dict
  haves at literal `(0:Fin 2)`/`(1:Fin 2)`, collapse `Fin.castSucc/.succ` widths with
  `Fin.castSucc_zero`/`_one`/`Fin.succ_zero_eq_one`/`_one_eq_two`; transport the two conj readbacks to
  literal `1` by `exact` (defeq `lastLayer hL ≡ 1`, where `▸` fails on the dependent codomain width); the
  `hY0c` midWidth `finCongr_refl` collapse; bridge the dict identities by `.trans` (dodges the `rw`
  proof-term mismatch); apply `e2_conj_dict`.
- hm-triple: `subst hL2eq` UP FRONT (before the `set`s) so `conj_hm_triple`/`conj_he2_raw` (stated at
  `Fin 3`) apply directly; derive `h0`/`h11G`/`h21G`/`he2` (the four GREEN ingredients) and feed
  `conj_hm_triple` — all index/width residuals close by defeq.

GREEN ingredient lemmas (sorry-free): `reindex_decode_blocks_at` (decode↔read bridge),
`reindex_decode0_conj_shared` (h0/layer-0 shared), `reindex_decodeLast_conj_b11`/`_b21` (h11G/h21G),
`e2_conj_dict` (the e2 leak-kill, `l2*Conj` dict form via `e2_regPreserve`), `conj_hm_triple` (the
`reindex_prod_regBlocks_eq_of_e2` assembly engine, at `Fin 3`). The `hsub3reg` scaffold itself (frame
ids + the psi-AGNOSTIC #147 helpers `resid_regBlocks_eq_of_mid_agree` + `deepestEFull_sq_sum_eq_of_resid_blocks`)
composes GREEN.

THE 2 REMAINING SORRIES (pure Lean opaque-width gluing — NOT math; the documented friction class,
lean/CLAUDE.md "have+exact opaque-width"):
1. `conj_he2_raw` final step: the dictionary haves + `he2 := e2_conj_dict` are assembled; need the
   let-unfold (`Aq`/`Aψ` are `let`-bound — `simp only [hAq…]` makes no progress because the goal's
   `Aq 0` ≠ syntactic `(paramsEquivFlat H).symm x ⟨0,_⟩`) + defeq-index (`⟨0,_⟩.castSucc`↔`0`,
   `⟨0,_⟩.succ`↔`1`) + the `l2Y0Conj` midWidth `finCongr_refl` collapse (hY0c @DeepestDiffeoBridgeL2Conj:2459).
   ROUTE: `change`/`show` the goal to the `(paramsEquivFlat H).symm x`-index form first, OR state
   `reindex_decode_blocks_at` calls with literal `(0:Fin 2)`/`(1:Fin 2)` so widths are `H 0/1/2`.
2. `…_eq_germ` hm-triple assembly: `subst hL2eq` (FAILS on the `set Aψ/Aq` let-bindings — use plain
   `have`/avoid `set`, or `clear_value`), then `conj_hm_triple` (Fin 3) applies with `h0`/`h11G`/`h21G`
   (derived in-proof) + `conj_he2_raw` for `he2`. Index reconcile: `lastLayer hL = (1:Fin 2)` by
   `simp[lastLayer];rfl` (VERIFIED).

THEN: LINK 2 = clean wire on two banked primitives (`rlctAtOn_comp_homeomorph` @S1Fubini:54 [the @439
Θ-peel template] + `rlctAtOn_comp_localDiffeo`/`rlctAtOn_diffeo_bridge_of` [the in-file Ψ_conj use is the
template]); `hstep2 = LINK1∘LINK2` → close `deepest_diffeo_bridge_L2` (the wire is `deepest_gauge_construction`
L=2 branch, DeepestL2Wiring.lean:485-689 — `hstep2`'s sorry @694 / the hm·/hsub4core sorries @611-686). -/

open MeasureTheory Topology Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

-- Step (c) pieces: hY, hZ, hbdy come directly from banked lemmas at L=2.
-- Layer-0 hDA: IsUnit (deepBlkA 0) from deepestPoint_leadingBlock_isUnit + inline submatrix↔toBlocks₁₁.

/-- Layer-0 conjugated pivot base is a unit: `deepBlkA 0` IS the leading r×r block, a unit by htop. -/
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r) :
    IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)) := by
  have hlead := deepestPoint_leadingBlock_isUnit H r B hB hr hL hL2 htop
  -- deepBlkA 0 = (reindex rThr rThr (deepestPoint 0)).toBlocks₁₁; show it equals the submatrix.
  have heq : deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)
      = (deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L)).submatrix
        (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).castSucc) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).castSucc))
        (Fin.castLE (hr (⟨0, by omega⟩ : Fin L).succ) : Fin r → Fin (H (⟨0, by omega⟩ : Fin L).succ)) := by
    apply Matrix.ext
    intro i j
    show (Matrix.reindex (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).castSucc) (hr _))
        (rThresholdSplit r (H (⟨0, by omega⟩ : Fin L).succ) (hr _))
        (deepestPoint H r B hB hr hL (⟨0, by omega⟩ : Fin L))).toBlocks₁₁ i j = _
    simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      rThresholdSplit_symm_inl]
  rw [heq]; exact hlead

-- hY at L=2: deepBlkY 0 = 0
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0 :=
  deepBlkY_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin L) rfl

-- hZ at L=2: deepBlkZ last = 0
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    deepBlkZ H r B hB hr hL (lastLayer hL) = 0 :=
  deepBlkZ_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL)
    (by simp only [lastLayer]; omega)

-- hbdy: the boundary structure (both layers boundary at L=2)
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2) :
    ∀ s : Fin L, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0 :=
  deepBlk_boundary_of_L2 H r B hB hr hL hL2eq

-- conj spectator: (conjAbsorb q).2.2 = q.2.2 via coreShearHomeo_spectator
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s))
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (deepestCoreAbsorbConj H r B hB hr hL hDA q).2.2 = q.2.2 :=
  coreShearHomeo_spectator (schurCutoffShiftConj H r B hB hr hL hDA)
    (continuous_schurCutoffShiftConj H r B hB hr hL hDA) q

/-! ### Step (e) germs: psiSplitRawL2CoreConj continuous-at-0 ⟹ closedBall germ; l2WConj.det germ. -/

-- psiSplitRawL2CoreConj continuous at the split origin (δc strict-deriv at 0 + id).
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDA1 : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)))
    (hY : deepBlkY H r B hB hr hL (⟨0, by omega⟩ : Fin L) = 0)
    (hZ : deepBlkZ H r B hB hr hL (lastLayer hL) = 0) :
    ContinuousAt (psiSplitRawL2CoreConj H r B hB hr hL hL2eq)
      (0 : DeepestSplit H r (deepestNGauge H r)) := by
  have hδ : ContinuousAt (fun q => psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q)
      (0 : DeepestSplit H r (deepestNGauge H r)) :=
    (hasStrictFDerivAt_psiSplitDeltaL2CoreConj_zero H r B hB hr hL hL2eq hDA0 hDA1 hY hZ).continuousAt
  have hid : psiSplitRawL2CoreConj H r B hB hr hL hL2eq
      = fun q => (psiSplitRawL2CoreConj H r B hB hr hL hL2eq q - q) + q := by
    funext q; rw [sub_add_cancel]
  rw [hid]; exact hδ.add continuousAt_id

/-! ### Step (c) last-layer hDA: IsUnit (deepBlkA last) via the corner identity + Qf block-upper. -/

-- Probe: deepBlkA last in terms of the pivotJSucc-split reindex, under hJfront.
-- Target: A₁₁·B₁₁ = 1 (from corner, Qf₂₁=0) ⟹ deepBlkA last is a unit.
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    -- bundle corner (with pivotJSucc J), bundle hQUpper (Qf₂₁=0), aligned to pivotJSucc J:
    (hcorner : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (hQUpper : (Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₁ = 0) :
    IsUnit (deepBlkA H r B hB hr hL (lastLayer hL)) := by
  -- The shared middle split eMid := pivotThr (pivotJSucc J) on H ((lastLayer).succ).
  set eR := rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc) with heR
  set eMid := pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J) with heMid
  -- Block-mult: (reindex eR eMid (dP * Qf))₁₁ = A₁₁·B₁₁ + A₁₂·B₂₁.
  have hblk := reindex_mul_fromBlocks eR eMid eMid
    (deepestPoint H r B hB hr hL (lastLayer hL)) (Qf (lastLayer hL))
  -- corner ₁₁ = 1.
  have hc11 : (Matrix.reindex eR eMid
      ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))).toBlocks₁₁
      = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    rw [show Matrix.reindex eR eMid
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 from hcorner,
      Matrix.toBlocks_fromBlocks₁₁]
  -- A₁₁·B₁₁ = 1 (Qf₂₁ = 0 kills the second summand).
  have hkey : (Matrix.reindex eR eMid (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₁₁
      * (Matrix.reindex eMid eMid (Qf (lastLayer hL))).toBlocks₁₁ = 1 := by
    have h := hc11
    rw [hblk, Matrix.toBlocks_fromBlocks₁₁, hQUpper, Matrix.mul_zero, add_zero] at h
    exact h
  -- A₁₁ = deepBlkA last (the pivotJSucc-split column equiv collapses to rThr under hJfront).
  have hAeq : (Matrix.reindex eR eMid (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₁₁
      = deepBlkA H r B hB hr hL (lastLayer hL) := by
    have hpiv : eMid = rThresholdSplit r (H ((lastLayer hL).succ)) (hr ((lastLayer hL).succ)) := by
      rw [heMid, hJfront', pivotThresholdSplit_pivotJSucc_frontEmbed H r hr hL]
    rw [hpiv]; rfl
  rw [hAeq] at hkey
  -- A·B = 1 (square matrices) ⟹ det A · det B = 1 ⟹ det A is a unit ⟹ A is a unit.
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : (deepBlkA H r B hB hr hL (lastLayer hL)).det
      * (Matrix.reindex eMid eMid (Qf (lastLayer hL))).toBlocks₁₁.det = 1 := by
    rw [← Matrix.det_mul, hkey, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ hdet

/-! ### hDA assembly: ∀ s : Fin L at L=2 from the two layers. -/

-- At L=2, ∀ s : Fin L reduces to s=0 and s=lastLayer; assemble from the two banked units.
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (hDA0 : IsUnit (deepBlkA H r B hB hr hL (⟨0, by omega⟩ : Fin L)))
    (hDAlast : IsUnit (deepBlkA H r B hB hr hL (lastLayer hL))) :
    ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s) := by
  intro s
  rcases Nat.eq_zero_or_pos (s : ℕ) with hs0 | hspos
  · have : s = (⟨0, by omega⟩ : Fin L) := Fin.ext hs0
    rw [this]; exact hDA0
  · have : s = lastLayer hL := by
      apply Fin.ext; simp only [lastLayer]
      have := s.isLt; omega
    rw [this]; exact hDAlast

/-! ### The conjugated `hm11/hm12/hm21` (the long pole) — Codex-mapped route.

Build the three block agreements for `prod H Aψ` vs `prod H Aq` where `Aq = decode x`,
`Aψ = decode (split.symm (psiSplitRawL2CoreConj (split x)))`, then `hsub3reg` = #147 verbatim. -/

-- Per-layer block dictionary at the MOVED point (reindex(Aψ s)₁₁) via the chart-point readback +
-- the conj readX-transport + the split round-trip. Layer s, boundary (deepBlkT_s = 0).
example (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ) (s : Fin L)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) s)).toBlocks₁₁
      = deepBlkA H r B hB hr hL s
        + readX H r hr hL ((split x).1, (split x).2.2) s := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hrt : deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w
      = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [← hsplit w, hw, split.apply_symm_apply]
  obtain ⟨h11, _, _, _⟩ := reindex_decode_split_toBlocks H r B hB hr hL w s hT
  rw [h11, hrt, readX_psiSplitRawL2CoreConj_eq]

/-- **A clean per-layer block dictionary at the chart/moved point** (helper). For any flat point `w`,
the four blocks of `reindex (rThr s.castSucc) (rThr s.succ) (decode w)_s` are
`deepBlk· + read·(split w)` and the core, at a boundary layer (`hT`). Just `reindex_decode_split_toBlocks`
with the round-trip `deepestSplit w0 w = split w`. -/
private theorem reindex_decode_blocks_at (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (w : Fin (flatDim H) → ℝ) (s : Fin L)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    let MX := Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)
    MX.toBlocks₁₁ = deepBlkA H r B hB hr hL s + readX H r hr hL ((split w).1, (split w).2.2) s
      ∧ MX.toBlocks₂₁ = deepBlkZ H r B hB hr hL s + readZ H r hr hL ((split w).1, (split w).2.2) s
      ∧ MX.toBlocks₁₂ = deepBlkY H r B hB hr hL s + readY H r hr hL ((split w).1, (split w).2.2) s
      ∧ MX.toBlocks₂₂ = (paramsEquivFlat (deepestM H r)).symm (split w).2.1 s := by
  intro MX
  obtain ⟨h11, h21, h12, h22⟩ := reindex_decode_split_toBlocks H r B hB hr hL w s hT
  rw [hsplit w] at *
  exact ⟨h11, h21, h12, h22⟩

/-- **Layer-0 SHARED under the conjugated move** (`reindex(Aψ 0) = reindex(Aq 0)`). At layer 0 (≠ last,
boundary) the conjugated move fixes every read + the core, so the reindexed decoded layer-0 is unchanged.
Stated at the `rThr`/`rThr` split (s.castSucc / s.succ). -/
private theorem reindex_decode0_conj_shared (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ) (s : Fin L) (hs : s ≠ lastLayer hL)
    (hT : (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (deepestPoint H r B hB hr hL s)).toBlocks₂₂ = 0) :
    Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) s)
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s) := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hw, split.apply_symm_apply]
  -- Blocks at the moved point (split w = ψ(split x)) and the chart point (split x).
  obtain ⟨hψ11, hψ21, hψ12, hψ22⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit w s hT
  obtain ⟨hq11, hq21, hq12, hq22⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit x s hT
  -- All four reads are fixed at a non-last layer.
  rw [hsw] at hψ11 hψ21 hψ12 hψ22
  rw [readX_psiSplitRawL2CoreConj_eq] at hψ11
  rw [readZ_psiSplitRawL2CoreConj_eq] at hψ21
  rw [readY_psiSplitRawL2CoreConj_of_ne_eq H r B hB hr hL hL2eq (split x) s hs] at hψ12
  rw [coreRead_psiSplitRawL2CoreConj_of_ne H r B hB hr hL hL2eq (split x) s hs] at hψ22
  -- Reassemble via fromBlocks of the four (now-equal) blocks.
  rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ))
        (((paramsEquivFlat H).symm w) s)),
    ← Matrix.fromBlocks_toBlocks (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s))]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₁₁
      from by rw [hψ11, hq11]]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₁₂
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₁₂
      from by rw [hψ12, hq12]]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₂₁
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₂₁
      from by rw [hψ21, hq21]]
  rw [show (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm w) s)).toBlocks₂₂
      = (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (((paramsEquivFlat H).symm x) s)).toBlocks₂₂
      from by rw [hψ22, hq22]]

/-- **Last-layer ₁₁ agreement** under the conjugated move (`reindex(Aψ last)₁₁ = reindex(Aq last)₁₁`),
at the `rThr (H last.succ)` split (readX fixed). -/
private theorem reindex_decodeLast_conj_b11 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ)
    (hT : (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₂₂ = 0) :
    (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) (lastLayer hL))).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₁₁ := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hw, split.apply_symm_apply]
  obtain ⟨hψ11, _, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit w (lastLayer hL) hT
  obtain ⟨hq11, _, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit x (lastLayer hL) hT
  rw [hψ11, hsw, readX_psiSplitRawL2CoreConj_eq, hq11]

/-- **Last-layer ₂₁ agreement** under the conjugated move (readZ fixed). Mirror of `_b11`. -/
private theorem reindex_decodeLast_conj_b21 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ)
    (hT : (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (deepestPoint H r B hB hr hL (lastLayer hL))).toBlocks₂₂ = 0) :
    (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm (split.symm
          (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)))) (lastLayer hL))).toBlocks₂₁
      = (Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr (lastLayer hL).castSucc))
        (rThresholdSplit r (H (lastLayer hL).succ) (hr (lastLayer hL).succ))
        (((paramsEquivFlat H).symm x) (lastLayer hL))).toBlocks₂₁ := by
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x) := by
    rw [hw, split.apply_symm_apply]
  obtain ⟨_, hψ21, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit w (lastLayer hL) hT
  obtain ⟨_, hq21, _, _⟩ := reindex_decode_blocks_at H r B hB hr hL split hsplit x (lastLayer hL) hT
  rw [hψ21, hsw, readZ_psiSplitRawL2CoreConj_eq, hq21]

/-- **The e2 dictionary relation** (the {12}-leak-kill, `P01` fixed). In the `l2*Conj` dictionary:
`A0c·Y1'c + Y0c·T1'c = A0c·Y1c + Y0c·T1c`. Via `e2_regPreserve` (needs `Invertible l2A0Conj`). -/
private theorem e2_conj_dict (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hdet : (l2A0Conj H r B hB hr hL q).det ≠ 0) :
    l2A0Conj H r B hB hr hL q * l2Y1pConj H r B hB hr hL hL2eq q
        + l2Y0Conj H r B hB hr hL hL2eq q * l2T1pConj H r B hB hr hL hL2eq q
      = l2A0Conj H r B hB hr hL q * l2Y1Conj H r B hB hr hL q
        + l2Y0Conj H r B hB hr hL hL2eq q * l2T1Conj H r hr hL q := by
  letI hinv : Invertible (l2A0Conj H r B hB hr hL q) :=
    (l2A0Conj H r B hB hr hL q).invertibleOfIsUnitDet (Ne.isUnit hdet)
  -- `l2Y1pConj = l2Y1Conj + ⅟(l2A0Conj)·l2Y0Conj·(l2T1Conj − l2T1pConj)` (the def, with ⅟ for ⁻¹).
  have hY1p : l2Y1pConj H r B hB hr hL hL2eq q
      = l2Y1Conj H r B hB hr hL q
        + ⅟(l2A0Conj H r B hB hr hL q) * l2Y0Conj H r B hB hr hL hL2eq q
          * (l2T1Conj H r hr hL q - l2T1pConj H r B hB hr hL hL2eq q) := by
    rw [l2Y1pConj, invOf_eq_nonsing_inv]
  rw [hY1p]
  exact e2_regPreserve (l2A0Conj H r B hB hr hL q) (l2Y0Conj H r B hB hr hL hL2eq q)
    (l2Y1Conj H r B hB hr hL q) (l2T1Conj H r hr hL q) (l2T1pConj H r B hB hr hL hL2eq q)

/-! ### The conj hm assembly skeleton (Fin 3 / subst) — validate the two-factor + column collapse. -/

/-- **The conj `hm` triple** (at `Fin 3`) — the three `{11,12,21}` block agreements for `prod Aψ` vs
`prod Aq` in #147's `pivotThr J` form, given layer-0 shared (`h0`), last-layer X/Z fixed (`h11G`/`h21G`),
and the e2 leak-kill (`he2`). Pure block algebra via `reindex_prod_regBlocks_eq_of_e2`. -/
private theorem conj_hm_triple (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1:ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront' : J = frontEmbed H r hr)
    (Aψ Aq : Params (L := 2) H)
    (h0 : Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aψ 0)
        = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0))
    (h11G : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₁₁)
    (h21G : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₂₁)
    (he2 : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₂₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₂₂) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₁
      ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₂
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₂
      ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₂₁
        = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₂₁ := by
  -- Collapse the pivot column split to rThr (H 2) (J = frontEmbed).
  rw [hJfront', pivotThresholdSplit_frontEmbed H r hr]
  -- Two-factor unfold both products.
  rw [prodDecode_eq_two_of_L2 H Aψ, prodDecode_eq_two_of_L2 H Aq]
  -- The finCongr width-casts are rfl ⟹ Equiv.refl ⟹ identity reindex; collapse them.
  simp only [show (finCongr (rfl : H 0 = H ((0 : Fin 2)).castSucc)) = Equiv.refl _ from finCongr_refl _,
    show (finCongr (rfl : H 1 = H ((0 : Fin 2)).succ)) = Equiv.refl _ from finCongr_refl _,
    show (finCongr (rfl : H 1 = H ((1 : Fin 2)).castSucc)) = Equiv.refl _ from finCongr_refl _,
    show (finCongr (rfl : H 2 = H (Fin.last 2))) = Equiv.refl _ from finCongr_refl _]
  erw [Matrix.reindex_refl_refl, Matrix.reindex_refl_refl, Matrix.reindex_refl_refl,
    Matrix.reindex_refl_refl]
  -- `Aψ 0 = Aq 0` (reindex is an Equiv on matrices; use its injectivity).
  have hAψ0 : Aψ 0 = Aq 0 :=
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))).injective h0
  rw [hAψ0]
  -- Apply the e2 engine: G0 = Aq 0, G1ψ' = Aψ 1, G1q' = Aq 1.
  exact reindex_prod_regBlocks_eq_of_e2 (rThresholdSplit r (H 0) (hr 0))
    (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
    (Aq 0) (Aq 0) (Aq 0) (Aψ 1) (Aq 1) h11G h21G he2

/-- **The he2 raw-block connector** (`Fin 3`): the raw `{11}·{12}+{12}·{22}` e2 combination of the
chart-point/moved decode blocks equals `e2_conj_dict`'s `l2*Conj` form, so it is fixed under the move.
Built at the chart point `x` (`Aq = decode x`, `Aψ = decode (split.symm (ψ (split x)))`). -/
private theorem conj_he2_raw (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1:ℕ) ≤ 2)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (x : Fin (flatDim H) → ℝ)
    (hdet0 : (l2A0Conj H r B hB hr hL (split x)).det ≠ 0) :
    let Aq : Params (L := 2) H := (paramsEquivFlat H).symm x
    let Aψ : Params (L := 2) H :=
      (paramsEquivFlat H).symm (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)))
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aψ 1)).toBlocks₂₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₁
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₁₂
        + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1)) (Aq 0)).toBlocks₁₂
          * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2)) (Aq 1)).toBlocks₂₂ := by
  intro Aq Aψ
  set q := split x with hq
  set w := split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl q) with hw
  have hsw : split w = psiSplitRawL2CoreConj H r B hB hr hL rfl q := by
    rw [hw, split.apply_symm_apply]
  -- Unfold the let-bound Aq/Aψ; the goal is now in explicit `(paramsEquivFlat H).symm …` form (literal
  -- indices `0`/`1`, widths `H 0`/`H 1`/`H 2`).
  show (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₁₂
      + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₂₂
    = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₂
      + (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂
        * (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
            (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₂
  -- The boundary deepBlkT facts (both layers, L=2), at literal indices.
  have hT0 : (Matrix.reindex (rThresholdSplit r (H ((0 : Fin 2)).castSucc) (hr _))
      (rThresholdSplit r (H ((0 : Fin 2)).succ) (hr _))
      (deepestPoint H r B hB hr hL ((0 : Fin 2)))).toBlocks₂₂ = 0 :=
    deepBlkT_layer0_zero H r B hB hr hL (by omega) ((0 : Fin 2)) rfl
  have hTlast : (Matrix.reindex (rThresholdSplit r (H ((1 : Fin 2)).castSucc) (hr _))
      (rThresholdSplit r (H ((1 : Fin 2)).succ) (hr _))
      (deepestPoint H r B hB hr hL ((1 : Fin 2)))).toBlocks₂₂ = 0 :=
    deepBlkT_layerLast_zero H r B hB hr hL (by omega) ((1 : Fin 2)) rfl
  -- Chart/moved-point block dictionaries at literal indices (widths come out `H 0`/`H 1`/`H 2`).
  obtain ⟨hAq0_11, _, hAq0_12, _⟩ :=
    reindex_decode_blocks_at H r B hB hr hL split hsplit x ((0 : Fin 2)) hT0
  obtain ⟨_, _, hAq1_12, hAq1_22⟩ :=
    reindex_decode_blocks_at H r B hB hr hL split hsplit x ((1 : Fin 2)) hTlast
  obtain ⟨_, _, hAψ1_12, hAψ1_22⟩ :=
    reindex_decode_blocks_at H r B hB hr hL split hsplit w ((1 : Fin 2)) hTlast
  -- Collapse the `Fin.castSucc/.succ` width-indices to the literal `H 0`/`H 1`/`H 2` the goal uses.
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two]
    at hAq0_11 hAq0_12 hAq1_12 hAq1_22 hAψ1_12 hAψ1_22
  -- Literal-`1` forms of the two conj readbacks: `exact`-transport handles `lastLayer hL ≡ 1` (defeq),
  -- where `▸`/`rw` fail on the dependent codomain width.
  have hRY : readY H r hr hL ((psiSplitRawL2CoreConj H r B hB hr hL rfl q).1,
        (psiSplitRawL2CoreConj H r B hB hr hL rfl q).2.2) (1 : Fin 2)
      = l2Y1pReadConj H r B hB hr hL rfl q :=
    readY_psiSplitRawL2CoreConj_last_eq H r B hB hr hL rfl q
  have hRT : (paramsEquivFlat (deepestM H r)).symm
        (psiSplitRawL2CoreConj H r B hB hr hL rfl q).2.1 (1 : Fin 2)
      = l2T1pConj H r B hB hr hL rfl q :=
    coreRead_psiSplitRawL2CoreConj_last H r B hB hr hL rfl q
  -- Rewrite the moved-layer last blocks via the conj readbacks (sw round-trip).
  rw [hsw, hRY] at hAψ1_12
  rw [hsw, hRT] at hAψ1_22
  -- Collapse the chart-point `split x` to `q`.
  rw [← hq] at hAq0_11 hAq0_12 hAq1_12 hAq1_22
  -- Translate the six raw block-haves into `l2*Conj` dictionary terms.
  --  Last-layer dict terms (`l2Y1Conj`/`l2T1Conj`) are typed at `lastLayer hL`; the literal-`1` block
  --  matches them by defeq, so `exact` closes each (`rw` then `rfl` would mismatch the index syntactically).
  -- `lastLayer hL = (1 : Fin 2)` (defeq) — bridge the literal-`1` block indices to the `l2*Conj` defs'.
  have hlast : lastLayer hL = (1 : Fin 2) := by simp only [lastLayer]; rfl
  have hY0c : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₂
      = l2Y0Conj H r B hB hr hL rfl q :=
    hAq0_12.trans (by
      rw [l2Y0Conj, show finCongr (midWidth_eq_of_L2 H r hL rfl) = Equiv.refl _ from finCongr_refl _]
      erw [Matrix.reindex_refl_refl]
      rfl)
  have hA0c : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 1) (hr 1))
          (((paramsEquivFlat H).symm x) (0 : Fin 2))).toBlocks₁₁
      = l2A0Conj H r B hB hr hL q := hAq0_11.trans rfl
  have hY1pc : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₁₂
      = l2Y1pConj H r B hB hr hL rfl q :=
    hAψ1_12.trans (by
      -- `deepBlkY 1` is defeq `deepBlkY (lastLayer hL)`; `show` aligns the index so the unfold + abel fire.
      show deepBlkY H r B hB hr hL (lastLayer hL) + l2Y1pReadConj H r B hB hr hL rfl q
          = l2Y1pConj H r B hB hr hL rfl q
      rw [l2Y1pConj, l2Y1pReadConj, l2Y1Conj]; abel)
  have hT1pc : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm w) (1 : Fin 2))).toBlocks₂₂
      = l2T1pConj H r B hB hr hL rfl q := hAψ1_22.trans rfl
  have hY1c : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₁₂
      = l2Y1Conj H r B hB hr hL q := hAq1_12.trans rfl
  have hT1c : (Matrix.reindex (rThresholdSplit r (H 1) (hr 1)) (rThresholdSplit r (H 2) (hr 2))
          (((paramsEquivFlat H).symm x) (1 : Fin 2))).toBlocks₂₂
      = l2T1Conj H r hr hL q := hAq1_22.trans rfl
  -- Rewrite the goal into the `l2*Conj` dictionary form and apply e2_conj_dict.
  rw [hA0c, hY0c, hY1pc, hT1pc, hY1c, hT1c]
  exact e2_conj_dict H r B hB hr hL rfl q hdet0

/-- **The conjugated reg-energy invariance `hsub3reg`** (the long pole) — germ-local. Mirrors #147,
with `psiSplitRawL2CoreConj` as the moved point. Per-x on the germ (where `l2A0Conj (split x)` is a
unit), the three `hm·` block agreements hold (decode↔read + layer-0 shared + last-layer X/Z fixed +
the e2 leak-kill), so #147 gives the `deepestEFull²`-sum invariance. -/
private theorem deepestEFull_sq_sum_psiSplitRawL2CoreConj_eq_germ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2eq : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L))) (hJfront' : J = frontEmbed H r hr)
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri' : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri' : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    (hNF : ∀ s : Fin L, (s : ℕ) + 1 ≠ L →
      Pf s * (deepestPoint H r B hB hr hL s) * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0))
    (hPfL : Pf (lastLayer hL)
      = (1 : Matrix (Fin (H (lastLayer hL).castSucc)) (Fin (H (lastLayer hL).castSucc)) ℝ))
    (hcorner' : Matrix.reindex (rThresholdSplit r (H (lastLayer hL).castSucc) (hr _))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        ((deepestPoint H r B hB hr hL (lastLayer hL)) * Qf (lastLayer hL))
        = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r))
    (hsplit : ∀ w, split w
      = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) w)
    (hinterface : ∀ (s : Fin L) (_ : (s : ℕ) + 1 < L),
      Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        Pf ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc))
          (Fin (H (⟨(s : ℕ) + 1, by omega⟩ : Fin L).castSucc)) ℝ))
    (hS3b : Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointP0 H hL Pf * B * endpointQL H hL Qf)
      = Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    (x : Fin (flatDim H) → ℝ)
    (hdet0 : (l2A0Conj H r B hB hr hL (split x)).det ≠ 0) :
    (∑ i, (deepestEFull H r hr hL J Pf Qf
        (psiSplitRawL2CoreConj H r B hB hr hL hL2eq (split x)) i) ^ 2)
      = ∑ i, (deepestEFull H r hr hL J Pf Qf (split x) i) ^ 2 := by
  -- Specialize to `L = 2` up front so `conj_hm_triple`/`conj_he2_raw` (stated at `Fin 3`) apply directly.
  subst hL2eq
  -- The two framed raw params: Aq = decode x, Aψ = decode (split.symm (ψ (split x))).
  set Aq : Params H := (paramsEquivFlat H).symm x with hAq
  set Aψ : Params H :=
    (paramsEquivFlat H).symm (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)))
    with hAψ
  -- Frame identities (§iii) for both points.
  have hframeq : ∀ s : Fin 2,
      framedParamsPivot H r hr hL J Pf Qf (split x) s = Pf s * Aq s * Qf s := by
    intro s; rw [hsplit x]
    exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner' x s
  have hframeψ : ∀ s : Fin 2,
      framedParamsPivot H r hr hL J Pf Qf
          (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) s
        = Pf s * Aψ s * Qf s := by
    intro s
    have hrt : psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)
        = split (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))) :=
      (split.apply_symm_apply _).symm
    rw [hrt, hsplit (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)))]
    exact framedParamsPivot_eq_frame_of_front H r B hB hr hL J hJfront' Pf Qf hNF hPfL hcorner'
      (split.symm (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x))) s
  -- The four hm-inputs (all GREEN standalone): layer-0 shared (`h0`), last-layer X/Z fixed
  -- (`h11G`/`h21G`), and the e2 leak-kill (`he2`, the raw↔dict connector). Then `conj_hm_triple` (Fin 3)
  -- assembles the three `{11,12,21}` block agreements `reindex(prod Aψ) = reindex(prod Aq)`.
  have h0 := reindex_decode0_conj_shared H r B hB hr hL rfl split hsplit x (⟨0, by omega⟩ : Fin 2)
    (Fin.ne_of_val_ne (by simp only [lastLayer]; omega))
    (deepBlkT_layer0_zero H r B hB hr hL (by omega) (⟨0, by omega⟩ : Fin 2) rfl)
  have h11G := reindex_decodeLast_conj_b11 H r B hB hr hL rfl split hsplit x
    (deepBlkT_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by simp [lastLayer]))
  have h21G := reindex_decodeLast_conj_b21 H r B hB hr hL rfl split hsplit x
    (deepBlkT_layerLast_zero H r B hB hr hL (by omega) (lastLayer hL) (by simp [lastLayer]))
  have he2 := conj_he2_raw H r B hB hr hL split hsplit x hdet0
  -- Reconcile the ingredient indices (`⟨0,_⟩`/`lastLayer hL`) to `conj_hm_triple`'s literals
  -- (`0`/`1 : Fin 2`); all defeq, so `convert` closes the residual index/width casts.
  obtain ⟨hm11, hm12, hm21⟩ :
      (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₁
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₁
        ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₁₂
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₁₂
        ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aψ)).toBlocks₂₁
          = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last 2)) (hr (Fin.last 2)) J) (prod H Aq)).toBlocks₂₁ :=
    conj_hm_triple H r B hB hr hL J hJfront' Aψ Aq h0 h11G h21G he2
  obtain ⟨h11, h12, h21⟩ :=
    resid_regBlocks_eq_of_mid_agree H r B hr hL J Pf Qf Aψ Aq hPtri' hQtri' hm11 hm12 hm21
  exact deepestEFull_sq_sum_eq_of_resid_blocks H r B hr hL J Pf Qf
    (psiSplitRawL2CoreConj H r B hB hr hL rfl (split x)) (split x) Aψ Aq
    hframeψ hframeq hinterface hS3b h11 h12 h21

end DLNFibre.DLN.RLCT
