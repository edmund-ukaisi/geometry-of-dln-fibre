import DLNFibre.DLN.Aoyagi.MultiAffineStepWire
import DLNFibre.Core.SubmultComp

/-!
# `DLN.Aoyagi.MultiAffineHomogWire` — the Gap-B homogeneity atoms (SEAT-L3T2)

Primed twins of the three `MonumentAtlas` Gap-B homogeneity statements (the controller swaps the
`MonumentAtlas` sorries for these, same pattern as `Case2Wire.case2_preserves_stepInv'`):

* `homogeneousDeg1On_comp_of_fixing` — the STEP helper (no prime; a fresh general lemma): a support-fixing
  `σ` preserves `HomogeneousDeg1On` on the SAME block. The `AffineOn` half mirrors
  `MultiAffineStepWire.deg1_comp_of_fixing`; the vanishing half rides `hfix` (σ fixes `X` ⟹ σu's `X`-coords
  stay `0`).
* `coreGen_layerHomogeneous'` — the BASE atom (canonFlatten pin): each flattened core generator is
  degree-1-homogeneous on every layer `ℓ < N`. Route: isolate the layer-`ℓ` matrix `A_ℓ` in `mult` via
  `Core.submult_comp` (`mult = L · A_ℓ · R`, `L`/`R` reading layers `≠ ℓ`); `coreGen` is then a linear form
  `∑ (layer-ℓ-free coeff)·(A_ℓ entry)` in the layer-`ℓ` flat coords, with no constant part.
* `foldResid_layerHomogeneous'` — the fold INDUCTION (conjunct-2 only): base = `coreGen_layerHomogeneous'`;
  step = `homogeneousDeg1On_comp_of_fixing` per δ-case (the step map fixes layers `≥ threshold` at the
  current shear, `MultiAffineStepWire`'s banked `hfix`/`hagree`).

This lives DOWNSTREAM of `MonumentAtlas` (the induction consumes `MultiAffineStepWire`'s geometric lemmas
`canonCenterOf_decode_layer_le` / `case11_pivot_decode_lt` / `conOracle_child_transition`, which sit here).
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-! ### The step helper — `HomogeneousDeg1On` composes with a support-fixing map -/

/-- **`HomogeneousDeg1On` survives composition with a support-fixing `σ`.** If `σ` FIXES every `X`-coord
(`hfix`) and PRESERVES off-`X` agreement (`hagree`), then `g ∘ σ` is `HomogeneousDeg1On` on the SAME block
`X`. The `AffineOn` half is the single-block form of `deg1_comp_of_fixing`'s per-layer logic; the vanishing
half: if every `X`-coord of `u` is `0`, then `hfix` makes every `X`-coord of `σ u` be `0` too, so
`g (σ u) = 0` by `g`'s vanishing clause. -/
theorem homogeneousDeg1On_comp_of_fixing {D : ℕ}
    (g : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (hfix : ∀ x ∈ X, ∀ u, σ u x = u x)
    (hagree : ∀ u v : Fin D → ℝ, (∀ s, s ∉ X → u s = v s) → ∀ s, s ∉ X → σ u s = σ v s)
    (hg : HomogeneousDeg1On g X Set.univ) :
    HomogeneousDeg1On (fun u => g (σ u)) X Set.univ := by
  obtain ⟨hAff, hvan⟩ := hg
  refine ⟨?_, ?_⟩
  · -- AffineOn (g ∘ σ) X univ: c'/a' = (·∘σ); σ fixes X ⟹ the X-linear part survives.
    obtain ⟨a, b, ha_ign, hb_ign, hrepr⟩ := hAff
    refine ⟨fun u => a (σ u), fun x u => b x (σ u), ?_, ?_, ?_⟩
    · exact (ignoresCoords_univ_iff_agree _ X).mpr (fun u v hag =>
        (ignoresCoords_univ_iff_agree a X).mp ha_ign (σ u) (σ v) (hagree u v hag))
    · intro x hx
      exact (ignoresCoords_univ_iff_agree _ X).mpr (fun u v hag =>
        (ignoresCoords_univ_iff_agree (b x) X).mp (hb_ign x hx) (σ u) (σ v) (hagree u v hag))
    · intro u _
      show g (σ u) = a (σ u) + ∑ x ∈ X, b x (σ u) * u x
      rw [hrepr (σ u) (Set.mem_univ _)]
      refine congrArg (a (σ u) + ·) (Finset.sum_congr rfl (fun x hx => ?_))
      rw [hfix x hx u]
  · -- vanishing: σ fixes X ⟹ σu vanishes on X ⟹ g (σ u) = 0.
    intro u _ hu
    exact hvan (σ u) (Set.mem_univ _) (fun x hx => by rw [hfix x hx u]; exact hu x hx)

/-! ### The base atom — `coreGen` is per-layer degree-1-homogeneous at the canonical flatten

`canonFlatten` is the coordinate reindex, so the layer-`ℓ` matrix `A_ℓ` of `canonFlatten d u` reads exactly
the layer-`ℓ` flat coords. Isolating `A_ℓ` in `mult` via `Core.submult_comp` writes `coreGen` as a linear
form `∑ (coeff reading layers ≠ ℓ)·(A_ℓ entry)` — degree-1-homogeneous on `layerCoords d ℓ`. -/

/-- The `canonFlatten` coordinate reindex, at an entry: `(canonFlatten d u) i row col = u (flat (i,row,col))`. -/
theorem canonFlatten_apply (d : Fin (N + 1) → ℕ) (u : Fin (flatDim d) → ℝ)
    (i : Fin N) (row : Fin (d i.succ)) (col : Fin (d i.castSucc)) :
    (canonFlatten d u) i row col = u (tupIdxEquiv d ⟨⟨i, row⟩, col⟩) := rfl

/-- If `u`, `v` agree on `layerCoords d p`, the layer-`p` matrices of `canonFlatten` agree. -/
theorem canonFlatten_layer_eq_of_agree (d : Fin (N + 1) → ℕ) (p : Fin N)
    {u v : Fin (flatDim d) → ℝ} (h : ∀ x ∈ layerCoords d p, u x = v x) :
    (canonFlatten d u) p = (canonFlatten d v) p := by
  funext row col
  rw [canonFlatten_apply, canonFlatten_apply]
  refine h _ ?_
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨⟨p, row⟩, col⟩, rfl, rfl⟩

/-- **Interval congruence for `submult`.** If two tuples agree on every layer inside `[i, j)`, their
sub-products over `[i, j]` agree. By induction on the upper index `j` through `submult_succ`. -/
theorem submult_congr {k : Type*} [CommRing k] (d : Fin (N + 1) → ℕ) (A B : Tuple (k := k) d)
    (i : Fin (N + 1)) :
    ∀ (j : Fin (N + 1)) (hij : i ≤ j)
      (h : ∀ p : Fin N, i ≤ p.castSucc → p.succ ≤ j → A p = B p),
      submult d A i j hij = submult d B i j hij := by
  intro j
  induction j using Fin.induction with
  | zero =>
    intro hij _
    obtain rfl : i = 0 := le_antisymm hij (Fin.zero_le _)
    rw [submult_self, submult_self]
  | succ p ih =>
    intro hij h
    rcases eq_or_lt_of_le hij with hie | hilt
    · subst hie; rw [submult_self, submult_self]
    · have hic : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hilt
      rw [submult_succ d A i p hic, submult_succ d B i p hic,
        ih hic (fun q hq1 hq2 => h q hq1 (hq2.trans (Fin.castSucc_le_succ p))),
        h p hic le_rfl]

/-- A flat coord at layer `p ≠ ℓ` lies OUTSIDE `layerCoords d ℓ`, so off-`layerCoords ℓ` agreement of
`u`, `v` restricts to agreement on `layerCoords d p`. -/
theorem agree_on_layerCoords_of_agree_off (d : Fin (N + 1) → ℕ) (ℓ : ℕ) (p : Fin N)
    (hp : (p : ℕ) ≠ ℓ) {u v : Fin (flatDim d) → ℝ}
    (h : ∀ s, s ∉ layerCoords d ℓ → u s = v s) : ∀ x ∈ layerCoords d p, u x = v x := by
  intro x hx
  refine h x (fun hxℓ => hp ?_)
  rw [← decode_layer_of_mem_layerCoords d p x hx, decode_layer_of_mem_layerCoords d ℓ x hxℓ]

/-- **Base atom (primed twin).** Each flattened core generator at `canonFlatten d` is degree-1-homogeneous
on every layer `ℓ < N`. See `MonumentAtlas.coreGen_layerHomogeneous`.

Route: isolate the layer-`ℓ` matrix `A_ℓ` in `mult` via a double `submult_comp`, so `coreGen` reads a
linear form `∑ (M·R coeff, reading layers ≠ ℓ)·(A_ℓ entry)`; `A_ℓ`'s entries ARE the layer-`ℓ` flat coords
(`canonFlatten_apply`), giving `AffineOn` with zero constant part + vanishing. -/
theorem coreGen_layerHomogeneous' (d : Fin (N + 1) → ℕ)
    (i : Fin (d (Fin.last N) * d 0)) (ℓ : ℕ) (hℓ : ℓ < N) :
    HomogeneousDeg1On (coreGen d (canonFlatten d) i) (layerCoords d ℓ) Set.univ := by
  classical
  set ℓ' : Fin N := ⟨ℓ, hℓ⟩ with hℓ'
  set a := (finProdFinEquiv.symm i).1 with ha
  set b := (finProdFinEquiv.symm i).2 with hb
  -- interval order proofs for the layer-ℓ isolation
  have h0succ : (0 : Fin (N + 1)) ≤ ℓ'.succ := Fin.zero_le _
  have hsuccL : ℓ'.succ ≤ Fin.last N := by
    rw [Fin.le_def, Fin.val_succ, Fin.val_last]; exact hℓ
  have h0cast : (0 : Fin (N + 1)) ≤ ℓ'.castSucc := Fin.zero_le _
  have hcastsucc : ℓ'.castSucc ≤ ℓ'.succ := Fin.castSucc_le_succ ℓ'
  -- the layer-ℓ isolated factors, as functions of the point
  set M : (Fin (flatDim d) → ℝ) → Matrix (Fin (d (Fin.last N))) (Fin (d ℓ'.succ)) ℝ :=
    fun u => submult d (canonFlatten d u) ℓ'.succ (Fin.last N) hsuccL with hM
  set R : (Fin (flatDim d) → ℝ) → Matrix (Fin (d ℓ'.castSucc)) (Fin (d 0)) ℝ :=
    fun u => submult d (canonFlatten d u) 0 ℓ'.castSucc h0cast with hR
  set coeff : (Fin (d ℓ'.succ) × Fin (d ℓ'.castSucc)) → (Fin (flatDim d) → ℝ) → ℝ :=
    fun p u => M u a p.1 * R u p.2 b with hcoeff
  set enc : (Fin (d ℓ'.succ) × Fin (d ℓ'.castSucc)) → Fin (flatDim d) :=
    fun p => tupIdxEquiv d ⟨⟨ℓ', p.1⟩, p.2⟩ with henc
  set bcoeff : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ :=
    fun x u => ∑ p, if enc p = x then coeff p u else 0 with hbcoeff
  -- enc lands in `layerCoords d ℓ`
  have hencMem : ∀ p, enc p ∈ layerCoords d ℓ := by
    intro p
    simp only [henc, layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨⟨ℓ', p.1⟩, p.2⟩, rfl, rfl⟩
  -- the one-layer reduction: `submult over [ℓ.castSucc, ℓ.succ] = A_ℓ`
  have honelayer : ∀ u, submult d (canonFlatten d u) ℓ'.castSucc ℓ'.succ hcastsucc
      = (canonFlatten d u) ℓ' := by
    intro u
    rw [submult_succ d (canonFlatten d u) ℓ'.castSucc ℓ' le_rfl, submult_self, Matrix.mul_one]
  -- the residual as a linear form in the layer-ℓ coords
  have hrepr : ∀ u, coreGen d (canonFlatten d) i u = ∑ p, coeff p u * u (enc p) := by
    intro u
    show (mult d (canonFlatten d u)) a b = _
    rw [mult_eq_submult, submult_comp d (canonFlatten d u) 0 ℓ'.succ h0succ (Fin.last N) hsuccL,
      submult_comp d (canonFlatten d u) 0 ℓ'.castSucc h0cast ℓ'.succ hcastsucc, honelayer u,
      Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c1 _ => ?_)
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c2 _ => ?_)
    rw [canonFlatten_apply]
    show M u a c1 * ((canonFlatten d u) ℓ' c1 c2 * R u c2 b) = M u a c1 * R u c2 b * _
    rw [canonFlatten_apply]; ring
  -- M, R ignore `layerCoords d ℓ`, hence `coeff p` does
  have hℓ'v : (ℓ' : ℕ) = ℓ := rfl
  have hcoeff_ign : ∀ p, ∀ u v : Fin (flatDim d) → ℝ,
      (∀ s, s ∉ layerCoords d ℓ → u s = v s) → coeff p u = coeff p v := by
    intro p u v hag
    have hMe : M u = M v := by
      refine submult_congr d _ _ _ _ _ (fun q hq1 _ => ?_)
      refine canonFlatten_layer_eq_of_agree d q (agree_on_layerCoords_of_agree_off d ℓ q ?_ hag)
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc] at hq1; omega
    have hRe : R u = R v := by
      refine submult_congr d _ _ _ _ _ (fun q _ hq2 => ?_)
      refine canonFlatten_layer_eq_of_agree d q (agree_on_layerCoords_of_agree_off d ℓ q ?_ hag)
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc] at hq2; omega
    simp only [hcoeff, hMe, hRe]
  refine ⟨⟨fun _ => 0, bcoeff, ?_, ?_, ?_⟩, ?_⟩
  · -- constant part `0` ignores everything
    exact (ignoresCoords_univ_iff_agree _ _).mpr (fun _ _ _ => rfl)
  · -- each `bcoeff x` ignores `layerCoords d ℓ`
    intro x _
    refine (ignoresCoords_univ_iff_agree _ _).mpr (fun u v hag => ?_)
    simp only [hbcoeff]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hcoeff_ign p u v hag]
  · -- the `AffineOn` representation
    intro u _
    rw [hrepr u, zero_add]
    -- reindex `∑ x ∈ layerCoords, bcoeff x u * u x` back to `∑ p, coeff p u * u (enc p)`
    symm
    calc ∑ x ∈ layerCoords d ℓ, bcoeff x u * u x
        = ∑ x ∈ layerCoords d ℓ, ∑ p, (if enc p = x then coeff p u * u x else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [hbcoeff, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          split_ifs <;> ring
      _ = ∑ p, ∑ x ∈ layerCoords d ℓ, (if enc p = x then coeff p u * u x else 0) := Finset.sum_comm
      _ = ∑ p, coeff p u * u (enc p) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.sum_ite_eq (layerCoords d ℓ) (enc p) (fun x => coeff p u * u x),
            if_pos (hencMem p)]
  · -- vanishing: every `enc p ∈ layerCoords d ℓ`, so `u (enc p) = 0`
    intro u _ hu
    rw [hrepr u]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [hu (enc p) (hencMem p), mul_zero]

/-! ### The fold induction — conjunct-2 propagation -/

/-- **Fold induction (primed twin).** The fold residual at `canonFlatten d` is degree-1-homogeneous on
every layer `ℓ ≥ supportLayerOf p.conState` (`ℓ < N`). See `MonumentAtlas.foldResid_layerHomogeneous`. -/
theorem foldResid_layerHomogeneous' (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (p : TreePath d) (hnonterm : ¬ N ≤ p.conState.layer)
    (hbranch : p.IsRealBranch (canonFlatten d))
    (j : Fin (foldNR d p)) (ℓ : ℕ)
    (hℓsup : supportLayerOf p.conState ≤ ℓ) (hℓN : ℓ < N) :
    HomogeneousDeg1On (foldResid d (canonFlatten d) p j) (layerCoords d ℓ)
      (foldRegion d (canonFlatten d) p) := by
  classical
  suffices H : ∀ (q : TreePath d), ¬ N ≤ q.conState.layer → q.IsRealBranch (canonFlatten d) →
      supportLayerOf q.conState ≤ ℓ → ∀ (i : Fin (foldNR d q)),
      HomogeneousDeg1On (foldResid d (canonFlatten d) q i) (layerCoords d ℓ)
        (foldRegion d (canonFlatten d) q) by
    exact H p hnonterm hbranch hℓsup j
  intro q
  induction q with
  | root =>
    intro _ _ _ i
    exact coreGen_layerHomogeneous' d i ℓ hℓN
  | step p' c pv cse ns φ ih =>
    intro hnonterm hbranch hℓsup j
    obtain ⟨hrec, ⟨sc, hsc, hecase, hchild, hcenter, hpivpin⟩, hwcRaw, hvpin⟩ := hbranch
    obtain ⟨hwc1, hwc2, _⟩ := hwcRaw
    have hnt : ¬ N ≤ ns.layer := hnonterm
    replace hℓsup : supportLayerOf ns ≤ ℓ := hℓsup
    have htrans := conOracle_child_transition p'.conState sc hsc
    have hpnt : ¬ N ≤ p'.conState.layer := by
      rcases htrans with ⟨_, _, hL, _⟩ | ⟨_, hL, _⟩ | ⟨_, hL, _⟩ <;> · rw [hchild] at hL; omega
    have hslmono : supportLayerOf p'.conState ≤ supportLayerOf ns := by
      have key : supportLayerOf p'.conState ≤ p'.conState.layer + 1 := by
        unfold supportLayerOf; split_ifs <;> omega
      rcases htrans with ⟨_, _, hL, hC⟩ | ⟨_, hL, hC⟩ | ⟨_, hL, hC⟩ <;> rw [hchild] at hL hC
      · have hns : supportLayerOf ns = p'.conState.layer + 1 := by unfold supportLayerOf; rw [hC, hL]; simp
        omega
      · have hns : supportLayerOf ns = p'.conState.layer + 1 := by unfold supportLayerOf; rw [hC, hL]; simp
        omega
      · have hns : supportLayerOf ns = supportLayerOf p'.conState := by unfold supportLayerOf; rw [hC, hL]
        omega
    have hslP : supportLayerOf p'.conState ≤ ℓ := le_trans hslmono hℓsup
    have hNReq : foldNR d (TreePath.step p' c pv cse ns φ) = foldNR d p' := by
      show (if N ≤ ns.layer then 1 else foldNR d p') = foldNR d p'; rw [if_neg hnt]
    set g := foldResid d (canonFlatten d) p' (Fin.cast hNReq j) with hg_def
    have hIH : HomogeneousDeg1On g (layerCoords d ℓ) Set.univ := by
      have := ih hpnt hrec hslP (Fin.cast hNReq j)
      rwa [foldRegion_eq_univ] at this
    have hpInv : DivBirthInv d p'.conState :=
      PivotPres.divBirthInv_of_isRealBranch (canonFlatten d) p' hrec
    have hcb : ∀ y ∈ c, (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤ p'.conState.layer := fun y hy =>
      canonCenterOf_decode_layer_le p'.conState sc hpInv y (hcenter ▸ hy)
    have hguniv : foldRegion d (canonFlatten d) (TreePath.step p' c pv cse ns φ) = Set.univ :=
      foldRegion_eq_univ _ _
    rw [hguniv]
    -- The child support layer is `supportLayerOf ns`; the shear write/read-vanishing (`hwc1`/`hwc2`)
    -- is STRICTLY above it. Compose `g` (IH) with the step map `σ` via the fixing / recoord atoms.
    by_cases hactive : cse = StepCase.case12 ∨ cse = StepCase.case2
    · -- SHEAR-ACTIVE (case12/case2): `edgeShearRaw = blockShear φ`, `φ = canonNormalizationOf` (value-pin).
      -- The child support layer is `p'.layer + 1` here (cleared → 1 at δ1, or unchanged ≠ 0 at δ0).
      have hedgeBS : edgeShearRaw d cse φ = blockShear φ := by
        rcases hactive with h | h <;> rw [h] <;> rfl
      have hcsl : supportLayerOf ns = p'.conState.layer + 1 := by
        by_cases hδ : edgeδ d p' = true
        · have hcl : p'.conState.cleared = 0 := of_decide_eq_true hδ
          rcases htrans with ⟨_, _, hL, hC⟩ | ⟨_, hL, hC⟩ | ⟨he, _, _⟩
          · rcases hactive with h | h <;> exact absurd (h.symm.trans (hecase.symm.trans (by assumption))) (by simp)
          · rw [hchild] at hL hC; rw [supportLayerOf, hC, hcl, if_neg (by omega), hL]
          · rcases hactive with h | h <;> exact absurd (hecase.trans h) (by rw [he]; simp)
        · have hcl : p'.conState.cleared ≠ 0 := fun h => hδ (by simp [edgeδ, h])
          rcases htrans with ⟨_, _, hL, hC⟩ | ⟨_, hL, hC⟩ | ⟨_, hL, hC⟩ <;> rw [hchild] at hL hC
          · rw [supportLayerOf, hC, if_pos rfl, hL]
          · rw [supportLayerOf, hC, if_neg (by omega), hL]
          · rw [supportLayerOf, hC, if_neg hcl, hL]
      have hN1 : p'.conState.layer + 1 < N := by have := hℓsup; rw [hcsl] at this; omega
      -- pivot is inside the (layer-`≤ p'.layer`) center, so it sits strictly below layer `ℓ`
      have hpvle : (((tupIdxEquiv d).symm pv).1.1 : ℕ) ≤ p'.conState.layer := by
        refine hcb pv ?_
        have : pv ∈ canonCenterOf d p'.conState sc := by
          have := hpivpin
          rcases hactive with h | h <;> · rw [h] at this; simpa using this
        rw [hcenter]; exact this
      -- `σ` (the δ-dependent step map) equals `blockShear φ` at layer-`ℓ` coords (off pivot/center)
      -- and equals it via the value-pin. Split ℓ = child_sl (recoord) vs ℓ > child_sl (fixing).
      rcases hℓsup.lt_or_eq with hℓgt | hℓeq
      · -- ℓ > child_sl = p'.layer + 1: the shear VANISHES at layer ℓ, so `σ` FIXES it → comp_of_fixing
        have hshv : ∀ x ∈ layerCoords d ℓ, ∀ u, φ u x = 0 := fun x hx u =>
          hwc1 ℓ hℓgt x hx u (by rw [hguniv]; exact Set.mem_univ _)
        have hxne : ∀ x ∈ layerCoords d ℓ, x ≠ pv ∧ x ∉ c := by
          intro x hx
          have hxℓ := decode_layer_of_mem_layerCoords d ℓ x hx
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [h] at hxℓ; rw [hcsl] at hℓgt; omega
          · have := hcb x h; rw [hcsl] at hℓgt; omega
        by_cases hδ : edgeδ d p' = true
        · have hfun : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j
              = fun u => g (fun k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)) := by
            funext u
            show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j u = _
            rw [foldResid, dif_neg hnt, if_pos hδ]; rfl
          rw [hfun]
          refine homogeneousDeg1On_comp_of_fixing g (layerCoords d ℓ)
            (fun u k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)) (fun x hx u => ?_)
            (fun u v hag s hs => ?_) hIH
          · show blockBlowupCoordQuot pv x (edgeShearRaw d cse φ u) = u x
            rw [blockBlowupCoordQuot, if_neg (hxne x hx).1, hedgeBS]
            exact PivotPres.blockShear_fixes_of_displacement_zero φ u x (hshv x hx u)
          · show blockBlowupCoordQuot pv s (edgeShearRaw d cse φ u)
                = blockBlowupCoordQuot pv s (edgeShearRaw d cse φ v)
            rw [blockBlowupCoordQuot, blockBlowupCoordQuot]
            by_cases hsp : s = pv
            · rw [if_pos hsp, if_pos hsp]
            · rw [if_neg hsp, if_neg hsp, hedgeBS]
              show blockShear φ u s = blockShear φ v s
              have hφs : φ u s = φ v s :=
                (ignoresCoords_univ_iff_agree (fun z => φ z s) (layerCoords d ℓ)).mp
                  (by have := hwc2 ℓ hℓgt s; rwa [hguniv] at this) u v hag
              simp only [blockShear, Pi.add_apply, hag s hs, hφs]
        · have hδ0 : edgeδ d p' = false := by
            cases h : edgeδ d p' with | false => rfl | true => exact absurd h hδ
          have hfun : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j
              = fun u => g (stepMapRaw d cse c pv φ u) := by
            funext u
            show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j u = _
            rw [foldResid, dif_neg hnt, if_neg (by simp [hδ0])]; rfl
          rw [hfun]
          refine homogeneousDeg1On_comp_of_fixing g (layerCoords d ℓ) (stepMapRaw d cse c pv φ)
            (fun x hx u => ?_) (fun u v hag s hs => ?_) hIH
          · show blockBlowupMap c pv (edgeShearRaw d cse φ u) x = u x
            rw [Core.Aoyagi.blockBlowupMap_offCenter_eq c pv (edgeShearRaw d cse φ u) (hxne x hx).2,
              hedgeBS]
            exact PivotPres.blockShear_fixes_of_displacement_zero φ u x (hshv x hx u)
          · have hES : ∀ w, w ∉ layerCoords d ℓ → edgeShearRaw d cse φ u w = edgeShearRaw d cse φ v w := by
              intro w hw
              have hφw : φ u w = φ v w :=
                (ignoresCoords_univ_iff_agree (fun z => φ z w) (layerCoords d ℓ)).mp
                  (by have := hwc2 ℓ hℓgt w; rwa [hguniv] at this) u v hag
              rw [hedgeBS]; show blockShear φ u w = blockShear φ v w
              simp only [blockShear, Pi.add_apply, hag w hw, hφw]
            have hpivc : pv ∉ layerCoords d ℓ := by
              intro h; have := decode_layer_of_mem_layerCoords d ℓ pv h; rw [hcsl] at hℓgt; omega
            show blockBlowupMap c pv (edgeShearRaw d cse φ u) s
              = blockBlowupMap c pv (edgeShearRaw d cse φ v) s
            unfold blockBlowupMap
            by_cases hsp : s = pv
            · rw [if_pos hsp, if_pos hsp]; exact hES pv hpivc
            · by_cases hsc2 : s ∈ c
              · rw [if_neg hsp, if_pos hsc2, if_neg hsp, if_pos hsc2, hES pv hpivc, hES s hs]
              · rw [if_neg hsp, if_neg hsc2, if_neg hsp, if_neg hsc2, hES s hs]
      · -- ℓ = child_sl = p'.layer + 1: the shear is the recoord X-linear form → comp_of_linear
        have hℓpv1 : ℓ = p'.conState.layer + 1 := hℓeq.symm.trans hcsl
        obtain ⟨hlin_bs, hC⟩ := canonNorm_blockShear_linear_on_succLayer d p'.conState pv hN1
        have hxne : ∀ x ∈ layerCoords d ℓ, x ≠ pv ∧ x ∉ c := by
          intro x hx
          have hxℓ := decode_layer_of_mem_layerCoords d ℓ x hx
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [h] at hxℓ; rw [hℓpv1] at hxℓ; omega
          · have := hcb x h; rw [hℓpv1] at hxℓ; omega
        subst hℓpv1
        by_cases hδ : edgeδ d p' = true
        · have hfun : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j
              = fun u => g (fun k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)) := by
            funext u
            show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j u = _
            rw [foldResid, dif_neg hnt, if_pos hδ]; rfl
          rw [hfun]
          refine homogeneousDeg1On_comp_of_linear g (layerCoords d (p'.conState.layer + 1))
            (fun u k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u))
            (recoordCoeff d p'.conState pv hN1) (fun u v hag s hs => ?_) (fun u x hx => ?_) hC hIH
          · show blockBlowupCoordQuot pv s (edgeShearRaw d cse φ u)
                = blockBlowupCoordQuot pv s (edgeShearRaw d cse φ v)
            rw [blockBlowupCoordQuot, blockBlowupCoordQuot]
            by_cases hsp : s = pv
            · rw [if_pos hsp, if_pos hsp]
            · rw [if_neg hsp, if_neg hsp, hedgeBS]
              show blockShear φ u s = blockShear φ v s
              have hφs : φ u s = φ v s := by
                rw [hvpin]; exact canonNormalizationOf_agree_off_succLayer d p'.conState pv u v hag s hs
              simp only [blockShear, Pi.add_apply, hag s hs, hφs]
          · show blockBlowupCoordQuot pv x (edgeShearRaw d cse φ u)
                = ∑ jj ∈ layerCoords d (p'.conState.layer + 1), recoordCoeff d p'.conState pv hN1 u x jj * u jj
            rw [blockBlowupCoordQuot, if_neg (hxne x hx).1, hedgeBS, hvpin, hlin_bs u x hx]
        · have hδ0 : edgeδ d p' = false := by
            cases h : edgeδ d p' with | false => rfl | true => exact absurd h hδ
          have hfun : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j
              = fun u => g (stepMapRaw d cse c pv φ u) := by
            funext u
            show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j u = _
            rw [foldResid, dif_neg hnt, if_neg (by simp [hδ0])]; rfl
          rw [hfun]
          refine homogeneousDeg1On_comp_of_linear g (layerCoords d (p'.conState.layer + 1))
            (stepMapRaw d cse c pv φ) (recoordCoeff d p'.conState pv hN1)
            (fun u v hag s hs => ?_) (fun u x hx => ?_) hC hIH
          · have hES : ∀ w, w ∉ layerCoords d (p'.conState.layer + 1) →
                edgeShearRaw d cse φ u w = edgeShearRaw d cse φ v w := by
              intro w hw
              rw [hedgeBS]; show blockShear φ u w = blockShear φ v w
              have hφw : φ u w = φ v w := by
                rw [hvpin]; exact canonNormalizationOf_agree_off_succLayer d p'.conState pv u v hag w hw
              simp only [blockShear, Pi.add_apply, hag w hw, hφw]
            have hpivc : pv ∉ layerCoords d (p'.conState.layer + 1) := by
              intro h; have := decode_layer_of_mem_layerCoords d (p'.conState.layer + 1) pv h; omega
            show blockBlowupMap c pv (edgeShearRaw d cse φ u) s
              = blockBlowupMap c pv (edgeShearRaw d cse φ v) s
            unfold blockBlowupMap
            by_cases hsp : s = pv
            · rw [if_pos hsp, if_pos hsp]; exact hES pv hpivc
            · by_cases hsc2 : s ∈ c
              · rw [if_neg hsp, if_pos hsc2, if_neg hsp, if_pos hsc2, hES pv hpivc, hES s hs]
              · rw [if_neg hsp, if_neg hsc2, if_neg hsp, if_neg hsc2, hES s hs]
          · show blockBlowupMap c pv (edgeShearRaw d cse φ u) x = _
            rw [Core.Aoyagi.blockBlowupMap_offCenter_eq c pv (edgeShearRaw d cse φ u) (hxne x hx).2,
              hedgeBS, hvpin, hlin_bs u x hx]
    · -- SHEAR-ID (case11/rollover): `edgeShearRaw = id`, so `σ` FIXES every layer `≥ child_sl` → comp_of_fixing.
      have hedgeId : edgeShearRaw d cse φ = id := by
        rcases hc : cse with _ | _ | _ | _
        · rfl
        · exact absurd (Or.inl hc) hactive
        · exact absurd (Or.inr hc) hactive
        · rfl
      -- pivot below layer `ℓ`: case11 pivot is a below-layer ledger corner; rollover has `c = ∅` (σ = id)
      by_cases hδ : edgeδ d p' = true
      · -- δ = 1
        have hcl : p'.conState.cleared = 0 := of_decide_eq_true hδ
        by_cases hc11 : cse = StepCase.case11
        · -- δ1 case11: child_sl = p'.layer; pivot born strictly below p'.layer
          simp only [hc11] at hpivpin
          have hsce : sc.ecase = StepCase.case11 := hecase.trans hc11
          have hmi : sc.esubst.mergeIdx < p'.conState.numDiv :=
            conOracle_case11_mergeIdx_lt p'.conState sc hsc hsce
          obtain ⟨hval, hlayerLE, hfresh, -⟩ := hpInv
          have hcv := hval ⟨sc.esubst.mergeIdx, hmi⟩
          have hS : (p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).1 < N := hcv.1
          have hrr : (p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).2
              < d (⟨(p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).1, hS⟩ : Fin N).succ :=
            hcv.2.2 _ rfl
          have hcc : (p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).2
              < d (⟨(p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).1, hS⟩ : Fin N).castSucc :=
            hcv.2.1 _ rfl
          have hcpsome : canonPivotOf d p'.conState sc
              = some (tupIdxEquiv d ⟨⟨⟨_, hS⟩, ⟨_, hrr⟩⟩, ⟨_, hcc⟩⟩) := by
            simp only [canonPivotOf, hsce]; rw [dif_pos hmi]
            simp only [cornerToFlat]; rw [dif_pos hS, dif_pos hrr, dif_pos hcc]
          have hpiv : pv = tupIdxEquiv d ⟨⟨⟨_, hS⟩, ⟨_, hrr⟩⟩, ⟨_, hcc⟩⟩ := (hpivpin _ hcpsome).symm
          have hpvlt : (((tupIdxEquiv d).symm pv).1.1 : ℕ) < p'.conState.layer := by
            rw [hpiv, Equiv.symm_apply_apply]
            rcases eq_or_lt_of_le (hlayerLE ⟨sc.esubst.mergeIdx, hmi⟩) with heq | hlt
            · exact absurd (hfresh ⟨sc.esubst.mergeIdx, hmi⟩ heq)
                (by rw [hcl]; exact Nat.not_lt_zero _)
            · exact hlt
          have hcsl : supportLayerOf ns = p'.conState.layer := by
            rcases htrans with ⟨he, _, _, _⟩ | ⟨he, _, _⟩ | ⟨_, hL, hC⟩
            · exact absurd (hsce.symm.trans he) (by simp)
            · rcases he with he | he <;> exact absurd (hsce.symm.trans he) (by simp)
            · rw [hchild] at hL hC; rw [supportLayerOf, hC, hcl, if_pos rfl, hL]
          have hfun : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j
              = fun u => g (fun k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)) := by
            funext u
            show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j u = _
            rw [foldResid, dif_neg hnt, if_pos hδ]; rfl
          rw [hfun]
          have hxne : ∀ x ∈ layerCoords d ℓ, x ≠ pv := by
            intro x hx h
            have hxℓ := decode_layer_of_mem_layerCoords d ℓ x hx
            rw [h] at hxℓ; have hle := hℓsup; rw [hcsl] at hle; omega
          refine homogeneousDeg1On_comp_of_fixing g (layerCoords d ℓ)
            (fun u k => blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)) (fun x hx u => ?_)
            (fun u v hag s hs => ?_) hIH
          · show blockBlowupCoordQuot pv x (edgeShearRaw d cse φ u) = u x
            rw [hedgeId, blockBlowupCoordQuot, if_neg (hxne x hx), id_eq]
          · show blockBlowupCoordQuot pv s (edgeShearRaw d cse φ u)
                = blockBlowupCoordQuot pv s (edgeShearRaw d cse φ v)
            rw [hedgeId, blockBlowupCoordQuot, blockBlowupCoordQuot]
            by_cases hsp : s = pv
            · rw [if_pos hsp, if_pos hsp]
            · rw [if_neg hsp, if_neg hsp]; exact hag s hs
        · -- δ1 rollover: unreachable (rollover needs cleared ≥ widthMinUpto > 0)
          exfalso
          rcases htrans with ⟨_, hge, _, _⟩ | ⟨he, _, _⟩ | ⟨he, _, _⟩
          · have := widthMinUpto_pos hpos (p'.conState.layer + 1); rw [hcl] at hge; omega
          · exact hactive (Or.symm (hecase ▸ he))
          · exact hc11 (hecase.symm.trans he)
      · -- δ = 0: child_sl = p'.layer + 1; σ fixes all layers ≥ p'.layer+1 (blow-up off center, edgeShear id)
        have hδ0 : edgeδ d p' = false := by
          cases h : edgeδ d p' with | false => rfl | true => exact absurd h hδ
        have hcl : p'.conState.cleared ≠ 0 := fun h => by simp [edgeδ, h] at hδ0
        have hcsl : supportLayerOf ns = p'.conState.layer + 1 := by
          rcases htrans with ⟨_, _, hL, hC⟩ | ⟨_, hL, hC⟩ | ⟨_, hL, hC⟩ <;> rw [hchild] at hL hC
          · rw [supportLayerOf, hC, if_pos rfl, hL]
          · rw [supportLayerOf, hC, if_neg (by omega), hL]
          · rw [supportLayerOf, hC, if_neg hcl, hL]
        have hfun : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j
            = fun u => g (stepMapRaw d cse c pv φ u) := by
          funext u
          show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) j u = _
          rw [foldResid, dif_neg hnt, if_neg (by simp [hδ0])]; rfl
        rw [hfun]
        have hxc : ∀ x ∈ layerCoords d ℓ, x ∉ c := by
          intro x hx h
          have hxℓ := decode_layer_of_mem_layerCoords d ℓ x hx
          have := hcb x h; have hle := hℓsup; rw [hcsl] at hle; omega
        by_cases hc11 : cse = StepCase.case11
        · -- case11: the reused pivot sits inside `c`, hence strictly below layer `ℓ`
          simp only [hc11] at hpivpin
          have hsce : sc.ecase = StepCase.case11 := hecase.trans hc11
          have hmi : sc.esubst.mergeIdx < p'.conState.numDiv :=
            conOracle_case11_mergeIdx_lt p'.conState sc hsc hsce
          obtain ⟨hval, hlayerLE, -, -⟩ := hpInv
          have hcv := hval ⟨sc.esubst.mergeIdx, hmi⟩
          have hS : (p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).1 < N := hcv.1
          have hrr : (p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).2
              < d (⟨(p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).1, hS⟩ : Fin N).succ :=
            hcv.2.2 _ rfl
          have hcc : (p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).2
              < d (⟨(p'.conState.divBirthCoord ⟨sc.esubst.mergeIdx, hmi⟩).1, hS⟩ : Fin N).castSucc :=
            hcv.2.1 _ rfl
          have hcpsome : canonPivotOf d p'.conState sc
              = some (tupIdxEquiv d ⟨⟨⟨_, hS⟩, ⟨_, hrr⟩⟩, ⟨_, hcc⟩⟩) := by
            simp only [canonPivotOf, hsce]; rw [dif_pos hmi]
            simp only [cornerToFlat]; rw [dif_pos hS, dif_pos hrr, dif_pos hcc]
          have hcpsomePv : canonPivotOf d p'.conState sc = some pv := by
            rw [hcpsome, ← (hpivpin _ hcpsome)]
          have hpvc : pv ∈ c := by
            rw [hcenter]
            simp only [canonCenterOf, hsce, Finset.mem_union, Option.mem_toFinset, Option.mem_def]
            exact Or.inl hcpsomePv
          have hpivc : pv ∉ layerCoords d ℓ := by
            intro h
            have := decode_layer_of_mem_layerCoords d ℓ pv h
            have := hcb pv hpvc; have hle := hℓsup; rw [hcsl] at hle; omega
          refine homogeneousDeg1On_comp_of_fixing g (layerCoords d ℓ) (stepMapRaw d cse c pv φ)
            (fun x hx u => ?_) (fun u v hag s hs => ?_) hIH
          · show blockBlowupMap c pv (edgeShearRaw d cse φ u) x = u x
            rw [Core.Aoyagi.blockBlowupMap_offCenter_eq c pv (edgeShearRaw d cse φ u) (hxc x hx),
              hedgeId, id_eq]
          · show blockBlowupMap c pv (edgeShearRaw d cse φ u) s
              = blockBlowupMap c pv (edgeShearRaw d cse φ v) s
            have hES : ∀ w, w ∉ layerCoords d ℓ → edgeShearRaw d cse φ u w = edgeShearRaw d cse φ v w := by
              intro w hw; rw [hedgeId]; exact hag w hw
            unfold blockBlowupMap
            by_cases hsp : s = pv
            · rw [if_pos hsp, if_pos hsp]; exact hES pv hpivc
            · by_cases hsc2 : s ∈ c
              · rw [if_neg hsp, if_pos hsc2, if_neg hsp, if_pos hsc2, hES pv hpivc, hES s hs]
              · rw [if_neg hsp, if_neg hsc2, if_neg hsp, if_neg hsc2, hES s hs]
        · -- rollover: `c = ∅`, so the blow-up is the identity — `σ = id`, fixing everything
          have hcroll : cse = StepCase.rollover := by
            rcases hc : cse with _ | _ | _ | _
            · exact absurd hc hc11
            · exact absurd (Or.inl hc) hactive
            · exact absurd (Or.inr hc) hactive
            · rfl
          have hc0 : c = (∅ : Finset (Fin (flatDim d))) := by
            rw [hcenter]; simp only [canonCenterOf, hecase.trans hcroll]
          have hemp : ∀ z : Fin (flatDim d), z ∉ (∅ : Finset (Fin (flatDim d))) := fun z => by simp
          refine homogeneousDeg1On_comp_of_fixing g (layerCoords d ℓ) (stepMapRaw d cse c pv φ)
            (fun x hx u => ?_) (fun u v hag s hs => ?_) hIH
          · show blockBlowupMap c pv (edgeShearRaw d cse φ u) x = u x
            rw [hc0, Core.Aoyagi.blockBlowupMap_offCenter_eq ∅ pv (edgeShearRaw d cse φ u)
              (hemp x), hedgeId, id_eq]
          · show blockBlowupMap c pv (edgeShearRaw d cse φ u) s
              = blockBlowupMap c pv (edgeShearRaw d cse φ v) s
            rw [hc0, Core.Aoyagi.blockBlowupMap_offCenter_eq ∅ pv (edgeShearRaw d cse φ u)
              (hemp s),
              Core.Aoyagi.blockBlowupMap_offCenter_eq ∅ pv (edgeShearRaw d cse φ v)
              (hemp s), hedgeId]
            exact hag s hs

end DLNFibre.DLN.Aoyagi
