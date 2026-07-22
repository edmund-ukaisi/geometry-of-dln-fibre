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
open DLNFibre.Core DLNFibre.Core.Aoyagi

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
theorem foldResid_layerHomogeneous' (d : Fin (N + 1) → ℕ)
    (p : TreePath d) (hnonterm : ¬ N ≤ p.conState.layer)
    (hbranch : p.IsRealBranch (canonFlatten d))
    (j : Fin (foldNR d p)) (ℓ : ℕ)
    (hℓsup : supportLayerOf p.conState ≤ ℓ) (hℓN : ℓ < N) :
    HomogeneousDeg1On (foldResid d (canonFlatten d) p j) (layerCoords d ℓ)
      (foldRegion d (canonFlatten d) p) := by
  sorry

end DLNFibre.DLN.Aoyagi
