import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.MergeBoostSplit
import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `DLN.Aoyagi.Case1Wire` — the wall's crux, wired to the fold defs (SEAT-L4)

The reusable per-entry FIX-RESID identity that discharges the δ=1 divisibility of
`case1_preserves_stepInv` (and `case2` δ=1) against the CONCRETE fold defs (`foldResid`, `stepMap`,
`edgeShear`), using `Deg1SupportedOn`'s center-exact degree-1 structure + seat-L4's `BlockDivision`
FIX-A enabler. Kept in a separate file (not `MonumentAtlas`) during the canonCenter parallel-dev round.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **The edge shear keeps the pivot coordinate** — `id` at case11/rollover, `blockShear` (via
`hshear_pivot`) at case12/case2. The uniform fact the FIX-A center-division consumes. -/
theorem edgeShear_keeps_pivot (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (u : Fin (flatDim d) → ℝ) : edgeShear d ed u ed.pivot = u ed.pivot := by
  change edgeShearRaw d ed.case ed.shearφ u ed.pivot = u ed.pivot
  cases ed.case
  · rfl                       -- case11: `id`
  · exact ed.hshear_pivot u   -- case12: `blockShear`
  · exact ed.hshear_pivot u   -- case2:  `blockShear`
  · rfl                       -- rollover: `id`

/-- **The FIX-RESID per-entry identity (the wall's δ=1 crux).** For a `Deg1SupportedOn` parent residual
(center `ed.center`), the parent residual pulled back through `stepMap` (blow-up OUTERMOST) factors as
`u_pivot ·` the residual at the `blockBlowupCoordQuot`-map (the strict transform): each center
coordinate gains the pivot factor (`blockBlowupMap_shear_center_eq`, FIX-A) and the center-DISJOINT
coefficient is unchanged (`IgnoresCoords`, since `stepMap u` and the quot-map agree off the center). -/
theorem foldResid_stepMap_eq_pivot_mul (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (j : Fin (foldNR d p)) (u : Fin (flatDim d) → ℝ) :
    foldResid d e p j (stepMap d ed u)
      = u ed.pivot
        * foldResid d e p j (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  classical
  -- the quot-map and its off-center agreement with `stepMap u`
  set qm : Fin (flatDim d) → ℝ := fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) with hqm
  set σu : Fin (flatDim d) → ℝ := stepMap d ed u with hσu
  have hσu_eq : ∀ k, σu k = blockBlowupMap ed.center ed.pivot (edgeShear d ed u) k := fun k ↦ rfl
  -- off-center, `σu` and `qm` agree (spectators of the blow-up are the shear's values; the coord quot
  -- off-pivot is the shear's value too).
  have hagree : ∀ s, s ∉ ed.center → σu s = qm s := by
    intro s hs
    have hsp : s ≠ ed.pivot := fun h ↦ hs (h ▸ ed.hpivot)
    rw [hσu_eq s, blockBlowupMap_spectator_eq ed.center ed.hpivot hs (edgeShear d ed u), hqm]
    change edgeShear d ed u s = (if s = ed.pivot then (1 : ℝ) else edgeShear d ed u s)
    rw [if_neg hsp]
  -- the Deg1 witness for entry `j`
  obtain ⟨c, _hc, hrepr, hign⟩ := hdeg1 j
  have hmem : ∀ w : Fin (flatDim d) → ℝ, w ∈ foldRegion d e p := by
    rw [foldRegion_eq_univ]; exact fun w ↦ Set.mem_univ w
  -- coefficients agree at `σu` and `qm` (they agree off center; `c i` ignores center)
  have hceq : ∀ i, c i σu = c i qm := by
    intro i
    have := (ignoresCoords_univ_iff_agree (c i) ed.center)
    rw [foldRegion_eq_univ] at hign
    exact (this.mp (hign i)) σu qm hagree
  rw [hrepr σu (hmem _), hrepr qm (hmem _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  have hcenter : σu i = u ed.pivot * qm i := by
    rw [hσu_eq i, hqm]
    exact blockBlowupMap_shear_center_eq ed.center ed.pivot hi (edgeShear d ed)
      (edgeShear_keeps_pivot d ed) u
  rw [hceq i, hcenter]; ring

/-! ### Child-state reductions (conjunct-2 plumbing, seat-L4)

The `foldResid`/`foldNR` values at a non-terminal child `p.extend ed`, split by `edgeδ`. Consumed
by `case1_preserves_stepInv`'s conjunct-2 (the descend of `Deg1SupportedSlot`, parent to child). All
proof-free reductions off the fold defs; `hlt : ¬ N ≤ ed.nextState.layer` comes from `hlayer`. -/

/-- The child residual width is the parent's at a non-terminal step (`foldNR` collapses to `1` only
at a TERMINAL child). -/
theorem foldNR_extend_of_lt (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) : foldNR d (p.extend ed) = foldNR d p := by
  change (if N ≤ ed.nextState.layer then 1 else foldNR d p) = foldNR d p
  rw [if_neg hlt]

/-- **δ=1 child residual = parent's STRICT TRANSFORM** at a non-terminal case edge: the
pivot-quotiented sheared point (`blockBlowupCoordQuot` removes the blow-up `u_pivot`). -/
theorem foldResid_extend_delta1 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = true)
    (j : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    foldResid d e (p.extend ed) j u
      = foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j)
          (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  change foldResid d e (TreePath.step p ed.center ed.pivot ed.case ed.nextState ed.shearφ) j u = _
  rw [foldResid, dif_neg hlt, if_pos hδ]; rfl

/-- **δ=0 child residual = parent's PULLBACK** at a non-terminal case edge (no `u_pivot`). -/
theorem foldResid_extend_delta0 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = false)
    (j : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    foldResid d e (p.extend ed) j u
      = foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j) (stepMap d ed u) := by
  change foldResid d e (TreePath.step p ed.center ed.pivot ed.case ed.nextState ed.shearφ) j u = _
  rw [foldResid, dif_neg hlt, if_neg (by simp [hδ])]; rfl

/-! ### The case-generic re-factoring core (conjunct-2, ∃c half) — seat-L4

The shear-graded substitution re-factors into a DIRECT `S'`-support decomposition. CASE-GENERIC:
both `case1` and `case2` conjunct-2 reduce their child residual (parent supported on `S'`, evaluated
through the step map, each `S'`-image `S'`-graded by `ShearGrades (a)`) to this shape, so this ONE
lemma supplies the `∃c` (first) conjunct of `Deg1SupportedSlot` for both. It is the double-sum swap
`∑_{i∈S'} a i·(∑_{k∈S'} b i k·u k) = ∑_{k∈S'} (∑_{i∈S'} a i·b i k)·u k` plus continuity — abstract
over the fold, so ruling-invariant (it consumes the graded form as `hchild`, whatever the fixed
`DescendView`/`ShearGrades` shape delivers). It does NOT supply the `PerLayerDeg1From` (second)
conjunct — that needs the layerwise-affine strengthening of `ShearGrades (a)` (the `c i k` must ignore
`S'`, else `σ_s = u_s + u_r²` slips through degree-2). -/
theorem exists_graded_decomp {D : ℕ} (S' : Finset (Fin D)) (V : Set (Fin D → ℝ))
    (child : (Fin D → ℝ) → ℝ) (a : Fin D → (Fin D → ℝ) → ℝ) (b : Fin D → Fin D → (Fin D → ℝ) → ℝ)
    (ha : ∀ i, ContinuousOn (a i) V) (hb : ∀ i k, ContinuousOn (b i k) V)
    (hchild : ∀ u ∈ V, child u = ∑ i ∈ S', a i u * ∑ k ∈ S', b i k u * u k) :
    ∃ c : Fin D → (Fin D → ℝ) → ℝ,
      (∀ k, ContinuousOn (c k) V) ∧ (∀ u ∈ V, child u = ∑ k ∈ S', c k u * u k) := by
  refine ⟨fun k u ↦ ∑ i ∈ S', a i u * b i k u, fun k ↦ ?_, fun u hu ↦ ?_⟩
  · exact continuousOn_finset_sum _ (fun i _ ↦ (ha i).mul (hb i k))
  · rw [hchild u hu]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ ↦ Finset.sum_congr rfl (fun i _ ↦ by ring))

/-! ### Conjunct-1 (divisibility ∃q) — the δ=0 PULLBACK branch (case-generic; seat-L4)

At a δ=0 (`edgeδ d p = false`, i.e. `p.conState.cleared ≠ 0`) non-terminal edge, `foldB` gains NO
`u_pivot` (`(u pivot)^0 = 1`) and `foldResid` is the pure pullback, so the child `StepInv` witness is
`q' = q ∘ stepMap` (reindexed by the `foldNR` cast). Shared by case1 and case2's δ=0 sub-cases. -/
theorem stepInv_child_delta0 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = false)
    (q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ)
    (hq : StepInv (coreGen d e) (foldG d e p) (foldB d e p) (foldResid d e p) q (foldRegion d e p)) :
    ∃ q' : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (foldResid d e (p.extend ed)) q' (foldRegion d e (p.extend ed)) := by
  classical
  obtain ⟨hqc, hq0, hqd⟩ := hq
  have hcast := foldNR_extend_of_lt d ed hlt
  have hg : foldG d e (p.extend ed) = foldG d e p ∘ stepMap d ed := rfl
  have hb : ∀ u, foldB d e (p.extend ed) u = foldB d e p (stepMap d ed u) := by
    intro u; rw [foldB_extend_eq]; simp [hδ]
  have hmem : ∀ w : Fin (flatDim d) → ℝ, w ∈ foldRegion d e p := by
    rw [foldRegion_eq_univ]; exact fun w ↦ Set.mem_univ w
  refine ⟨fun i j' u ↦ q i (Fin.cast hcast j') (stepMap d ed u), ?_, ?_, ?_⟩
  · intro i j'
    have hc : Continuous (q i (Fin.cast hcast j')) :=
      continuousOn_univ.mp (by rw [← foldRegion_eq_univ e p]; exact hqc i (Fin.cast hcast j'))
    exact (hc.comp (continuous_stepMap d ed)).continuousOn
  · intro i
    show (coreGen d e i ∘ foldG d e (p.extend ed)) 0 = 0
    rw [hg]
    show (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) = 0
    rw [stepMap_zero]; exact hq0 i
  · intro u _ i
    show (coreGen d e i ∘ foldG d e (p.extend ed)) u = _
    rw [hg]
    show (coreGen d e i ∘ foldG d e p) (stepMap d ed u) = _
    rw [hqd (stepMap d ed u) (hmem _) i]
    refine (Equiv.sum_comp (finCongr hcast)
      (fun j ↦ q i j (stepMap d ed u) * (foldB d e p (stepMap d ed u) * foldResid d e p j (stepMap d ed u)))).symm.trans ?_
    refine Finset.sum_congr rfl (fun j' _ ↦ ?_)
    simp only [finCongr_apply]
    rw [hb, foldResid_extend_delta0 d e ed hlt hδ]

/-! ### The Deg1 bridge — support-decomp + AffineOn ⟹ center-IgnoresCoords support-decomp (seat-L4)

The δ=1 append crux consumes `Deg1SupportedOn` (a support-decomposition whose coefficients IGNORE the
center). `FoldStepInvAt`'s `Deg1SupportedSlot` gives a support-decomposition (∃c) PLUS `AffineOn` on the
support layer `X ⊇ S`, but the `∃c` need not ignore `S`. This bridge builds the IgnoresCoords form
(Codex-confirmed, TRUE, no extra hypothesis): the `AffineOn` witness `b` gives `c'ᵢ := bᵢ` (ignores
`X ⊇ S`); `a ≡ 0` and `b_x ≡ 0` for `x ∈ X∖S` are FORCED by the support-decomp vanishing at the reset
points; continuity is `c'ᵢ u = F(Pᵢ u) − F(P₀ u)`. Mechanism: fiberwise affine uniqueness in the freely
variable `X`-coords (NOT polynomial), evaluated at `0` and the unit vectors via `ignoresCoords_univ_iff_agree`. -/
theorem exists_ignoresCoords_decomp {D : ℕ} (F : (Fin D → ℝ) → ℝ) (S X : Finset (Fin D)) (hSX : S ⊆ X)
    (c : Fin D → (Fin D → ℝ) → ℝ) (hc : ∀ i, Continuous (c i))
    (hrepr : ∀ u, F u = ∑ i ∈ S, c i u * u i) (haff : AffineOn F X Set.univ) :
    ∃ c' : Fin D → (Fin D → ℝ) → ℝ, (∀ i, Continuous (c' i)) ∧
      (∀ u, F u = ∑ i ∈ S, c' i u * u i) ∧ (∀ i, IgnoresCoords (c' i) S Set.univ) := by
  classical
  obtain ⟨a, b, hai, hbi, hdecomp⟩ := haff
  -- F is continuous (finite sum of continuous · projection)
  have hF : Continuous F := by
    have : F = fun u ↦ ∑ i ∈ S, c i u * u i := funext hrepr
    rw [this]; exact continuous_finset_sum S (fun i _ ↦ (hc i).mul (continuous_apply i))
  -- reset maps: P₀ sends X-coords to 0; Pᵢ sends X-coords to the unit vector at i
  set P0 : (Fin D → ℝ) → (Fin D → ℝ) := fun u k ↦ if k ∈ X then 0 else u k with hP0
  set Pv : Fin D → (Fin D → ℝ) → (Fin D → ℝ) :=
    fun i u k ↦ if k ∈ X then (if k = i then 1 else 0) else u k with hPv
  have hP0c : Continuous P0 := by
    apply continuous_pi; intro k
    by_cases hk : k ∈ X
    · simp only [hP0, if_pos hk]; exact continuous_const
    · simp only [hP0, if_neg hk]; exact continuous_apply k
  have hPvc : ∀ i, Continuous (Pv i) := by
    intro i; apply continuous_pi; intro k
    by_cases hk : k ∈ X
    · simp only [hPv, if_pos hk]; exact continuous_const
    · simp only [hPv, if_neg hk]; exact continuous_apply k
  -- agreement off X (⊇ S) — for the IgnoresCoords/AffineOn evaluations
  have hai' := (ignoresCoords_univ_iff_agree a X).mp hai
  have hbi' : ∀ x ∈ X, ∀ u v, (∀ s, s ∉ X → u s = v s) → b x u = b x v :=
    fun x hx ↦ (ignoresCoords_univ_iff_agree (b x) X).mp (hbi x hx)
  -- a u = F(P₀ u): AffineOn at P₀ u (X-coords 0), a ignores X
  have haP0 : ∀ u, F (P0 u) = a u := by
    intro u
    rw [hdecomp (P0 u) (Set.mem_univ _)]
    have h1 : a (P0 u) = a u := hai' _ _ (fun s hs ↦ by simp [hP0, hs])
    have h2 : ∑ x ∈ X, b x (P0 u) * (P0 u) x = 0 :=
      Finset.sum_eq_zero fun x hx ↦ by simp only [hP0, if_pos hx, mul_zero]
    rw [h1, h2, add_zero]
  -- b x u = F(Pₓ u) − a u
  have hbPv : ∀ i, i ∈ X → ∀ u, F (Pv i u) = a u + b i u := by
    intro i hi u
    rw [hdecomp (Pv i u) (Set.mem_univ _)]
    have h1 : a (Pv i u) = a u := hai' _ _ (fun s hs ↦ by simp [hPv, hs])
    have h2 : ∑ x ∈ X, b x (Pv i u) * (Pv i u) x = b i u := by
      rw [Finset.sum_eq_single_of_mem i hi (fun x hx hxi ↦ by
        have hv : (Pv i u) x = 0 := by simp [hPv, hx, hxi]
        rw [hv, mul_zero])]
      have hbeq : b i (Pv i u) = b i u := hbi' i hi _ _ (fun s hs ↦ by simp [hPv, hs])
      have hval : (Pv i u) i = 1 := by simp [hPv, hi]
      rw [hval, mul_one, hbeq]
    rw [h1, h2]
  -- a ≡ 0: the support-decomp vanishes at P₀ u (S-coords are 0)
  have ha0 : ∀ u, a u = 0 := by
    intro u; rw [← haP0 u, hrepr (P0 u)]
    exact Finset.sum_eq_zero fun i hi ↦ by simp [hP0, hSX hi]
  -- b x ≡ 0 for x ∈ X∖S: the support-decomp vanishes at Pₓ u (S-coords are 0 since x ∉ S)
  have hbXS : ∀ x ∈ X, x ∉ S → ∀ u, b x u = 0 := by
    intro x hx hxS u
    have hv := hbPv x hx u
    rw [ha0, zero_add] at hv
    rw [← hv, hrepr (Pv x u)]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hix : i ≠ x := fun h ↦ hxS (h ▸ hi)
    have hv0 : (Pv x u) i = 0 := by simp [hPv, hSX hi, hix]
    rw [hv0, mul_zero]
  refine ⟨fun i u ↦ F (Pv i u) - F (P0 u), fun i ↦ (hF.comp (hPvc i)).sub (hF.comp hP0c), ?_, ?_⟩
  · intro u
    -- F u = a u + ∑_{x∈X} b x·u x = ∑_{i∈S} b i·u i  (a≡0, b_{X∖S}≡0); c'ᵢ u = b i u
    rw [hdecomp u (Set.mem_univ _), ha0 u, zero_add, ← Finset.sum_sdiff hSX,
      Finset.sum_eq_zero (fun x hx ↦ by
        rw [hbXS x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2, zero_mul]), zero_add]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    show b i u * u i = (F (Pv i u) - F (P0 u)) * u i
    rw [hbPv i (hSX hi) u, haP0 u]; ring
  · intro i
    rw [ignoresCoords_univ_iff_agree]
    intro u v hagree
    have hPve : Pv i u = Pv i v := funext fun k ↦ by
      by_cases hk : k ∈ X
      · simp only [hPv, if_pos hk]
      · simp only [hPv, if_neg hk]; exact hagree k fun h ↦ hk (hSX h)
    have hP0e : P0 u = P0 v := funext fun k ↦ by
      by_cases hk : k ∈ X
      · simp only [hP0, if_pos hk]
      · simp only [hP0, if_neg hk]; exact hagree k fun h ↦ hk (hSX h)
    simp only [hPve, hP0e]

/-- The append-case (case12/case2) canonical center sits within its layer's coords — the `S ⊆ X`
input the Deg1 bridge needs (`ed.center ⊆ layerCoords(support layer)` at δ=1, via `centerPin`). -/
theorem canonCenterOf_append_subset_layerCoords {N : ℕ} (d : Fin (N + 1) → ℕ) (s : ConState N)
    (sc : StepChild d s) (hcase : sc.ecase = StepCase.case12 ∨ sc.ecase = StepCase.case2) :
    canonCenterOf d s sc ⊆ layerCoords d s.layer := by
  have harm : canonCenterOf d s sc = (Finset.univ.filter (fun q : tupIdx d =>
      (q.1.1 : ℕ) = s.layer ∧ s.cleared ≤ (q.1.2 : ℕ) ∧ s.cleared ≤ (q.2 : ℕ) ∧
        (q.2 : ℕ) < widthMinUpto d s.layer)).image (tupIdxEquiv d) := by
    rcases hcase with h | h <;> · unfold canonCenterOf; rw [h]
  rw [harm, layerCoords]
  intro x hx
  rw [Finset.mem_image] at hx ⊢
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2.1⟩, rfl⟩

/-! ### δ=1 append: the parent residual is `Deg1SupportedOn` the LEDGER center (seat-L4)

Assembles the crux's input for the δ=1 case12/case2 branch: from the carried `Deg1SupportedSlot` on
`supportAt(parent)` (`hinv`) plus the construction pins — `realBranch_cover` (`supportAt ⊆ ed.center`, at
δ=1), `realBranch_centerPin` (`ed.center = canonCenterOf`, giving `ed.center ⊆ layerCoords` via the
append-subset lemma), and `PerLayerDeg1From`'s `AffineOn` at the support layer — the Deg1 bridge yields
`Deg1SupportedOn (foldResid p) ed.center`. -/
theorem deg1SupportedOn_center_of_hslot {N : ℕ} (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hcase : ed.case = StepCase.case12 ∨ ed.case = StepCase.case2)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState) (foldRegion d e p)) :
    Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p) := by
  classical
  have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ
  have hsl : supportLayerOf p.conState = p.conState.layer := by simp [supportLayerOf, hcl]
  have hcov : supportAt d p.conState.layer p.conState.cleared ⊆ ed.center :=
    realBranch_cover e p ed hbranch hδ hcase
  -- extract the oracle step child sc from IsRealBranch (ecase, center-pin)
  obtain ⟨-, ⟨sc, _, hecase, -, hcenterEq, -⟩, -⟩ := hbranch
  have hXsub : ed.center ⊆ layerCoords d p.conState.layer := by
    rw [hcenterEq]
    exact canonCenterOf_append_subset_layerCoords d p.conState sc (by rw [hecase]; exact hcase)
  intro j
  rw [foldRegion_eq_univ e p]
  obtain ⟨⟨c, hc, hcrepr⟩, hpl⟩ := hslot j
  -- pad the supportAt-decomposition to the (larger) ledger center ed.center, then apply the bridge
  obtain ⟨c', hc'cont, hc'repr, hc'ign⟩ := exists_ignoresCoords_decomp (foldResid d e p j) ed.center
    (layerCoords d p.conState.layer) hXsub
    (fun i u ↦ if i ∈ supportAt d p.conState.layer p.conState.cleared then c i u else 0)
    (fun i ↦ by
      by_cases hi : i ∈ supportAt d p.conState.layer p.conState.cleared
      · simp only [hi, if_true]
        exact continuousOn_univ.mp (by rw [← foldRegion_eq_univ e p]; exact hc i)
      · simp only [hi, if_false]; exact continuous_const)
    (fun u ↦ by
      rw [hcrepr u (by rw [foldRegion_eq_univ]; exact Set.mem_univ _),
        ← Finset.sum_subset hcov (fun i _ hi ↦ by simp [hi])]
      exact Finset.sum_congr rfl (fun i hi ↦ by simp [hi]))
    (by have := hpl p.conState.layer (le_of_eq hsl); rwa [foldRegion_eq_univ] at this)
  exact ⟨c', fun i ↦ (hc'cont i).continuousOn, fun u _ ↦ hc'repr u, hc'ign⟩

/-- **Conjunct-1 δ=1 APPEND branch** (case12/case2): the child `StepInv` witness is `q'=q∘stepMap` — the
`u_pivot` from `foldB`'s `(u pivot)^1` factor is matched by the crux moving it out of the residual
(`foldResid_p(stepMap) = u_pivot·foldResid_p(qm)`). Consumes `Deg1SupportedOn ed.center`
(`deg1SupportedOn_center_of_hslot`). -/
theorem stepInv_child_delta1_append (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = true)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ)
    (hq : StepInv (coreGen d e) (foldG d e p) (foldB d e p) (foldResid d e p) q (foldRegion d e p)) :
    ∃ q' : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (foldResid d e (p.extend ed)) q' (foldRegion d e (p.extend ed)) := by
  classical
  obtain ⟨hqc, hq0, hqd⟩ := hq
  have hcast := foldNR_extend_of_lt d ed hlt
  have hg : foldG d e (p.extend ed) = foldG d e p ∘ stepMap d ed := rfl
  have hb : ∀ u, foldB d e (p.extend ed) u = u ed.pivot * foldB d e p (stepMap d ed u) := by
    intro u; rw [foldB_extend_eq, hδ]; simp
  have hmem : ∀ w : Fin (flatDim d) → ℝ, w ∈ foldRegion d e p := by
    rw [foldRegion_eq_univ]; exact fun w ↦ Set.mem_univ w
  refine ⟨fun i j' u ↦ q i (Fin.cast hcast j') (stepMap d ed u), ?_, ?_, ?_⟩
  · intro i j'
    have hc : Continuous (q i (Fin.cast hcast j')) :=
      continuousOn_univ.mp (by rw [← foldRegion_eq_univ e p]; exact hqc i (Fin.cast hcast j'))
    exact (hc.comp (continuous_stepMap d ed)).continuousOn
  · intro i
    show (coreGen d e i ∘ foldG d e (p.extend ed)) 0 = 0
    rw [hg]; show (coreGen d e i ∘ foldG d e p) (stepMap d ed 0) = 0
    rw [stepMap_zero]; exact hq0 i
  · intro u _ i
    show (coreGen d e i ∘ foldG d e (p.extend ed)) u = _
    rw [hg]; show (coreGen d e i ∘ foldG d e p) (stepMap d ed u) = _
    rw [hqd (stepMap d ed u) (hmem _) i]
    refine (Equiv.sum_comp (finCongr hcast)
      (fun j ↦ q i j (stepMap d ed u) *
        (foldB d e p (stepMap d ed u) * foldResid d e p j (stepMap d ed u)))).symm.trans ?_
    refine Finset.sum_congr rfl (fun j' _ ↦ ?_)
    simp only [finCongr_apply]
    rw [hb, foldResid_extend_delta1 d e ed hlt hδ,
      foldResid_stepMap_eq_pivot_mul d e ed hdeg1 (Fin.cast hcast j') u]
    ring

/-! ### The WALL — primed leaf `case1_preserves_stepInv'` (SEAT-L4, primed-leaf pattern)

Statement-identical to `MonumentAtlas.case1_preserves_stepInv`; the controller swaps the MonumentAtlas
`sorry` to `:= case1_preserves_stepInv' …` at the summit cleanup (same pattern as `Case2Wire`'s
`case2_preserves_stepInv'` / L8's `leafPath_realizesExponents'`). Lands HERE (not `MonumentAtlas`)
because the divisibility engine it consumes lives downstream of `MonumentAtlas`. The dispatch is
verified correct; the two frontier obligations are named holes (elder-ruling-pending). -/

/-- **case11 δ=1 BOOST-READINESS** (Codex xhigh 2026-07-22; RULING B — statement blessed). DELEGATED to
`realBranch_boostReady_case11'` (MergeBoostSplit) — proven via the content lemma + the algebraic assembly;
the wall's ONLY remaining debt is `foldResid_case11_mergeBoostSplit_canon`. For a real case1(1) edge at δ=1, the parent residual is `Deg1SupportedOn`
the LEDGER (boost) center `ed.center = {pivot} ∪ partial-block` — even though its GEOMETRIC support
`supportAt` is the larger full layer block: the untouched (`support ∖ center`) terms carry `u_pivot` in
their non-dominant b-chain coefficient `b_i/b_1`. Blessed in place; derives from the `CanonicalSchurStep`
conjunct (via `realBranch_canonicalSchurStep`) + the b-chain, re-expressing the carried parent slot
(`hslot`) over the boost center. Feeds `stepInv_child_delta1_append` exactly like the case12 cover route.
PIN `he : e = canonFlatten d` (idiom ruling): the b-chain factoring is a `canonFlatten`-alignment fact,
false at general/linear `e`; born here. -/
theorem realBranch_boostReady_case11 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d) {p : TreePath d}
    (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p) :=
  -- DELEGATED to the proven primed variant (MergeBoostSplit): the wall's ONLY remaining debt is the
  -- content lemma `foldResid_case11_mergeBoostSplit_canon` (the assembly + the reduction are kernel-proven).
  realBranch_boostReady_case11' d e he ed hδ hc11 hbranch hslot

/-- **Conjunct A (divisibility ∃q) of the wall — dispatched.** δ=0 → `stepInv_child_delta0`
(case-generic pullback, BANKED); δ=1 case12 → `stepInv_child_delta1_append` fed
`deg1SupportedOn_center_of_hslot` (cover route, BANKED); δ=1 case11 → `stepInv_child_delta1_append` fed
`realBranch_boostReady_case11` (the boost-center Deg1 obligation). The SAME append lemma closes both δ=1
sub-cases — only the `Deg1SupportedOn ed.center` source differs.

PIN (idiom ruling 2026-07-23): the case11 derivation carries `he : e = canonFlatten d` (the concrete
flatten aligns the flat coords so the reused-pivot coordinate factors cleanly — false at general/linear
`e`, the `(1,1,1)` unipotent-scrambler countermodel). `case1_conjA` supplies it to the wall for the
case11 branch (δ=0 / δ=1-case12 branches ignore it). -/
theorem case1_conjA (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    ∃ q : Fin (d (Fin.last N) * d 0) → Fin (foldNR d (p.extend ed)) → (Fin (flatDim d) → ℝ) → ℝ,
      StepInv (coreGen d e) (foldG d e (p.extend ed)) (foldB d e (p.extend ed))
        (foldResid d e (p.extend ed)) q (foldRegion d e (p.extend ed)) := by
  classical
  have hlt : ¬ N ≤ ed.nextState.layer := Nat.not_le.mpr (by omega)
  obtain ⟨q, hq⟩ := hinv.1
  by_cases hδ : edgeδ d p = true
  · rcases hcase1 with hc11 | hc12
    · -- δ=1 case11: boost-readiness → append crux
      exact stepInv_child_delta1_append d e ed hlt hδ
        (realBranch_boostReady_case11 d e he ed hδ hc11 hbranch hinv.2) q hq
    · -- δ=1 case12: cover route → append crux
      exact stepInv_child_delta1_append d e ed hlt hδ
        (deg1SupportedOn_center_of_hslot d e ed hδ (Or.inl hc12) hbranch hinv.2) q hq
  · -- δ=0: pure pullback (case-generic)
    have hδ0 : edgeδ d p = false := by
      cases h : edgeδ d p with
      | false => rfl
      | true => exact absurd h hδ
    exact stepInv_child_delta0 d e ed hlt hδ0 q hq

/-- **⟨THE WALL — primed⟩** `case1_preserves_stepInv'`, statement-identical to
`MonumentAtlas.case1_preserves_stepInv`. Conjunct A is `case1_conjA` (dispatched; consumes the
boost-readiness obligation for the δ=1 case11 sub-branch); conjunct B is the shared child
`Deg1SupportedSlot` descent — CLOSED via the step-form `realBranch_multiAffine_step` (parent slot from
`hinv.2` + the child branch `hbranch`), identical to `Case2Wire.case2_preserves_stepInv'`'s conjunct B. -/
theorem case1_preserves_stepInv'
    (d : Fin (N + 1) → ℕ) (hN : 0 < N) (hpos : ∀ k, 0 < d k)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he : e = canonFlatten d)
    (p : TreePath d) (ed : TreeEdge d p) (hcase1 : ed.isCase1)
    (hlayer : ed.nextState.layer + 1 < N)
    (hinv : FoldStepInvAt d e (supportAt d p.conState.layer p.conState.cleared) p)
    (hbranch : (p.extend ed).IsRealBranch e) :
    FoldStepInvAt d e
      (supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared) (p.extend ed) := by
  refine ⟨case1_conjA d e he p ed hcase1 hlayer hinv hbranch, ?_⟩
  -- CONJUNCT B — child `Deg1SupportedSlot` on `supportAt(child)` (the descended block); CLOSED via the
  -- step-form `realBranch_multiAffine_step`: parent slot (`hinv.2`) + child branch (`hbranch`) → child slot.
  exact realBranch_multiAffine_step hpos e p ed hlayer hbranch hinv.2

end DLNFibre.DLN.Aoyagi
