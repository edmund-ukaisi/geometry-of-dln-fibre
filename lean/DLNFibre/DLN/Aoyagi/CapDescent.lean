import DLNFibre.DLN.Aoyagi.SourceClearedResid
import DLNFibre.DLN.Aoyagi.MultiAffineHomogWire
import DLNFibre.DLN.Aoyagi.LeafChartWire

/-!
# `DLN.Aoyagi.CapDescent` — the cap-frontier render (SEAT-CAPF)

Closes the support-descent frontier at the FRESH-after-rollover WIDE interior node: the primed twin
`realBranch_appendResidDescent_fresh_sourceCleared'` of `SourceClearedResid.lean`'s §12.2 obligation (b).

The mechanism (pnp cap-transport hinge, `verify/capstone_cap_transport.py`; TRANSPORTS verdict): on a WIDE
branch (`d_{S+1} > widthMinUpto S`) the RAW fold reads the out-of-cap columns
(`layerCoords ∖ blockCoords`) — the capped raw descent is FALSE there (the cap-escape,
`recoord-cap-escape-note.md`). But the SOURCE-CLEARED residual `foldResid ∘ couplingClear` does NOT read
them: the escaped-column coefficients factor through the ancestor coupling coordinates, which
`couplingClear` zeroes — a FUNCTION-level kill, not a set-level containment (the escaped coords are NOT in
`couplingCoords`). So obligation (b) = the raw UNCAPPED descent ∘ `couplingClear` + the KILL.

Pieces (this module, all additive — touches no existing file):
* `continuous_foldResid` — the fold residual is continuous (`blockBlowupCoordQuot` is a projection, not a
  division), needed by the AffineOn → continuous-decomposition bridge.
* `continuous_decomp_of_homogeneousDeg1On` — the (L2) bridge: `Continuous F` + `HomogeneousDeg1On F X` ⟹
  a continuous, `X`-`IgnoresCoords` support decomposition over `X` (mirrors `Case1Wire`'s
  `exists_ignoresCoords_decomp`, with `F`-continuity as a hypothesis and the zero-constant part from the
  homogeneity vanishing clause).
* `couplingCoords_decode_layer_le` — the (L1) separation: every ancestor coupling coordinate decodes to a
  layer `≤ p.conState.layer`, so at a fresh rollover child (layer advances) `couplingClear` FIXES every
  coordinate at layers `≥` the child layer.
* `realBranch_appendResidDescent_fresh_layerCoords` — the raw UNCAPPED descent: `Deg1SupportedSlot` of the
  raw fold over the FULL descended layer `layerCoords` (NOT `blockCoords` — capped is false wide), from
  `foldResid_layerHomogeneous'` (H) + continuity.
* `sourceClearedResid_ignoresEscaped` — the KILL: the source-cleared residual ignores the escaped
  out-of-cap columns (the genuinely new content).
* `realBranch_appendResidDescent_fresh_sourceCleared'` — the primed (b)-twin (statement byte-identical to
  `SourceClearedResid.lean`'s), assembled from the raw uncapped descent ∘ `couplingClear` + the KILL +
  the separation.

Cross-ref honesty: `sourceClearedResid` is RLCT-equivalent to Aoyagi's `D_J` via the source-clear
rendering (coordinate-form differs by our shear-frame), NOT coordinate-identical.
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **`readEntry` is continuous** — it reads a fixed flat coordinate (`u fc`, `fc` from `blockEntryFlat`,
which is `u`-independent) or `0` off-cone. -/
@[fun_prop]
theorem continuous_readEntry (d : Fin (N + 1) → ℕ) (S row col : ℕ) :
    Continuous (fun u : Fin (flatDim d) → ℝ ↦ readEntry d u S row col) := by
  unfold readEntry
  split
  · exact continuous_apply _
  · exact continuous_const

/-- **`canonNormalizationOf` is continuous** ⟨shared Core/CanonShear-grade fact; relocate at integration
`#73`⟩. Its four branches are `readEntry`-polynomials (the Schur cross-term, the two recoord sums, and `0`)
selected by conditions on the DECODED coordinate index — all `u`-independent — so each component is
continuous, division-free (`canonNormalizationOf` never inverts). This is the real-branch shear-continuity
atom that `continuous_foldResid` needs: `TreeEdge.hshear_analytic` covers only edges, not a path's stored
shears, and `IsRealBranch`'s value-pin carries the value only. (Continuity is the strength `continuous_foldResid`
needs; the `analyticOnNhd` upgrade — from which continuity falls out — is deferrable at relocation.) -/
theorem continuous_canonNormalizationOf (d : Fin (N + 1) → ℕ) (s : ConState N) (p : Fin (flatDim d)) :
    Continuous (canonNormalizationOf d s p) := by
  apply continuous_pi
  intro k
  unfold canonNormalizationOf
  refine continuous_if_const _ (fun _ ↦ ?_) (fun _ ↦ ?_)
  · exact (Continuous.neg (continuous_readEntry d _ _ _)).mul (continuous_readEntry d _ _ _)
  · refine continuous_if_const _ (fun _ ↦ ?_) (fun _ ↦ ?_)
    · refine continuous_finset_sum _ (fun i _ ↦ ?_)
      refine continuous_if_const _ (fun _ ↦ continuous_const) (fun _ ↦ ?_)
      exact (continuous_readEntry d _ _ _).mul (continuous_readEntry d _ _ _)
    · refine continuous_if_const _ (fun _ ↦ ?_) (fun _ ↦ ?_)
      · refine continuous_finset_sum _ (fun i _ ↦ ?_)
        refine continuous_if_const _ (fun _ ↦ continuous_const) (fun _ ↦ ?_)
        exact (continuous_readEntry d _ _ _).mul (continuous_readEntry d _ _ _)
      · exact continuous_const

/-- **`edgeShearRaw` is continuous** given a continuous displacement — `id` at merge/rollover,
`blockShear φ = id + φ` at case12/case2. -/
theorem continuous_edgeShearRaw (d : Fin (N + 1) → ℕ) (cse : StepCase)
    {φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)} (hφ : Continuous φ) :
    Continuous (edgeShearRaw d cse φ) := by
  cases cse <;> first | exact continuous_id | exact continuous_id.add hφ

/-- **Continuity of the fold residual (on a real branch).** `coreGen` (continuous) composed with the
per-edge step maps (strict-transform `blockBlowupCoordQuot` is the projection `if k = pivot then 1 else ·`,
NOT a division; the blow-up `blockBlowupMap` is continuous). The `IsRealBranch` hypothesis is REQUIRED:
`TreePath.step` carries an ARBITRARY `shearφ` with no analyticity, so `foldResid` is not continuous for an
arbitrary path — the branch value-pins each shear to `canonNormalizationOf` (`SEAT-CAPF finding: this needs
a `canonNormalizationOf`-continuity sub-lemma, not yet in the tree). Path induction descending `hbranch`. -/
theorem continuous_foldResid (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (hbranch : p.IsRealBranch (canonFlatten d)) (j : Fin (foldNR d p)) :
    Continuous (foldResid d (canonFlatten d) p j) := by
  suffices H : ∀ (q : TreePath d), q.IsRealBranch (canonFlatten d) →
      ∀ (i : Fin (foldNR d q)), Continuous (foldResid d (canonFlatten d) q i) by
    exact H p hbranch j
  intro q
  induction q with
  | root => intro _ i; exact continuous_coreGen d (canonFlatten d) i
  | step p' c pv cse ns φ ih =>
    intro hbr i
    obtain ⟨hrec, -, -, hvpin⟩ := hbr
    by_cases hnt : N ≤ ns.layer
    · have h1 : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i = fun _ ↦ (1 : ℝ) := by
        funext u
        show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i u = _
        rw [foldResid, dif_pos hnt]; rfl
      rw [h1]; exact continuous_const
    · have hNReq : foldNR d (TreePath.step p' c pv cse ns φ) = foldNR d p' := by
        show (if N ≤ ns.layer then 1 else foldNR d p') = foldNR d p'; rw [if_neg hnt]
      have hg : Continuous (foldResid d (canonFlatten d) p' (Fin.cast hNReq i)) := ih hrec _
      have hφ : Continuous φ := hvpin ▸ continuous_canonNormalizationOf d p'.conState pv
      have hshear : Continuous (edgeShearRaw d cse φ) := continuous_edgeShearRaw d cse hφ
      by_cases hδ : edgeδ d p' = true
      · have h1 : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i
            = fun u ↦ foldResid d (canonFlatten d) p' (Fin.cast hNReq i)
                (fun k ↦ blockBlowupCoordQuot pv k (edgeShearRaw d cse φ u)) := by
          funext u
          show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i u = _
          rw [foldResid, dif_neg hnt, if_pos hδ]; rfl
        rw [h1]
        exact hg.comp (continuous_pi (fun k ↦ (continuous_blockBlowupCoordQuot pv k).comp hshear))
      · have hδ0 : edgeδ d p' = false := by
          cases h : edgeδ d p' with
          | false => rfl
          | true => exact absurd h hδ
        have h1 : foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i
            = fun u ↦ foldResid d (canonFlatten d) p' (Fin.cast hNReq i)
                (stepMapRaw d cse c pv φ u) := by
          funext u
          show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i u = _
          rw [foldResid, dif_neg hnt, if_neg (by simp [hδ0])]; rfl
        rw [h1]
        exact hg.comp ((continuous_blockBlowupMap c pv).comp hshear)

/-- **(L2) The continuous support-decomposition bridge.** A continuous `F` that is
`HomogeneousDeg1On X` decomposes as `∑_{i∈X} cᵢ·uᵢ` with each `cᵢ` continuous AND ignoring `X`. Mirrors
`Case1Wire.exists_ignoresCoords_decomp` (`cᵢ u = F(Pᵢ u) − F(P₀ u)`, continuous from `hF`), with the zero
constant part forced by the homogeneity vanishing clause rather than by an input decomposition. -/
theorem continuous_decomp_of_homogeneousDeg1On {D : ℕ}
    (F : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (hF : Continuous F) (hhom : HomogeneousDeg1On F X Set.univ) :
    ∃ c : Fin D → (Fin D → ℝ) → ℝ, (∀ i, Continuous (c i)) ∧
      (∀ u, F u = ∑ i ∈ X, c i u * u i) ∧ (∀ i, IgnoresCoords (c i) X Set.univ) := by
  classical
  obtain ⟨⟨a, b, hai, hbi, hdecomp⟩, hvan⟩ := hhom
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
  -- a ≡ 0: the homogeneity vanishing clause at P₀ u (every X-coord is 0)
  have ha0 : ∀ u, a u = 0 := by
    intro u; rw [← haP0 u]
    exact hvan (P0 u) (Set.mem_univ _) (fun x hx ↦ by simp only [hP0, if_pos hx])
  refine ⟨fun i u ↦ F (Pv i u) - F (P0 u), fun i ↦ (hF.comp (hPvc i)).sub (hF.comp hP0c), ?_, ?_⟩
  · intro u
    rw [hdecomp u (Set.mem_univ _), ha0 u, zero_add]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    show b i u * u i = (F (Pv i u) - F (P0 u)) * u i
    rw [hbPv i hi u, haP0 u]; ring
  · intro i
    rw [ignoresCoords_univ_iff_agree]
    intro u v hagree
    have hPve : Pv i u = Pv i v := funext fun k ↦ by
      by_cases hk : k ∈ X
      · simp only [hPv, if_pos hk]
      · simp only [hPv, if_neg hk]; exact hagree k hk
    have hP0e : P0 u = P0 v := funext fun k ↦ by
      by_cases hk : k ∈ X
      · simp only [hP0, if_pos hk]
      · simp only [hP0, if_neg hk]; exact hagree k hk
    simp only [hPve, hP0e]

/-- **(L1) Coupling / layer separation.** Every ancestor coupling coordinate of a real branch `p` decodes
to a layer `≤ p.conState.layer` (a case2/case12 clear's below-pivot column sits at the clearing layer, and
layers are non-decreasing along the branch). At a fresh rollover child the layer strictly advances, so
`couplingClear` fixes every coordinate at layers `≥` the child layer. -/
theorem couplingCoords_decode_layer_le (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (hbranch : p.IsRealBranch (canonFlatten d))
    {y : Fin (flatDim d)} (hy : y ∈ couplingCoords d p) :
    (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤ p.conState.layer := by
  -- map: B-CAPF-couplingCoords-decode-layer-le (path induction; belowPivotCol at pivot layer, layer mono)
  sorry

/-- **The raw UNCAPPED descent** (NOT `blockCoords` — the capped raw form is FALSE on wide branches, the
cap-escape). At a fresh rollover child the raw fold residual is `Deg1SupportedSlot` over the FULL descended
layer `layerCoords d (child.layer)`. From `foldResid_layerHomogeneous'` (H, conjunct-2 directly) +
`continuous_foldResid` + the (L2) bridge (conjunct-1 over `layerCoords`). -/
theorem realBranch_appendResidDescent_fresh_layerCoords (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∀ j, Deg1SupportedSlot d (foldResid d (canonFlatten d) (p.extend ed)) j
      (layerCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  intro j
  have hguniv : foldRegion d (canonFlatten d) (p.extend ed) = Set.univ := foldRegion_eq_univ _ _
  have hnonterm : ¬ N ≤ (p.extend ed).conState.layer := by omega
  have hsl : supportLayerOf (p.extend ed).conState = (p.extend ed).conState.layer := by
    unfold supportLayerOf; rw [if_pos hfresh]
  refine ⟨?_, ?_⟩
  · -- conjunct 1: the continuous support decomposition over the FULL descended layer.
    have hH : HomogeneousDeg1On (foldResid d (canonFlatten d) (p.extend ed) j)
        (layerCoords d (p.extend ed).conState.layer) Set.univ := by
      have := foldResid_layerHomogeneous' d hpos (p.extend ed) hnonterm hbranch j
        (p.extend ed).conState.layer hsl.le (by omega)
      rwa [hguniv] at this
    obtain ⟨c, hc_cont, hc_repr, _⟩ := continuous_decomp_of_homogeneousDeg1On _ _
      (continuous_foldResid d (p.extend ed) hbranch j) hH
    exact ⟨c, fun i ↦ (hc_cont i).continuousOn, fun u _ ↦ hc_repr u⟩
  · -- conjunct 2: per-layer degree ≤ 1 from the support layer up (H's homogeneity; ∅ above N).
    intro ℓ hℓ
    by_cases hℓN : ℓ < N
    · exact (foldResid_layerHomogeneous' d hpos (p.extend ed) hnonterm hbranch j ℓ hℓ hℓN).1
    · have hemp : layerCoords d ℓ = ∅ := by
        unfold layerCoords
        rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
        intro q _
        have := q.1.1.isLt
        omega
      rw [hemp]
      exact ⟨foldResid d (canonFlatten d) (p.extend ed) j, fun _ _ ↦ 0,
        fun w _ m hm _ ↦ absurd hm (Finset.notMem_empty m),
        fun x hx ↦ absurd hx (Finset.notMem_empty x),
        fun u _ ↦ by rw [Finset.sum_empty, add_zero]⟩

/-- **The KILL — the source-cleared residual ignores the escaped out-of-cap columns** ⟨GENUINELY NEW⟩.
The escaped columns `layerCoords ∖ blockCoords` (col `≥ widthMinUpto`) are read by the raw fold ONLY through
the layer-(S)-clear recoord's column mixing, whose coefficients factor through the ancestor coupling
coordinates; `couplingClear` zeroes those, so `sourceClearedResid = foldResid ∘ couplingClear` does not read
them (the FUNCTION-level kill — the escaped coords themselves are NOT in `couplingCoords`, so this is not a
set-level containment). -/
theorem sourceClearedResid_ignoresEscaped (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d))
    (j : Fin (foldNR d (p.extend ed))) :
    IgnoresCoords (sourceClearedResid d (p.extend ed) j)
      (layerCoords d (p.extend ed).conState.layer \ blockCoords d (p.extend ed).conState.layer)
      Set.univ := by
  -- map: B-CAPF-kill-escaped ⟨GENUINELY NEW — escaped coeffs factor through ancestor couplings⟩
  sorry

/-- **Cap-frontier obligation (b), source-cleared — PRIMED TWIN.** Statement byte-identical to
`SourceClearedResid.realBranch_appendResidDescent_fresh_sourceCleared` (the controller swaps its `sorry`
for `:= realBranch_appendResidDescent_fresh_sourceCleared' …` at integration). At a fresh rollover child the
source-cleared residual is `Deg1SupportedSlot` over the running-min-capped `blockCoords`. Assembled from the
raw UNCAPPED descent ∘ `couplingClear` (via the (L1) separation, so `couplingClear` fixes the descended
layer) + the KILL (escaped columns unread), which confines the layerCoords decomposition to `blockCoords`. -/
theorem realBranch_appendResidDescent_fresh_sourceCleared' (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∀ j, Deg1SupportedSlot d (sourceClearedResid d (p.extend ed)) j
      (blockCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  -- map: B-CAPF-fresh-sourceCleared-twin (raw uncapped descent ∘ couplingClear + KILL + separation)
  sorry

end DLNFibre.DLN.Aoyagi
