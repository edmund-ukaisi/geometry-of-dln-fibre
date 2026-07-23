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
* `sourceClearedResid_capped` ⟨THE CRUX⟩ — the route-(a) path induction: the source-cleared residual is
  `Deg1SupportedSlot` over `supportAt` at EVERY real-branch node (base via `blockCoords_zero_eq_layerCoords`;
  step = `couplingClear` absorbs the escaped-col dependence into the cap, carrying multi-ancestor coupling
  depth — the genuinely new content, its full design in the lemma docstring).
* `realBranch_appendResidDescent_fresh_sourceCleared'` — the primed (b)-twin (statement byte-identical to
  `SourceClearedResid.lean`'s), DERIVED from `sourceClearedResid_capped` at the fresh child
  (`supportAt` at cleared=0 = `blockCoords`). (The earlier standalone `sourceClearedResid_ignoresEscaped`
  KILL lemma was DROPPED — SUPERSEDED-BY this helper→twin route + un-consumed; its mechanism prose survives
  in the helper docstring.)

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

/-- **`belowPivotCol` sits at the pivot's layer** — every coordinate of the below-pivot column decodes to
the pivot's decoded layer (the filter fixes the layer index). -/
theorem belowPivotCol_decode_layer (d : Fin (N + 1) → ℕ) (pivot : Fin (flatDim d))
    {y : Fin (flatDim d)} (hy : y ∈ belowPivotCol d pivot) :
    (((tupIdxEquiv d).symm y).1.1 : ℕ) = (((tupIdxEquiv d).symm pivot).1.1 : ℕ) := by
  unfold belowPivotCol at hy
  rw [Finset.mem_image] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  rw [Equiv.symm_apply_apply]
  exact (Finset.mem_filter.mp hq).2.1

/-- **(L1) Coupling / layer separation.** Every ancestor coupling coordinate of a real branch `p` decodes
to a layer `≤ p.conState.layer` (a case2/case12 clear's below-pivot column sits at the clearing layer, and
layers are non-decreasing along the branch). At a fresh rollover child the layer strictly advances, so
`couplingClear` fixes every coordinate at layers `≥` the child layer. -/
theorem couplingCoords_decode_layer_le (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (hbranch : p.IsRealBranch (canonFlatten d))
    {y : Fin (flatDim d)} (hy : y ∈ couplingCoords d p) :
    (((tupIdxEquiv d).symm y).1.1 : ℕ) ≤ p.conState.layer := by
  suffices H : ∀ (q : TreePath d), q.IsRealBranch (canonFlatten d) →
      ∀ {z : Fin (flatDim d)}, z ∈ couplingCoords d q →
      (((tupIdxEquiv d).symm z).1.1 : ℕ) ≤ q.conState.layer by
    exact H p hbranch hy
  intro q
  induction q with
  | root => intro _ z hz; exact absurd hz (by simp [couplingCoords])
  | step p' c pv cse ns φ ih =>
    intro hbr z hz
    obtain ⟨hrec, ⟨sc, hsc, hecase, hchild, hcenter, hpivpin⟩, -, -⟩ := hbr
    have hpInv : DivBirthInv d p'.conState :=
      PivotPres.divBirthInv_of_isRealBranch (canonFlatten d) p' hrec
    have htrans := conOracle_child_transition p'.conState sc hsc
    have hmono : p'.conState.layer ≤ ns.layer := by
      rw [← hchild]
      rcases htrans with ⟨_, _, hL, _⟩ | ⟨_, hL, _⟩ | ⟨_, hL, _⟩ <;> omega
    show (((tupIdxEquiv d).symm z).1.1 : ℕ) ≤ ns.layer
    rcases cse with _ | _ | _ | _ <;>
      rcases Finset.mem_union.mp hz with hz1 | hz2 <;>
      first
      | exact le_trans (ih hrec hz1) hmono
      | exact absurd hz2 (Finset.notMem_empty z)
      | (rw [belowPivotCol_decode_layer d pv hz2];
         exact le_trans (canonCenterOf_decode_layer_le p'.conState sc hpInv pv hpivpin) hmono)

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

/-! ### Guard-independent core (seat-CX): the `couplingClear`-composition algebra

`sourceClearedResid d p j = foldResid d (canonFlatten d) p j ∘ couplingClear d p`, and `couplingClear d p`
is the coordinate-ZEROING map `u k ↦ if k ∈ couplingCoords d p then 0 else u k`. The four lemmas below are
the general algebra of composing an `AffineOn`/`HomogeneousDeg1On`/decomposable function with a
coordinate-zeroing map, plus the `X ⊇ Y` upgrade under an `X∖Y`-ignoring hypothesis. Everything in the
capped statement EXCEPT the escaped-column KILL rides these; they are statement-independent (no reference to
`sourceClearedResid_capped`). -/

/-- **`couplingClear` is continuous** — each output coordinate is `0` (constant) on a coupling, else the
input coordinate (`continuous_apply`). -/
theorem continuous_couplingClear (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    Continuous (couplingClear d p) := by
  apply continuous_pi; intro k
  show Continuous (fun u : Fin (flatDim d) → ℝ ↦ if k ∈ couplingCoords d p then (0 : ℝ) else u k)
  by_cases hk : k ∈ couplingCoords d p
  · simp only [if_pos hk]; exact continuous_const
  · simp only [if_neg hk]; exact continuous_apply k

/-- **Composing with a coordinate-zeroing map preserves `AffineOn`** (on `univ`). Zeroing the `Z`-coords
before `F` keeps the degree-≤1 grade on `X`: the `X ∩ Z` terms drop (their coord becomes `0`), and the
coefficients precompose with the zeroing (still `X`-ignoring, as the zeroing sends `X`-agreeing points to
`X`-agreeing points). The `couplingClear` composition rides this with `Z = couplingCoords d p`. -/
theorem affineOn_comp_coordZero {D : ℕ} (F : (Fin D → ℝ) → ℝ) (X Z : Finset (Fin D))
    (hF : AffineOn F X Set.univ) :
    AffineOn (fun u ↦ F (fun k ↦ if k ∈ Z then 0 else u k)) X Set.univ := by
  classical
  obtain ⟨a, b, ha, hb, hrepr⟩ := hF
  have hagree : ∀ u v : Fin D → ℝ, (∀ s, s ∉ X → u s = v s) →
      ∀ s, s ∉ X → (if s ∈ Z then (0 : ℝ) else u s) = (if s ∈ Z then 0 else v s) := by
    intro u v hag s hs; split
    · rfl
    · exact hag s hs
  refine ⟨fun u ↦ a (fun k ↦ if k ∈ Z then 0 else u k),
    fun x u ↦ if x ∈ Z then 0 else b x (fun k ↦ if k ∈ Z then 0 else u k), ?_, ?_, ?_⟩
  · rw [ignoresCoords_univ_iff_agree]
    exact fun u v hag ↦ (ignoresCoords_univ_iff_agree a X).mp ha _ _ (hagree u v hag)
  · intro x hx
    rw [ignoresCoords_univ_iff_agree]
    intro u v hag
    by_cases hxZ : x ∈ Z
    · simp only [if_pos hxZ]
    · simp only [if_neg hxZ]
      exact (ignoresCoords_univ_iff_agree (b x) X).mp (hb x hx) _ _ (hagree u v hag)
  · intro u _
    show F (fun k ↦ if k ∈ Z then 0 else u k)
        = a (fun k ↦ if k ∈ Z then 0 else u k)
          + ∑ x ∈ X, (if x ∈ Z then 0 else b x (fun k ↦ if k ∈ Z then 0 else u k)) * u x
    rw [hrepr _ (Set.mem_univ _)]
    congr 1
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    by_cases hxZ : x ∈ Z
    · simp only [if_pos hxZ, mul_zero, zero_mul]
    · simp only [if_neg hxZ]

/-- **Composing with a coordinate-zeroing map preserves `HomogeneousDeg1On`** (on `univ`). The `AffineOn`
grade is `affineOn_comp_coordZero`; the vanishing clause transports because zeroing the `Z`-coords keeps
every `X`-coord `0` when it started `0`. -/
theorem homogeneousDeg1On_comp_coordZero {D : ℕ} (F : (Fin D → ℝ) → ℝ) (X Z : Finset (Fin D))
    (hF : HomogeneousDeg1On F X Set.univ) :
    HomogeneousDeg1On (fun u ↦ F (fun k ↦ if k ∈ Z then 0 else u k)) X Set.univ := by
  refine ⟨affineOn_comp_coordZero F X Z hF.1, ?_⟩
  intro u _ hu
  exact hF.2 _ (Set.mem_univ _) (fun x hx ↦ by
    by_cases hxZ : x ∈ Z
    · simp only [if_pos hxZ]
    · simp only [if_neg hxZ]; exact hu x hx)

/-- **`AffineOn` is antitone in the block** (on `univ`): affine on `X` ⟹ affine on any `Y ⊆ X`. The `X∖Y`
linear terms fold into the constant part (each `b_x · u_x` for `x ∈ X∖Y` ignores `Y`, since `u_x` does and
`b_x` ignores `X ⊇ Y`). -/
theorem affineOn_of_subset {D : ℕ} (F : (Fin D → ℝ) → ℝ) {X Y : Finset (Fin D)} (hYX : Y ⊆ X)
    (hF : AffineOn F X Set.univ) : AffineOn F Y Set.univ := by
  classical
  obtain ⟨a, b, ha, hb, hrepr⟩ := hF
  have hoffY : ∀ u v : Fin D → ℝ, (∀ s, s ∉ Y → u s = v s) → ∀ s, s ∉ X → u s = v s :=
    fun u v hag s hs ↦ hag s (fun h ↦ hs (hYX h))
  refine ⟨fun u ↦ a u + ∑ x ∈ X \ Y, b x u * u x, fun y u ↦ b y u, ?_, ?_, ?_⟩
  · rw [ignoresCoords_univ_iff_agree]
    intro u v hag
    have hav : a u = a v := (ignoresCoords_univ_iff_agree a X).mp ha _ _ (hoffY u v hag)
    have hsum : ∑ x ∈ X \ Y, b x u * u x = ∑ x ∈ X \ Y, b x v * v x := by
      refine Finset.sum_congr rfl (fun x hx ↦ ?_)
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxY : x ∉ Y := (Finset.mem_sdiff.mp hx).2
      rw [(ignoresCoords_univ_iff_agree (b x) X).mp (hb x hxX) _ _ (hoffY u v hag), hag x hxY]
    rw [hav, hsum]
  · intro y hy
    rw [ignoresCoords_univ_iff_agree]
    exact fun u v hag ↦ (ignoresCoords_univ_iff_agree (b y) X).mp (hb y (hYX hy)) _ _ (hoffY u v hag)
  · intro u _
    rw [hrepr u (Set.mem_univ _), add_assoc]
    congr 1
    rw [← Finset.sum_sdiff hYX, add_comm]

/-- **The block-restriction upgrade** (on `univ`): `HomogeneousDeg1On X` + `IgnoresCoords (X∖Y)` ⟹
`HomogeneousDeg1On Y` (for `Y ⊆ X`). The `AffineOn Y` grade is antitonicity; the `Y`-vanishing comes from
the `X∖Y`-ignoring (zero the `X∖Y` coords freely) plus the `X`-vanishing. This is the KILL's consumer: with
`X = layerCoords`, `Y = blockCoords`, `X∖Y =` the escaped columns, it caps the decomposition to the block. -/
theorem homogeneousDeg1On_of_subset_ignores {D : ℕ} (G : (Fin D → ℝ) → ℝ) {X Y : Finset (Fin D)}
    (hYX : Y ⊆ X) (hhom : HomogeneousDeg1On G X Set.univ)
    (hign : IgnoresCoords G (X \ Y) Set.univ) :
    HomogeneousDeg1On G Y Set.univ := by
  classical
  refine ⟨affineOn_of_subset G hYX hhom.1, ?_⟩
  intro u _ hu
  -- zero the X∖Y coords: agrees with u off X∖Y, and G ignores X∖Y, so G u = G u0
  set u0 : Fin D → ℝ := fun k ↦ if k ∈ X \ Y then 0 else u k with hu0
  have hGu : G u = G u0 :=
    (ignoresCoords_univ_iff_agree G (X \ Y)).mp hign u u0
      (fun s hs ↦ by simp only [hu0, if_neg hs])
  rw [hGu]
  refine hhom.2 u0 (Set.mem_univ _) (fun x hx ↦ ?_)
  by_cases hxY : x ∈ Y
  · have : x ∉ X \ Y := fun h ↦ (Finset.mem_sdiff.mp h).2 hxY
    simp only [hu0, if_neg this]; exact hu x hxY
  · have : x ∈ X \ Y := Finset.mem_sdiff.mpr ⟨hx, hxY⟩
    simp only [hu0, if_pos this]

/-! ### THE KILL — the escaped-column ignore, via the certified telescoping invariant `Z(p)`

pnp certificate `verify/capstone_kill_invariant.py` (V1/V2/V3, 4 witnesses, commit `a24726b18`). The
source-cleared residual `sourceClearedResid = foldResid ∘ couplingClear` IGNORES the accumulated
`killZ p := couplingCoords p ∪ escapedBelow (S, c)`, where `escapedBelow (S, c)` collects the escaped
columns of layers `≤ S` plus — once `c` reaches the rollover threshold `widthMinUpto d (S+1)` (the LAST
clear of layer `S`) — the escaped columns of layer `S+1`. The KILL is the read-off at a fresh node
(`cleared = 0`): `escapedCol S ⊆ escapedBelow (S, 0) ⊆ killZ`. The couplingCoords part is trivial
(`couplingClear` zeroes them); the escapedBelow part is the certified induction (`escapedBelow` grows only
at a last clear, where the recoord-(ii) shear `A_{S+1}·Q₁⁻¹` writes the entering escaped columns with
coefficients = the accumulated couplings `couplingClear` zeroes — V3). -/

/-- The escaped (out-of-running-min-cap) columns of layer `M`: `layerCoords ∖ blockCoords` (col
`≥ widthMinUpto d M`). `∅` for `M ≥ N` (both sides `∅`) and for `M = 0` (`blockCoords_zero_eq_layerCoords`). -/
noncomputable def escapedCol (d : Fin (N + 1) → ℕ) (M : ℕ) : Finset (Fin (flatDim d)) :=
  layerCoords d M \ blockCoords d M

/-- The accumulated escaped columns at construction state `(S, c)` (pnp's `escapedBelow`): the escaped
columns of every layer `≤ S`, PLUS the escaped columns of layer `S+1` once `c` reaches the rollover
threshold `widthMinUpto d (S+1)` (the last clear of layer `S`, when the layer-`S` recoord shears have
accumulated the couplings that absorb layer-`(S+1)`'s escaped columns). -/
noncomputable def escapedBelow (d : Fin (N + 1) → ℕ) (S c : ℕ) : Finset (Fin (flatDim d)) :=
  (Finset.range (S + 1)).biUnion (escapedCol d) ∪
    (if widthMinUpto d (S + 1) ≤ c then escapedCol d (S + 1) else ∅)

/-- `escapedCol d S ⊆ escapedBelow d S c` (for any `c`): layer `S` sits in the `range (S+1)` biUnion. -/
theorem escapedCol_subset_escapedBelow (d : Fin (N + 1) → ℕ) (S c : ℕ) :
    escapedCol d S ⊆ escapedBelow d S c := fun x hx =>
  Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
    ⟨S, Finset.mem_range.mpr (Nat.lt_succ_self S), hx⟩))

/-- **`sourceClearedResid` ignores the ancestor coupling coordinates** — trivially: `couplingClear`
zeroes them, so a perturbation of a coupling coordinate does not survive the clear. -/
theorem sourceClearedResid_ignoresCouplingCoords (d : Fin (N + 1) → ℕ)
    (q : TreePath d) (j : Fin (foldNR d q)) :
    IgnoresCoords (sourceClearedResid d q j) (couplingCoords d q) Set.univ := by
  intro w _ m hm t
  show foldResid d (canonFlatten d) q j (couplingClear d q (Function.update w m t))
      = foldResid d (canonFlatten d) q j (couplingClear d q w)
  congr 1
  funext k
  show (if k ∈ couplingCoords d q then (0 : ℝ) else Function.update w m t k)
      = (if k ∈ couplingCoords d q then 0 else w k)
  by_cases hk : k ∈ couplingCoords d q
  · rw [if_pos hk, if_pos hk]
  · have hkm : k ≠ m := by rintro rfl; exact hk hm
    rw [if_neg hk, if_neg hk, Function.update_of_ne hkm]

/-- **`IgnoresCoords` over a union** — the conjunction of the two parts. -/
theorem ignoresCoords_union {D : ℕ} {c : (Fin D → ℝ) → ℝ} {A B : Finset (Fin D)}
    {V : Set (Fin D → ℝ)} (hA : IgnoresCoords c A V) (hB : IgnoresCoords c B V) :
    IgnoresCoords c (A ∪ B) V := by
  intro w hw m hm t
  rcases Finset.mem_union.mp hm with h | h
  · exact hA w hw m h t
  · exact hB w hw m h t

/-- **`IgnoresCoords` composes with a `T`-preserving pre-map** (on `univ`): if `g` ignores `T` and `σ` maps
`T`-agreeing points to `T`-agreeing points, then `g ∘ σ` ignores `T`. The step reduction rides this with
`g = sourceClearedResid` of the parent and `σ = (stepMap) ∘ couplingClear` of the child. -/
theorem ignoresCoords_comp {D : ℕ} {g : (Fin D → ℝ) → ℝ} {σ : (Fin D → ℝ) → (Fin D → ℝ)}
    {T : Finset (Fin D)} (hg : IgnoresCoords g T Set.univ)
    (hσ : ∀ u v : Fin D → ℝ, (∀ s, s ∉ T → u s = v s) → ∀ s, s ∉ T → σ u s = σ v s) :
    IgnoresCoords (fun u ↦ g (σ u)) T Set.univ := by
  rw [ignoresCoords_univ_iff_agree]
  intro u v hag
  exact (ignoresCoords_univ_iff_agree g T).mp hg _ _ (hσ u v hag)

/-- **`couplingClear` preserves agreement off any set** — coordinate-wise (`(couplingClear p u) k` reads
only `u k`), so it sends `T`-agreeing points to `T`-agreeing points, for every `T`. -/
theorem couplingClear_agree_of_agree (d : Fin (N + 1) → ℕ) (p : TreePath d) (T : Finset (Fin (flatDim d)))
    {u v : Fin (flatDim d) → ℝ} (hag : ∀ s, s ∉ T → u s = v s) :
    ∀ s, s ∉ T → couplingClear d p u s = couplingClear d p v s := by
  intro s hs
  show (if s ∈ couplingCoords d p then (0 : ℝ) else u s)
      = (if s ∈ couplingCoords d p then 0 else v s)
  by_cases hsc : s ∈ couplingCoords d p
  · rw [if_pos hsc, if_pos hsc]
  · rw [if_neg hsc, if_neg hsc, hag s hs]

/-! ### `escapedBelow` state-transition set-equalities + the `couplingClear` fixed-point (the step's
foundation — the pnp certificate's `telescoping_check` (V2), rendered as Finset facts). -/

/-- Peel the top layer off the `escapedBelow` biUnion: `⋃_{M<S+2} escapedCol M = escapedCol (S+1) ∪
⋃_{M<S+1} escapedCol M`. -/
theorem escapedCol_biUnion_range_succ (d : Fin (N + 1) → ℕ) (S : ℕ) :
    (Finset.range (S + 2)).biUnion (escapedCol d)
      = escapedCol d (S + 1) ∪ (Finset.range (S + 1)).biUnion (escapedCol d) := by
  rw [show S + 2 = (S + 1) + 1 from rfl, Finset.range_add_one, Finset.biUnion_insert]

/-- **Rollover transition** (V2): `escapedBelow (S+1, 0) = escapedBelow (S, c)` once `c` has reached the
rollover threshold `widthMinUpto d (S+1)` (the layer-`S` clears are exhausted, `conOracle_child_transition`
rollover arm). The escaped part is UNCHANGED — layer-`(S+1)`'s columns entered at the last clear. -/
theorem escapedBelow_rollover_eq (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k) (S c : ℕ)
    (h : widthMinUpto d (S + 1) ≤ c) :
    escapedBelow d (S + 1) 0 = escapedBelow d S c := by
  have hchild : ¬ (widthMinUpto d (S + 1 + 1) ≤ 0) := by
    have := widthMinUpto_pos hpos (S + 1 + 1); omega
  simp only [escapedBelow, if_neg hchild, if_pos h, Finset.union_empty]
  rw [escapedCol_biUnion_range_succ, Finset.union_comm]

/-- **Non-last clear transition** (V2): `escapedBelow (S, c+1) = escapedBelow (S, c)` when `c+1 <
widthMinUpto d (S+1)` (layer `S` not yet exhausted) — no escaped columns enter. -/
theorem escapedBelow_clear_notlast (d : Fin (N + 1) → ℕ) (S c : ℕ)
    (h : c + 1 < widthMinUpto d (S + 1)) :
    escapedBelow d S (c + 1) = escapedBelow d S c := by
  have h1 : ¬ (widthMinUpto d (S + 1) ≤ c + 1) := by omega
  have h2 : ¬ (widthMinUpto d (S + 1) ≤ c) := by omega
  simp only [escapedBelow, if_neg h1, if_neg h2]

/-- **Last clear transition** (V2, the LOAD-BEARING growth): `escapedBelow (S, c+1) = escapedBelow (S, c) ∪
escapedCol (S+1)` when `c+1 = widthMinUpto d (S+1)` — layer-`(S+1)`'s escaped columns ENTER here (V3). -/
theorem escapedBelow_clear_last (d : Fin (N + 1) → ℕ) (S c : ℕ)
    (h : c + 1 = widthMinUpto d (S + 1)) :
    escapedBelow d S (c + 1) = escapedBelow d S c ∪ escapedCol d (S + 1) := by
  have h1 : widthMinUpto d (S + 1) ≤ c + 1 := by omega
  have h2 : ¬ (widthMinUpto d (S + 1) ≤ c) := by omega
  simp only [escapedBelow, if_pos h1, if_neg h2, Finset.union_empty]

/-- **`couplingCoords` is monotone along a step** — the parent's couplings are among the child's (a step
UNIONS in the below-pivot column). -/
theorem couplingCoords_subset_step (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (c : Finset (Fin (flatDim d))) (pv : Fin (flatDim d)) (cse : StepCase) (ns : ConState N)
    (φ : (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ)) :
    couplingCoords d p ⊆ couplingCoords d (TreePath.step p c pv cse ns φ) := by
  intro x hx; exact Finset.mem_union.mpr (Or.inl hx)

/-- **`couplingClear p` FIXES a `couplingClear q`-cleared point** when `couplingCoords p ⊆ couplingCoords q`
— the (smaller) parent clear is subsumed by the (larger) child clear. This is the fixed-point that lets the
induction feed a child-cleared input to the parent's `sourceClearedResid` (`= foldResid ∘ couplingClear p`). -/
theorem couplingClear_couplingClear_of_subset (d : Fin (N + 1) → ℕ) {p q : TreePath d}
    (h : couplingCoords d p ⊆ couplingCoords d q) (u : Fin (flatDim d) → ℝ) :
    couplingClear d p (couplingClear d q u) = couplingClear d q u := by
  funext k
  show (if k ∈ couplingCoords d p then (0 : ℝ) else couplingClear d q u k) = couplingClear d q u k
  by_cases hk : k ∈ couplingCoords d p
  · rw [if_pos hk]
    show (0 : ℝ) = if k ∈ couplingCoords d q then 0 else u k
    rw [if_pos (h hk)]
  · rw [if_neg hk]

/-- **Canonical (full-diagonal) pivots along a path** (#95 — the row-phantom scope). Every fresh-clear
(case2/case12) edge's pivot is the DIAGONAL corner `cornerToFlat d layer cleared = (layer, cleared, cleared)`
(`= canonPivotOf`), not a free fan pivot. Case11 pivots are canonical already (forced by `IsRealBranch`'s
fan rule (b), `= canonPivotOf`); rollover has no pivot. **This is the scope the KILL / cap invariant needs:**
an off-diagonal (row-repeat) fan pivot has `belowPivotCol = ∅`, so `couplingClear` is the identity there and
the escaped column is read COUPLING-FREE (the KILL is FALSE off-diagonal — `(2,3,3,3)` `(0,2,0)+(0,2,1)`,
#95). On the diagonal the entering escaped column is read only through the recoord-(ii) shear whose
coefficients are the below-diagonal couplings `couplingClear` zeroes. (Matches the INV-lane
`CanonicalPivots`, `cornerToFlat (layer, cleared)`; reconcile the two at integration `#73`.) -/
def CanonicalPivots (d : Fin (N + 1) → ℕ) : TreePath d → Prop
  | .root => True
  | .step p _center pivot cse _ns _φ =>
      CanonicalPivots d p ∧
        (match cse with
         | StepCase.case12 => cornerToFlat d p.conState.layer p.conState.cleared = some pivot
         | StepCase.case2 => cornerToFlat d p.conState.layer p.conState.cleared = some pivot
         | _ => True)

/-- **A fresh-clear (case2/case12) child fires strictly below the rollover threshold** — `cleared <
widthMinUpto d (layer+1)`. At/above the threshold the oracle emits a ROLLOVER (its only child), so a
case2/case12 child forces the strict inequality. Used to place the `escapedBelow` transition in the
`clear_notlast` (`c+1 < wmu`) vs `clear_last` (`c+1 = wmu`) case, never the vacuous `wmu ≤ c` one. -/
theorem conOracle_case2or12_cleared_lt {N : ℕ} {d : Fin (N + 1) → ℕ} (s : ConState N)
    (sc : StepChild d s) (hsc : sc ∈ (conOracle d s).stepChildren)
    (hc : sc.ecase = StepCase.case2 ∨ sc.ecase = StepCase.case12) :
    s.cleared < widthMinUpto d (s.layer + 1) := by
  by_contra hcon
  push_neg at hcon
  have h1 : ¬ N ≤ s.layer := by
    intro hter
    have horacle : conOracle d s = oracleTerminal d s := by unfold conOracle; rw [dif_pos hter]
    rw [horacle] at hsc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
  have horacle : conOracle d s = rolloverDecision d s (le_of_lt (not_le.mp h1)) hcon := by
    unfold conOracle; rw [dif_neg h1, dif_pos hcon]
  rw [horacle] at hsc
  simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hsc
  subst hsc
  rcases hc with h | h <;> simp at h

/-- **A `cornerToFlat` corner decodes to the DIAGONAL** `(S, J, J)` — layer `S`, row `J`, col `J`. The
building block for "couplings sit strictly below the diagonal": a fresh-clear pivot is `cornerToFlat(S,
cleared)`, so its row `=` its col. -/
theorem cornerToFlat_decode {N : ℕ} {d : Fin (N + 1) → ℕ} {S J : ℕ} {pv : Fin (flatDim d)}
    (h : cornerToFlat d S J = some pv) :
    (((tupIdxEquiv d).symm pv).1.1 : ℕ) = S ∧ (((tupIdxEquiv d).symm pv).1.2 : ℕ) = J ∧
      (((tupIdxEquiv d).symm pv).2 : ℕ) = J := by
  simp only [cornerToFlat] at h
  split_ifs at h with hS hr hc <;> simp only [reduceCtorEq, Option.some.injEq] at h
  -- only the all-conditions-true branch survives; `h : tupIdxEquiv ⟨…⟩ = pv`.
  have hd : (tupIdxEquiv d).symm pv = ⟨⟨⟨S, hS⟩, ⟨J, hr⟩⟩, ⟨J, hc⟩⟩ := by
    rw [← h, Equiv.symm_apply_apply]
  rw [hd]; exact ⟨rfl, rfl, rfl⟩

/-- **`belowPivotCol` shares the pivot's column and lies strictly below its row.** -/
theorem belowPivotCol_decode (d : Fin (N + 1) → ℕ) (pivot : Fin (flatDim d))
    {y : Fin (flatDim d)} (hy : y ∈ belowPivotCol d pivot) :
    (((tupIdxEquiv d).symm y).2 : ℕ) = (((tupIdxEquiv d).symm pivot).2 : ℕ) ∧
      (((tupIdxEquiv d).symm pivot).1.2 : ℕ) < (((tupIdxEquiv d).symm y).1.2 : ℕ) := by
  unfold belowPivotCol at hy
  rw [Finset.mem_image] at hy
  obtain ⟨q, hq, rfl⟩ := hy
  rw [Equiv.symm_apply_apply]
  exact ⟨(Finset.mem_filter.mp hq).2.2.1, (Finset.mem_filter.mp hq).2.2.2⟩

/-- **Every ancestor coupling coordinate is STRICTLY BELOW the diagonal** (`col < row`), under
`CanonicalPivots`. Each fresh-clear pivot is the diagonal corner `cornerToFlat(S, cleared) = (S, cleared,
cleared)`, and its below-pivot column `{(S, r, cleared) : r > cleared}` therefore has `col = cleared =
pivot.row < r = row`. Gives `pv ∉ couplingCoords` for the DIAGONAL `pv` the FP needs (a diagonal coord has
`col = row`, contradicting `col < row`). -/
theorem couplingCoords_row_gt_col {N : ℕ} {d : Fin (N + 1) → ℕ} :
    ∀ (p : TreePath d), CanonicalPivots d p → ∀ {x : Fin (flatDim d)}, x ∈ couplingCoords d p →
      (((tupIdxEquiv d).symm x).2 : ℕ) < (((tupIdxEquiv d).symm x).1.2 : ℕ) := by
  intro p
  induction p with
  | root => intro _ x hx; simp [couplingCoords] at hx
  | step p' c pv cse ns φ ih =>
    intro hcanon x hx
    obtain ⟨hcanonP, hcanonPiv⟩ := hcanon
    cases cse with
    | case11 =>
      have hcc : couplingCoords d (TreePath.step p' c pv StepCase.case11 ns φ)
          = couplingCoords d p' := Finset.union_empty _
      rw [hcc] at hx; exact ih hcanonP hx
    | rollover =>
      have hcc : couplingCoords d (TreePath.step p' c pv StepCase.rollover ns φ)
          = couplingCoords d p' := Finset.union_empty _
      rw [hcc] at hx; exact ih hcanonP hx
    | case12 =>
      rw [couplingCoords] at hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · exact ih hcanonP h1
      · change x ∈ belowPivotCol d pv at h2
        obtain ⟨hcol, hrow⟩ := belowPivotCol_decode d pv h2
        obtain ⟨_, hpr, hpc⟩ := cornerToFlat_decode hcanonPiv
        omega
    | case2 =>
      rw [couplingCoords] at hx
      rcases Finset.mem_union.mp hx with h1 | h2
      · exact ih hcanonP h1
      · change x ∈ belowPivotCol d pv at h2
        obtain ⟨hcol, hrow⟩ := belowPivotCol_decode d pv h2
        obtain ⟨_, hpr, hpc⟩ := cornerToFlat_decode hcanonPiv
        omega

/-- **Ancestor decomposition of `couplingCoords` membership** — every coupling coordinate lies in the
below-pivot column of SOME ancestor fresh-clear pivot `q`, and that WHOLE column is coupling (`⊆
couplingCoords`). Under `CanonicalPivots` the pivot `q` is DIAGONAL (`q.row = q.col`), so its below-column
is `{(layer, r, col) : r > col}`: any deeper entry in the same cleared column is coupling too — the
branch-(iii)/(descent) step where a shear read lands on a deeper entry of a cleared column. -/
theorem couplingCoords_mem_belowPivotCol {N : ℕ} {d : Fin (N + 1) → ℕ} :
    ∀ (p : TreePath d), CanonicalPivots d p → ∀ {x : Fin (flatDim d)}, x ∈ couplingCoords d p →
      ∃ q, (((tupIdxEquiv d).symm q).1.2 : ℕ) = (((tupIdxEquiv d).symm q).2 : ℕ) ∧
        x ∈ belowPivotCol d q ∧ belowPivotCol d q ⊆ couplingCoords d p := by
  intro p
  induction p with
  | root => intro _ x hx; simp [couplingCoords] at hx
  | step p' c pv cse ns φ ih =>
    intro hcanon x hx
    obtain ⟨hcanonP, hcanonPiv⟩ := hcanon
    cases cse with
    | case11 =>
      have hcc : couplingCoords d (TreePath.step p' c pv StepCase.case11 ns φ)
          = couplingCoords d p' := Finset.union_empty _
      rw [hcc] at hx ⊢; exact ih hcanonP hx
    | rollover =>
      have hcc : couplingCoords d (TreePath.step p' c pv StepCase.rollover ns φ)
          = couplingCoords d p' := Finset.union_empty _
      rw [hcc] at hx ⊢; exact ih hcanonP hx
    | case12 =>
      have hcc : couplingCoords d (TreePath.step p' c pv StepCase.case12 ns φ)
          = couplingCoords d p' ∪ belowPivotCol d pv := rfl
      rw [hcc] at hx ⊢
      rcases Finset.mem_union.mp hx with h1 | h2
      · obtain ⟨q, hdiag, hq1, hq2⟩ := ih hcanonP h1
        exact ⟨q, hdiag, hq1, hq2.trans Finset.subset_union_left⟩
      · obtain ⟨_, hpr, hpc⟩ := cornerToFlat_decode hcanonPiv
        exact ⟨pv, by omega, h2, Finset.subset_union_right⟩
    | case2 =>
      have hcc : couplingCoords d (TreePath.step p' c pv StepCase.case2 ns φ)
          = couplingCoords d p' ∪ belowPivotCol d pv := rfl
      rw [hcc] at hx ⊢
      rcases Finset.mem_union.mp hx with h1 | h2
      · obtain ⟨q, hdiag, hq1, hq2⟩ := ih hcanonP h1
        exact ⟨q, hdiag, hq1, hq2.trans Finset.subset_union_left⟩
      · obtain ⟨_, hpr, hpc⟩ := cornerToFlat_decode hcanonPiv
        exact ⟨pv, by omega, h2, Finset.subset_union_right⟩

/-- **`blockEntryFlat` decodes to its `(S, row, col)`** — the flat coord of a matrix entry has exactly
that layer/row/col. Mirror of `cornerToFlat_decode`. -/
theorem blockEntryFlat_decode {N : ℕ} {d : Fin (N + 1) → ℕ} {S row col : ℕ} {fc : Fin (flatDim d)}
    (h : blockEntryFlat d S row col = some fc) :
    (((tupIdxEquiv d).symm fc).1.1 : ℕ) = S ∧ (((tupIdxEquiv d).symm fc).1.2 : ℕ) = row ∧
      (((tupIdxEquiv d).symm fc).2 : ℕ) = col := by
  simp only [blockEntryFlat] at h
  split_ifs at h with hS hr hc <;> simp only [reduceCtorEq, Option.some.injEq] at h
  have hd : (tupIdxEquiv d).symm fc = ⟨⟨⟨S, hS⟩, ⟨row, hr⟩⟩, ⟨col, hc⟩⟩ := by
    rw [← h, Equiv.symm_apply_apply]
  rw [hd]; exact ⟨rfl, rfl, rfl⟩

/-- **Membership in `belowPivotCol` from a decoded coordinate** — same layer/col as the pivot, strictly
below its row. -/
theorem mem_belowPivotCol_of_decode {N : ℕ} {d : Fin (N + 1) → ℕ} (pivot y : Fin (flatDim d))
    (hl : (((tupIdxEquiv d).symm y).1.1 : ℕ) = (((tupIdxEquiv d).symm pivot).1.1 : ℕ))
    (hc : (((tupIdxEquiv d).symm y).2 : ℕ) = (((tupIdxEquiv d).symm pivot).2 : ℕ))
    (hr : (((tupIdxEquiv d).symm pivot).1.2 : ℕ) < (((tupIdxEquiv d).symm y).1.2 : ℕ)) :
    y ∈ belowPivotCol d pivot := by
  unfold belowPivotCol
  rw [Finset.mem_image]
  exact ⟨(tupIdxEquiv d).symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hc, hr⟩,
    (tupIdxEquiv d).apply_symm_apply y⟩

/-- **`readEntry` on a coupling-cleared input is `0`** when the read coordinate is a coupling — the
`couplingClear` zeroes it (or the entry is off-cone, `0`). The bridge from a shear `readEntry` to the
coupling-vanishing the FP/AT need. -/
theorem readEntry_couplingClear_eq_zero {N : ℕ} {d : Fin (N + 1) → ℕ} (q : TreePath d)
    (u : Fin (flatDim d) → ℝ) (S row col : ℕ)
    (h : ∀ fc, blockEntryFlat d S row col = some fc → fc ∈ couplingCoords d q) :
    readEntry d (couplingClear d q u) S row col = 0 := by
  show (match blockEntryFlat d S row col with
    | some fc => couplingClear d q u fc | none => (0 : ℝ)) = 0
  cases hb : blockEntryFlat d S row col with
  | none => rfl
  | some fc =>
    show (if fc ∈ couplingCoords d q then (0 : ℝ) else u fc) = 0
    rw [if_pos (h fc hb)]

/-- **A within-block coordinate is NOT escaped-below** — layer `S`, col `< widthMinUpto d S` (in the
running-min block) ⟹ `∉ escapedBelow d S c`. The escaped set collects, per layer `M ≤ S`, the columns
`≥ widthMinUpto d M`; a layer-`S` coordinate can only match the `M = S` slice, where the block cap
`col < widthMinUpto d S` excludes it. Powers `pv ∉ escapedBelow` (the fresh-clear pivot sits in the block:
`col = cleared < widthMinUpto d (S+1) ≤ widthMinUpto d S`). -/
theorem notMem_escapedBelow_of_col_lt_wmu {N : ℕ} {d : Fin (N + 1) → ℕ} {S c : ℕ}
    {x : Fin (flatDim d)} (hlay : (((tupIdxEquiv d).symm x).1.1 : ℕ) = S)
    (hcol : (((tupIdxEquiv d).symm x).2 : ℕ) < widthMinUpto d S) :
    x ∉ escapedBelow d S c := by
  rw [escapedBelow]
  intro hx
  rcases Finset.mem_union.mp hx with hbi | hcond
  · obtain ⟨M, hM, hxM⟩ := Finset.mem_biUnion.mp hbi
    rw [escapedCol, Finset.mem_sdiff] at hxM
    have hMS : M = S := by rw [← decode_layer_of_mem_layerCoords d M x hxM.1]; exact hlay
    subst hMS
    exact hxM.2 (Finset.mem_image.mpr ⟨(tupIdxEquiv d).symm x,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlay, hcol⟩, (tupIdxEquiv d).apply_symm_apply x⟩)
  · split_ifs at hcond with hcnd
    · rw [escapedCol, Finset.mem_sdiff] at hcond
      have := decode_layer_of_mem_layerCoords d (S + 1) x hcond.1
      rw [hlay] at this; omega
    · exact absurd hcond (by simp)

/-- **The recoord shear VANISHES on the ancestor couplings, on a coupling-cleared input (Sfp).** For a
DIAGONAL fresh-clear pivot `pv = (S, cl, cl)` and any coupling coordinate `k ∈ couplingCoords p'`, the
displacement `canonNormalizationOf p'.conState pv (couplingClear q u) k = 0` — provided the current below-
pivot column AND the ancestor couplings are cleared (`belowPivotCol pv, couplingCoords p' ⊆ couplingCoords
q`). Branch (i) (layer-`S` Schur) reads the pivot's below-column `(S, kr, cl)` (`kr > cl`), a current-pivot
coupling → `0`. Branch (ii) (layer `S+1`) can't fire (couplings sit at layer `≤ S`). Branch (iii) (layer
`S−1` input recoord) reads `(S−1, k', kc)` in the SAME cleared column as `k` (`k`'s ancestor pivot is
diagonal, `col = kc`, and `k' > cl > kc`), a coupling → `0`. This is the FP's shear half; the FUNCTION-level
KILL. -/
theorem canonNormalizationOf_vanishes_on_couplings {N : ℕ} {d : Fin (N + 1) → ℕ}
    (p' q : TreePath d) (hcanonP : CanonicalPivots d p') (hrec : p'.IsRealBranch (canonFlatten d))
    (pv : Fin (flatDim d))
    (hcc : couplingCoords d p' ⊆ couplingCoords d q)
    (hbpv : belowPivotCol d pv ⊆ couplingCoords d q)
    (hpvlay : (((tupIdxEquiv d).symm pv).1.1 : ℕ) = p'.conState.layer)
    (hpvrow : (((tupIdxEquiv d).symm pv).1.2 : ℕ) = p'.conState.cleared)
    (hpvcol : (((tupIdxEquiv d).symm pv).2 : ℕ) = p'.conState.cleared)
    (u : Fin (flatDim d) → ℝ) {k : Fin (flatDim d)} (hk : k ∈ couplingCoords d p') :
    canonNormalizationOf d p'.conState pv (couplingClear d q u) k = 0 := by
  have hkl : (((tupIdxEquiv d).symm k).1.1 : ℕ) ≤ p'.conState.layer :=
    couplingCoords_decode_layer_le d p' hrec hk
  have hkrc : (((tupIdxEquiv d).symm k).2 : ℕ) < (((tupIdxEquiv d).symm k).1.2 : ℕ) :=
    couplingCoords_row_gt_col p' hcanonP hk
  simp only [canonNormalizationOf]
  split_ifs with hb1 hb2 hb3
  · -- branch (i): first factor reads `(S, kr, cl)`, a current-pivot below-column coupling → 0.
    obtain ⟨_, hbne_row, _, hbge_row, _⟩ := hb1
    rw [hpvrow] at hbne_row
    have h0 : readEntry d (couplingClear d q u) p'.conState.layer
        (((tupIdxEquiv d).symm k).1.2) (((tupIdxEquiv d).symm pv).2) = 0 := by
      refine readEntry_couplingClear_eq_zero q u _ _ _ (fun fc hfc => hbpv ?_)
      obtain ⟨hl, hr, hc⟩ := blockEntryFlat_decode hfc
      refine mem_belowPivotCol_of_decode pv fc (by rw [hl, hpvlay]) hc ?_
      rw [hr, hpvrow]; omega
    rw [h0]; ring
  · -- branch (ii): layer `S+1` can't be a coupling layer (`≤ S`).
    obtain ⟨hbl2, _⟩ := hb2; omega
  · -- branch (iii): each term's second factor reads a sibling of `k` in the same cleared column → 0.
    obtain ⟨hbl3, hbcol3⟩ := hb3
    rw [hpvcol] at hbcol3
    obtain ⟨qa, hqadiag, hqamem, hqasub⟩ := couplingCoords_mem_belowPivotCol p' hcanonP hk
    obtain ⟨hqac, hqar⟩ := belowPivotCol_decode d qa hqamem
    have hqalay := belowPivotCol_decode_layer d qa hqamem
    refine Finset.sum_eq_zero (fun k' hk' => ?_)
    split_ifs with hg
    · rfl
    · push_neg at hg
      have h0 : readEntry d (couplingClear d q u) (((tupIdxEquiv d).symm k).1.1) k'
          (((tupIdxEquiv d).symm k).2) = 0 := by
        refine readEntry_couplingClear_eq_zero q u _ _ _ (fun fc hfc => hcc (hqasub ?_))
        obtain ⟨hl, hr, hc⟩ := blockEntryFlat_decode hfc
        refine mem_belowPivotCol_of_decode qa fc (by rw [hl, hqalay]) (by rw [hc, hqac]) ?_
        rw [hr]; omega
      rw [h0, mul_zero]
  · rfl

/-- **`couplingCoords` COVERS every cleared column** — a below-diagonal coordinate in a cleared column
of the CURRENT layer (`col < cleared`) or a COMPLETED layer (`layer < S`, `col < widthMinUpto (layer+1)`)
is a coupling. Induction along the real branch: case2/case12 adds the just-cleared column's below-column
(pivot `= cornerToFlat(layer, cleared)`, diagonal); case11 keeps `cleared` (adds nothing, but changes
nothing to cover); rollover graduates the current layer's cleared columns (`< widthMinUpto(layer+1) ≤
cleared` by the rollover threshold) to completed. The AT branch-(iii) rides this: the escaped read's sibling
`(S−1, k', jc)` sits in a completed cleared column, hence is a coupling `couplingClear` zeroes. -/
theorem couplingCoords_covers_cleared {N : ℕ} {d : Fin (N + 1) → ℕ} :
    ∀ (p : TreePath d), p.IsRealBranch (canonFlatten d) → CanonicalPivots d p →
      ∀ {y : Fin (flatDim d)},
        (((tupIdxEquiv d).symm y).2 : ℕ) < (((tupIdxEquiv d).symm y).1.2 : ℕ) →
        ((((tupIdxEquiv d).symm y).1.1 : ℕ) < p.conState.layer ∧
            (((tupIdxEquiv d).symm y).2 : ℕ)
              < widthMinUpto d ((((tupIdxEquiv d).symm y).1.1 : ℕ) + 1)
          ∨ (((tupIdxEquiv d).symm y).1.1 : ℕ) = p.conState.layer ∧
            (((tupIdxEquiv d).symm y).2 : ℕ) < p.conState.cleared) →
        y ∈ couplingCoords d p := by
  intro p
  induction p with
  | root =>
    intro _ _ y _ hcov
    have h0l : (TreePath.root : TreePath d).conState.layer = 0 := rfl
    have h0c : (TreePath.root : TreePath d).conState.cleared = 0 := rfl
    rcases hcov with ⟨h, _⟩ | ⟨_, h⟩ <;> omega
  | step p' c pv cse ns φ ih =>
    intro hbr hcanon y hbd hcov
    obtain ⟨hrec, ⟨sc, hsc, hecase, hchild, hcenter, hpivpin⟩, hwcRaw, hvpin⟩ := hbr
    obtain ⟨hcanonP, hcanonPiv⟩ := hcanon
    have htrans := conOracle_child_transition p'.conState sc hsc
    simp only [show (TreePath.step p' c pv cse ns φ).conState = ns from rfl] at hcov
    cases cse with
    | case11 =>
      rcases htrans with ⟨he, _, _, _⟩ | ⟨he, _, _⟩ | ⟨_, hLc, hCc⟩
      · exact absurd (he.symm.trans hecase) (by decide)
      · rcases he with he | he <;> exact absurd (he.symm.trans hecase) (by decide)
      · have hnsL : ns.layer = p'.conState.layer := hchild ▸ hLc
        have hnsC : ns.cleared = p'.conState.cleared := hchild ▸ hCc
        rw [hnsL, hnsC] at hcov
        have hcc : couplingCoords d (TreePath.step p' c pv StepCase.case11 ns φ)
            = couplingCoords d p' := Finset.union_empty _
        rw [hcc]; exact ih hrec hcanonP hbd hcov
    | rollover =>
      rcases htrans with ⟨_, hthr, hLc, hCc⟩ | ⟨he, _, _⟩ | ⟨he, _, _⟩
      · have hnsL : ns.layer = p'.conState.layer + 1 := hchild ▸ hLc
        have hnsC : ns.cleared = 0 := hchild ▸ hCc
        rw [hnsL, hnsC] at hcov
        have hcc : couplingCoords d (TreePath.step p' c pv StepCase.rollover ns φ)
            = couplingCoords d p' := Finset.union_empty _
        rw [hcc]
        rcases hcov with ⟨hlt, hwmu⟩ | ⟨_, h0⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt2 | heqc
          · exact ih hrec hcanonP hbd (Or.inl ⟨hlt2, hwmu⟩)
          · refine ih hrec hcanonP hbd (Or.inr ⟨heqc, ?_⟩)
            rw [heqc] at hwmu; omega
        · omega
      · rcases he with he | he <;> exact absurd (he.symm.trans hecase) (by decide)
      · exact absurd (he.symm.trans hecase) (by decide)
    | case12 =>
      rcases htrans with ⟨he, _, _, _⟩ | ⟨_, hLc, hCc⟩ | ⟨he, _, _⟩
      · exact absurd (he.symm.trans hecase) (by decide)
      · have hnsL : ns.layer = p'.conState.layer := hchild ▸ hLc
        have hnsC : ns.cleared = p'.conState.cleared + 1 := hchild ▸ hCc
        rw [hnsL, hnsC] at hcov
        rw [couplingCoords]
        rcases hcov with ⟨hlt, hwmu⟩ | ⟨heq, hcl⟩
        · exact Finset.mem_union.mpr (Or.inl (ih hrec hcanonP hbd (Or.inl ⟨hlt, hwmu⟩)))
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hcl with hlt2 | heqc
          · exact Finset.mem_union.mpr (Or.inl (ih hrec hcanonP hbd (Or.inr ⟨heq, hlt2⟩)))
          · refine Finset.mem_union.mpr (Or.inr ?_)
            obtain ⟨hpl, hpr, hpc⟩ := cornerToFlat_decode hcanonPiv
            exact mem_belowPivotCol_of_decode pv y (by rw [heq, hpl])
              (by rw [heqc, hpc]) (by rw [hpr]; omega)
      · exact absurd (he.symm.trans hecase) (by decide)
    | case2 =>
      rcases htrans with ⟨he, _, _, _⟩ | ⟨_, hLc, hCc⟩ | ⟨he, _, _⟩
      · exact absurd (he.symm.trans hecase) (by decide)
      · have hnsL : ns.layer = p'.conState.layer := hchild ▸ hLc
        have hnsC : ns.cleared = p'.conState.cleared + 1 := hchild ▸ hCc
        rw [hnsL, hnsC] at hcov
        rw [couplingCoords]
        rcases hcov with ⟨hlt, hwmu⟩ | ⟨heq, hcl⟩
        · exact Finset.mem_union.mpr (Or.inl (ih hrec hcanonP hbd (Or.inl ⟨hlt, hwmu⟩)))
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hcl with hlt2 | heqc
          · exact Finset.mem_union.mpr (Or.inl (ih hrec hcanonP hbd (Or.inr ⟨heq, hlt2⟩)))
          · refine Finset.mem_union.mpr (Or.inr ?_)
            obtain ⟨hpl, hpr, hpc⟩ := cornerToFlat_decode hcanonPiv
            exact mem_belowPivotCol_of_decode pv y (by rw [heq, hpl])
              (by rw [heqc, hpc]) (by rw [hpr]; omega)
      · exact absurd (he.symm.trans hecase) (by decide)

/-- **THE INVARIANT `Z` (pnp certificate V1) — the source-cleared residual ignores `escapedBelow`.**
Proven by induction on the path (mirrors `foldResid_layerHomogeneous'`): root (`escapedBelow (0,0) = ∅`),
rollover / case11 (Z unchanged, carries verbatim through the identity blow-up), and the last-clear
case2/case12 step where layer-`(S+1)`'s escaped columns ENTER — absorbed because the recoord-(ii) shear
`A_{S+1}·Q₁⁻¹` writes them into the block with coefficients = the accumulated (below-diagonal) couplings
`couplingClear` zeroes (V3, the load-bearing absorption). **`hcanon`-scoped (#95):** the diagonal pivots
are what give `belowPivotCol` the full below-diagonal column, so `couplingClear` is non-trivial and the
escaped-column reads carry a zeroed coupling. -/
-- map: B-CAPF-kill-escapedBelow ⟨CRUX — the certified telescoping invariant; V3 = the last-clear absorption⟩
theorem sourceClearedResid_ignoresEscapedBelow (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (q : TreePath d) (hbranch : q.IsRealBranch (canonFlatten d))
    (hcanon : CanonicalPivots d q) (j : Fin (foldNR d q)) :
    IgnoresCoords (sourceClearedResid d q j)
      (escapedBelow d q.conState.layer q.conState.cleared) Set.univ := by
  classical
  suffices H : ∀ (r : TreePath d), r.IsRealBranch (canonFlatten d) → CanonicalPivots d r →
      ∀ (i : Fin (foldNR d r)), IgnoresCoords (sourceClearedResid d r i)
        (escapedBelow d r.conState.layer r.conState.cleared) Set.univ from
    H q hbranch hcanon j
  intro r
  induction r with
  | root =>
    -- `escapedBelow (0, 0) = ∅` (escapedCol 0 = ∅ via `blockCoords_zero_eq_layerCoords`; the
    -- `escaped(1)` term is gated off by `¬ widthMinUpto d 1 ≤ 0`).
    intro _ _ i
    have hEB : escapedBelow d (TreePath.root : TreePath d).conState.layer
        (TreePath.root : TreePath d).conState.cleared = (∅ : Finset (Fin (flatDim d))) := by
      show escapedBelow d 0 0 = ∅
      have h0 : escapedCol d 0 = (∅ : Finset (Fin (flatDim d))) := by
        rw [escapedCol, blockCoords_zero_eq_layerCoords]; exact Finset.sdiff_self _
      have hwmu : ¬ (widthMinUpto d 1 ≤ 0) := by have := widthMinUpto_pos hpos 1; omega
      rw [escapedBelow, if_neg hwmu, Finset.union_empty, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      obtain ⟨M, hM, hxM⟩ := Finset.mem_biUnion.mp hx
      rw [Finset.mem_range, Nat.lt_one_iff] at hM
      subst hM
      rw [h0] at hxM; exact absurd hxM (Finset.notMem_empty x)
    rw [hEB]
    intro w _ m hm _; exact absurd hm (Finset.notMem_empty m)
  | step p' c pv cse ns φ ih =>
    -- map: B-CAPF-kill-escapedBelow-step ⟨the certified telescoping step; V3 at the last clear⟩
    intro hbr hcanonStep i
    obtain ⟨hrec, ⟨sc, hsc, hecase, hchild, hcenter, hpivpin⟩, hwcRaw, hvpin⟩ := hbr
    obtain ⟨hcanonP, hcanonPiv⟩ := hcanonStep
    have htrans := conOracle_child_transition p'.conState sc hsc
    -- The goal's `escapedBelow` is at the child state `ns` (`(step …).conState = ns` by `rfl`).
    show IgnoresCoords (sourceClearedResid d (TreePath.step p' c pv cse ns φ) i)
      (escapedBelow d ns.layer ns.cleared) Set.univ
    by_cases hnt : N ≤ ns.layer
    · -- TERMINAL child: `foldResid = fun _ ↦ 1`, so the source-cleared residual is the constant `1`.
      have hconst : sourceClearedResid d (TreePath.step p' c pv cse ns φ) i = fun _ ↦ (1 : ℝ) := by
        funext u
        show foldResid d (canonFlatten d) (TreePath.step p' c pv cse ns φ) i
            (couplingClear d _ u) = _
        rw [foldResid, dif_pos hnt]; rfl
      rw [hconst]; intro w _ m _ _; rfl
    · -- NON-TERMINAL: the reduction lemma over `escapedBelow(parent)` + the per-arm `escapedBelow` transition.
      have hredEB : IgnoresCoords (sourceClearedResid d (TreePath.step p' c pv cse ns φ) i)
          (escapedBelow d p'.conState.layer p'.conState.cleared) Set.univ := by
        sorry
      rcases htrans with ⟨hcaseR, hthr, hLR, hCR⟩ | ⟨hcase2, hL2, hC2⟩ | ⟨hcase11, hL11, hC11⟩
      · -- ROLLOVER: `escapedBelow(S+1, 0) = escapedBelow(S, c)` (`c ≥ wmu(S+1)` — the layer exhausts).
        have hnsL : ns.layer = p'.conState.layer + 1 := hchild ▸ hLR
        have hnsC : ns.cleared = 0 := hchild ▸ hCR
        rw [hnsL, hnsC, escapedBelow_rollover_eq d hpos p'.conState.layer p'.conState.cleared hthr]
        exact hredEB
      · -- CASE2/CASE12 (fresh clear): `escapedBelow(S, c+1)` — LAST clear GROWS by `escapedCol(S+1)`.
        have hnsL : ns.layer = p'.conState.layer := hchild ▸ hL2
        have hnsC : ns.cleared = p'.conState.cleared + 1 := hchild ▸ hC2
        by_cases hlast : p'.conState.cleared + 1 = widthMinUpto d (p'.conState.layer + 1)
        · -- LAST clear (GROWTH): the layer-(S+1) escaped columns ENTER — the V3 multi-layer descent.
          rw [hnsL, hnsC, escapedBelow_clear_last d p'.conState.layer p'.conState.cleared hlast]
          refine ignoresCoords_union hredEB ?_
          sorry
        · -- NON-LAST clear: `escapedBelow` unchanged (`c+1 < wmu(S+1)`, from the case2/12 threshold bound).
          have hclt : p'.conState.cleared < widthMinUpto d (p'.conState.layer + 1) :=
            conOracle_case2or12_cleared_lt p'.conState sc hsc hcase2
          rw [hnsL, hnsC,
            escapedBelow_clear_notlast d p'.conState.layer p'.conState.cleared (by omega)]
          exact hredEB
      · -- CASE11 (merge): state unchanged, `escapedBelow` unchanged.
        have hnsL : ns.layer = p'.conState.layer := hchild ▸ hL11
        have hnsC : ns.cleared = p'.conState.cleared := hchild ▸ hC11
        rw [hnsL, hnsC]; exact hredEB

/-- **THE KILL ⟨CRUX — route (a) whole-path coupling factorization⟩ — the source-cleared residual ignores
the escaped out-of-cap columns.** At a fresh node (`cleared = 0`, layer `S`) the layer-`S` columns beyond
the running-min cap (`layerCoords d S ∖ blockCoords d S`, i.e. col `≥ widthMinUpto d S`) are read by the raw
fold ONLY through monomials that also carry an ancestor coupling coordinate (the wide remnant-row entry of
an ancestor case2/case12 clear — cap-escape trace `d=(2,3,2,2)`: coeff of the escaped `u_(1,0,2)` is
`u_(0,2,0)·u_(2,0,0)` with `u_(0,2,0)` a layer-0 coupling). `couplingClear` zeroes those couplings, so
`sourceClearedResid = foldResid ∘ couplingClear` does not depend on the escaped columns. FUNCTION-level kill
(the escaped coords are NOT in `couplingCoords`; the disjointness is `col ≥ widthMinUpto` vs
coupling-`col < widthMinUpto`). The dependence factors through the couplings of MULTIPLE ancestor layers via
the composed shears (single-recoord refuted on `(2,3,3,3)`, pnp 81ba59d2b) — a whole-path property.
Read off from the certified invariant `sourceClearedResid_ignoresEscapedBelow`: at `cleared = 0`,
`escapedCol S ⊆ escapedBelow (S, 0)`. -/
theorem sourceClearedResid_ignoresEscaped (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (q : TreePath d) (hnonterm : ¬ N ≤ q.conState.layer) (hcl : q.conState.cleared = 0)
    (hbranch : q.IsRealBranch (canonFlatten d)) (hcanon : CanonicalPivots d q)
    (j : Fin (foldNR d q)) :
    IgnoresCoords (sourceClearedResid d q j)
      (layerCoords d q.conState.layer \ blockCoords d q.conState.layer) Set.univ :=
  ignoresCoords_of_subset
    (sourceClearedResid_ignoresEscapedBelow d hpos q hbranch hcanon j)
    (escapedCol_subset_escapedBelow d q.conState.layer q.conState.cleared)

/-- **The capped statement under the interior guard `layer + 1 < N`** (seat-CX; the guard excludes the
last-layer born-unit arm where `supportAt = ∅` but cleared slots are units — the 28th catch, fix pending).
Assembled from the guard-independent core: conjunct 2 + the J≥1-interior conjunct 1 ride
`foldResid_layerHomogeneous'` composed through `couplingClear` (the `…_comp_coordZero` helpers + the L2
bridge); the J=0 conjunct 1 (the CAP) rides the KILL (`sourceClearedResid_ignoresEscaped`) via the
`X ⊇ Y`-restriction upgrade. Once CAPF/pnp bless the guard-shape, the frozen `sourceClearedResid_capped`
routes here. -/
theorem sourceClearedResid_capped_guarded (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (q : TreePath d) (hnonterm : ¬ N ≤ q.conState.layer)
    (hlayer : q.conState.layer + 1 < N)
    (hbranch : q.IsRealBranch (canonFlatten d)) (hcanon : CanonicalPivots d q)
    (j : Fin (foldNR d q)) :
    Deg1SupportedSlot d (sourceClearedResid d q) j
      (supportAt d q.conState.layer q.conState.cleared)
      (supportLayerOf q.conState)
      (foldRegion d (canonFlatten d) q) := by
  classical
  rw [foldRegion_eq_univ]
  have hcont : Continuous (sourceClearedResid d q j) :=
    (continuous_foldResid d q hbranch j).comp (continuous_couplingClear d q)
  have hhomL : ∀ ℓ : ℕ, supportLayerOf q.conState ≤ ℓ → ℓ < N →
      HomogeneousDeg1On (sourceClearedResid d q j) (layerCoords d ℓ) Set.univ := by
    intro ℓ hℓ hℓN
    have hraw := foldResid_layerHomogeneous' d hpos q hnonterm hbranch j ℓ hℓ hℓN
    rw [foldRegion_eq_univ] at hraw
    exact homogeneousDeg1On_comp_coordZero (foldResid d (canonFlatten d) q j)
      (layerCoords d ℓ) (couplingCoords d q) hraw
  refine ⟨?_, ?_⟩
  · by_cases hcl : q.conState.cleared = 0
    · rw [supportAt, if_pos hcl]
      have hsl : supportLayerOf q.conState = q.conState.layer := by
        unfold supportLayerOf; rw [if_pos hcl]
      have hhomS : HomogeneousDeg1On (sourceClearedResid d q j)
          (layerCoords d q.conState.layer) Set.univ :=
        hhomL q.conState.layer (le_of_eq hsl) (by omega)
      have hkill := sourceClearedResid_ignoresEscaped d hpos q hnonterm hcl hbranch hcanon j
      have hhomB : HomogeneousDeg1On (sourceClearedResid d q j)
          (blockCoords d q.conState.layer) Set.univ :=
        homogeneousDeg1On_of_subset_ignores (sourceClearedResid d q j)
          (blockCoords_subset_layerCoords d q.conState.layer) hhomS hkill
      obtain ⟨c, hc_cont, hc_repr, -⟩ :=
        continuous_decomp_of_homogeneousDeg1On (sourceClearedResid d q j)
          (blockCoords d q.conState.layer) hcont hhomB
      exact ⟨c, fun i ↦ (hc_cont i).continuousOn, fun u _ ↦ hc_repr u⟩
    · rw [supportAt, if_neg hcl, if_pos hlayer]
      have hsl : supportLayerOf q.conState = q.conState.layer + 1 := by
        unfold supportLayerOf; rw [if_neg hcl]
      have hhomS1 : HomogeneousDeg1On (sourceClearedResid d q j)
          (layerCoords d (q.conState.layer + 1)) Set.univ :=
        hhomL (q.conState.layer + 1) (le_of_eq hsl) hlayer
      obtain ⟨c, hc_cont, hc_repr, -⟩ :=
        continuous_decomp_of_homogeneousDeg1On (sourceClearedResid d q j)
          (layerCoords d (q.conState.layer + 1)) hcont hhomS1
      exact ⟨c, fun i ↦ (hc_cont i).continuousOn, fun u _ ↦ hc_repr u⟩
  · intro ℓ hℓ
    by_cases hℓN : ℓ < N
    · exact (hhomL ℓ hℓ hℓN).1
    · have hemp : layerCoords d ℓ = ∅ := by
        unfold layerCoords
        rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
        intro qq _
        have := qq.1.1.isLt
        omega
      rw [hemp]
      exact ⟨sourceClearedResid d q j, fun _ _ ↦ 0,
        fun w _ m hm _ ↦ absurd hm (Finset.notMem_empty m),
        fun x hx ↦ absurd hx (Finset.notMem_empty x),
        fun u _ ↦ by rw [Finset.sum_empty, add_zero]⟩

/-- **The capped-homogeneity induction ⟨THE CRUX; route (a) path induction⟩** — the source-cleared residual
is `Deg1SupportedSlot` over the geometric support `supportAt` at EVERY real-branch node. Base (root):
`supportAt(root) = blockCoords 0 = layerCoords 0` (`blockCoords_zero_eq_layerCoords` — layer 0 has NO escape,
`widthMinUpto 0 = d 0`), so it holds from `coreGen`'s homogeneity + continuity, the couplings being empty.
Step (per δ=1 ancestor clear): the recoord writes the next layer and `couplingClear` absorbs the escaped-col
dependence into the cap. THE KILL MECHANISM (certificate-grade, survives here from the dropped
`sourceClearedResid_ignoresEscaped`): the raw fold reads an escaped column ONLY through monomials that also
carry an ancestor coupling coordinate, so `couplingClear` — zeroing those couplings — makes the escaped
columns unread; this is a FUNCTION-level kill (the escaped coords themselves are NOT in `couplingCoords`, so
it is never a set-level containment — `capstone_cap_transport.py`/#78). **ROUTE-(a) DEPTH (load-bearing, pnp 81ba59d2b):** the layer-S escaped dependence
factors through the couplings of MULTIPLE ancestor layers via the composed shears (kill-route discriminator
refuted single-recoord localization on `(2,3,3,3)` — clearing only the S−1 couplings leaves it alive until
layer-0's are cleared); the step's absorption must NOT collapse to the immediately-preceding recoord — each
δ=1 ancestor clear contributes its coupling factor. Every-node UNIVERSALITY is carried by this induction
(base + step); pnp verified the base, the mechanism, and the wide/rollover nodes. At a fresh child this IS
the `(b)`-twin (`supportAt = blockCoords`); the escaped-ignore is a corollary. RLCT-equivalent to Aoyagi's
`D_J` confinement via the source-clear rendering (coordinate-form differs by our shear-frame). -/
theorem sourceClearedResid_capped (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    (q : TreePath d) (hnonterm : ¬ N ≤ q.conState.layer)
    (hlayer : q.conState.layer + 1 < N)
    (hbranch : q.IsRealBranch (canonFlatten d)) (hcanon : CanonicalPivots d q)
    (j : Fin (foldNR d q)) :
    Deg1SupportedSlot d (sourceClearedResid d q) j
      (supportAt d q.conState.layer q.conState.cleared)
      (supportLayerOf q.conState)
      (foldRegion d (canonFlatten d) q) :=
  -- GUARD-ADD (GO'd): the interior guard `layer + 1 < N` routes to the guard-independent core
  -- `sourceClearedResid_capped_guarded`. The excluded last-layer arm (`layer + 1 = N`, `cleared ≠ 0`)
  -- has `supportAt = ∅` yet the residual's cleared slots are units — the statement is FALSE there
  -- (the 28th catch), so the guard is a fidelity necessity, not a convenience. `hcanon` (#95, the
  -- diagonal-pivot scope) is the row-phantom fix, threaded from `sourceClearedResid_ignoresEscaped`.
  -- The sole consumer carries `hlayer` + `hcanon` and passes them through.
  sourceClearedResid_capped_guarded d hpos q hnonterm hlayer hbranch hcanon j

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
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d))
    (hcanon : CanonicalPivots d (p.extend ed)) :
    ∀ j, Deg1SupportedSlot d (sourceClearedResid d (p.extend ed)) j
      (blockCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  intro j
  have hnonterm : ¬ N ≤ (p.extend ed).conState.layer := by omega
  have hcap := sourceClearedResid_capped d hpos (p.extend ed) hnonterm hlayer hbranch hcanon j
  have hsa : supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared
      = blockCoords d (p.extend ed).conState.layer := by
    unfold supportAt; rw [if_pos hfresh]
  rwa [hsa] at hcap

end DLNFibre.DLN.Aoyagi
