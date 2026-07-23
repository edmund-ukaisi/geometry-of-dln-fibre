import DLNFibre.DLN.Aoyagi.MonumentAtlas

/-!
# `DLNFibre.DLN.Aoyagi.SourceClearedResid` — the Case-1(1) chart residual (the capstone object)

The wall's boost-center property `Deg1SupportedOn … ed.center` (property **(D)**, slots `∈ ⟨ed.center⟩`)
is **FALSE** on the raw shears-only `foldResid` (the (2,2,2,2) obstruction: an ancestor below-pivot input
coupling `u₀₁₀` survives, degree-1 (property **(B)**) but outside `⟨ed.center⟩`; (B) ⊬ (D)). It is **TRUE**
of the *source-cleared* chart residual — the RLCT-equivalent rendering of Aoyagi's Case-1(1) local
coordinate (coordinate-form differs by our shear-frame; RLCT-equivalent via the source-clear per her
Lemma 1, NOT coordinate-identical to her literal Q,P image), where that coupling is fixed by the
`E_J = identity` cleared-column structure. This file defines that object and the two facts it carries:

* `sourceClearedResid d p` — `foldResid d (canonFlatten d) p` with the **ancestor coupling coordinates**
  zeroed (the below-pivot entries of every ancestor case2/case12 cleared column). This is the elder ruling
  §7's `sourceClearedResid`; the RLCT read-off runs on it, the recursion `foldResid` is UNCHANGED
  (Option 2′, ruling §7.8).
* `sourceClearedResid_eq_restrict` — the (A)-characterization tying the object to the certificate's verified
  `foldResid|_{couplings=0}` form (the fidelity anchor for pnp's exact-algebra facts).
* `rlctGlobal_sumSqFam_foldResid_eq_sourceCleared` — the **Q₁-lift bridge** (`rlctGlobal(∑F²)=rlctGlobal(∑C²)`
  via the det-1 parameter-space gauge, certificate §2). STATE-ONLY here: a tracked LIVE-frontier `sorry`,
  its render (the landed det-1-CoV machinery + pnp's `ψ_gen`) is a SEPARATE follow-on, not this seat's §4
  induction.
* `sourceClearedResid_stepMap_eq_pivot_mul` — the append's new consumed shape (L4D def-owner note): the
  `sourceClearedResid` analog of `Case1Wire.foldResid_stepMap_eq_pivot_mul`. STATE-ONLY here (tracked
  LIVE-frontier); reduces to a `couplingClear`/step-map–strict-transform commutation + the cert's
  (D)-over-`ed.center` — the load-bearing new content of the append re-point (L4D consumes it).

DEF-FORM (CONFIRMED — L4D def-owner ruling 2026-07-23, routed via controller): **(A)-primary**.
`sourceClearedResid d p j u := foldResid d (canonFlatten d) p j (couplingClear d p u)`. Rationale (L4D):
the (B)-structural recursion carries an insertion-point ambiguity the certificate does not pin, and no
canonical insertion dodges the commutation proof anyway — "(A) is the bedrock choice: def unambiguous,
per-step structure DERIVED not baked." So `sourceClearedResid_eq_restrict` is the (definitional) fidelity
anchor tying the def to the certificate's verified `foldResid|_{couplings=0}` form. -/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

variable {N : ℕ}

/-- **`IgnoresCoords` is antitone in the ignored set** — ignoring a bigger set is a stronger property, so
it descends to any subset. The read-off's `IgnoresCoords`-target step rides this: the invariant carries
`IgnoresCoords … T` for the edge-independent target `T`, and `ed.center ⊆ T` (the hard containment)
specializes it to `IgnoresCoords … ed.center` by antitonicity. General; a candidate Core-lift (a plain local name here to
avoid a `DLNFibre.Core.Aoyagi.IgnoresCoords.mono` cross-namespace clash until a second consumer). -/
theorem ignoresCoords_of_subset {D : ℕ} {c : (Fin D → ℝ) → ℝ} {S S' : Finset (Fin D)}
    {V : Set (Fin D → ℝ)} (h : IgnoresCoords c S V) (hsub : S' ⊆ S) :
    IgnoresCoords c S' V :=
  fun w hw m hm t => h w hw m (hsub hm) t

/-- **`blockCoords d 0 = layerCoords d 0`** (elder's ROOT-cap dissolution): at layer 0 every coord has
`col < d 0` by `tupIdx` type, and `widthMinUpto d 0 = d 0` (running-min over `{0}`), so the running-min
col-cap is vacuous. Powers ROOT — `supportAt(root) = blockCoords d 0` is the full layer-0 block that
`coreGen` decomposes over (`coreGen_layerHomogeneous'` on `layerCoords d 0`). Candidate MonumentAtlas-lift
(local until a second consumer). -/
theorem blockCoords_zero_eq_layerCoords (d : Fin (N + 1) → ℕ) :
    blockCoords d 0 = layerCoords d 0 := by
  have hge : d 0 ≤ widthMinUpto d 0 := by
    unfold widthMinUpto
    refine Finset.le_inf' _ _ (fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.le_zero] at hi
    exact le_of_eq (congrArg d (Fin.ext hi).symm)
  unfold blockCoords layerCoords
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => h.1, fun h1 => ⟨h1, ?_⟩⟩
  have hcast : d q.1.1.castSucc = d 0 := congrArg d (Fin.ext (by rw [Fin.coe_castSucc]; exact h1))
  exact lt_of_lt_of_le (hcast ▸ q.2.isLt) hge

/-- **`submult` is continuous in the tuple** (Core-lift candidate — a general `Core.Submult` fact,
kept local until a second consumer). By `Fin.induction` on the upper index through `submult_self`
(base) / `submult_succ` (step, `Continuous.matrix_mul`), mirroring `Core.submult_congr`'s recursion.
Feeds the ROOT `coreGen`-decomposition's continuity (the `bcoeff` are entrywise products of `submult`
factors, `continuous_multPrefix`'s analogue for a variable lower index). -/
theorem continuous_submult (d : Fin (N + 1) → ℕ) (i : Fin (N + 1)) :
    ∀ (j : Fin (N + 1)) (hij : i ≤ j),
      Continuous (fun A : Tuple (k := ℝ) d => submult d A i j hij) := by
  intro j
  induction j using Fin.induction with
  | zero =>
    intro hij
    obtain rfl : i = 0 := le_antisymm hij (Fin.zero_le _)
    simpa only [submult_self] using continuous_const
  | succ p ih =>
    intro hij
    rcases eq_or_lt_of_le hij with hie | hilt
    · subst hie
      simpa only [submult_self] using continuous_const
    · have hic : i ≤ p.castSucc := Fin.le_castSucc_iff.mpr hilt
      have hfun : (fun A : Tuple (k := ℝ) d => submult d A i p.succ hij)
          = (fun A : Tuple (k := ℝ) d => A p * submult d A i p.castSucc hic) := by
        funext A; exact submult_succ d A i p hic
      rw [hfun]
      exact (continuous_apply p).matrix_mul (ih hic)

/-- **The below-pivot entries of a case2/case12 cleared column** (the ancestor coupling coords of one
edge). Decoding `pivot` to `(layer, a, b)` via `tupIdxEquiv`, this is the flat block
`{(layer, r, b) : a < r}` — the entries of the cleared column `b` strictly below the pivot row `a`
(Aoyagi's `E_J = identity` off-diagonal, cleared at the source). -/
noncomputable def belowPivotCol (d : Fin (N + 1) → ℕ) (pivot : Fin (flatDim d)) :
    Finset (Fin (flatDim d)) :=
  (Finset.univ.filter (fun q : tupIdx d =>
      (q.1.1 : ℕ) = (((tupIdxEquiv d).symm pivot).1.1 : ℕ) ∧
      (q.2 : ℕ) = (((tupIdxEquiv d).symm pivot).2 : ℕ) ∧
      (((tupIdxEquiv d).symm pivot).1.2 : ℕ) < (q.1.2 : ℕ))).image (tupIdxEquiv d)

/-- **The ancestor coupling coordinates of a path** — accumulated over every ancestor case2/case12 edge:
the below-pivot entries of its cleared column, in the LEAF/argument coordinate frame (`u` = `foldResid p`'s
argument; pnp `capstone_closing_ii.py:20-29`, leaf-frame anchors `capstone_split_oracle.py:69` +
`capstone_adjudication.py:74`). `∅` at the root (no ancestor clears). A single map on the leaf coords — no
per-ancestor chart frame, no bridge. For a case2/case12 edge the pivot is the diagonal corner
`canonPivotOf = cornerToFlat(layer, cleared) = (layer, cleared, cleared)`, so `a = b = cleared` and the set
reads `{(layer, r, cleared) : r > cleared}` — the strictly-below-diagonal entries of each cleared column.
These are the coordinates the Case-1(1) chart fixes (`{couplings = 0}`, Aoyagi's `E_J = identity`). -/
noncomputable def couplingCoords (d : Fin (N + 1) → ℕ) : TreePath d → Finset (Fin (flatDim d))
  | .root => ∅
  | .step p _center pivot cse _ns _φ =>
      couplingCoords d p ∪
        (match cse with
         | StepCase.case2 => belowPivotCol d pivot
         | StepCase.case12 => belowPivotCol d pivot
         | _ => ∅)

/-- **The ancestor-column-clear map** — zeros the coupling coordinates of `p`, fixes the rest. This is the
restriction to `{couplings = 0}`. -/
noncomputable def couplingClear (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  fun u k => if k ∈ couplingCoords d p then 0 else u k

/-- **The accumulated blow-up pivots along a path** — the recorded pivot of every ancestor BLOW-UP step
(case11/case12/case2; a rollover has no blow-up, `canonPivotOf = none`, so its unconstrained pivot field is
excluded). Recursive, sibling to `couplingCoords`. These are the exceptional divisor coordinates; a case11
edge's reused-divisor birth corner `e₂ = canonPivotOf` is one of them (born at an earlier blow-up step). -/
noncomputable def accumulatedPivots (d : Fin (N + 1) → ℕ) : TreePath d → Finset (Fin (flatDim d))
  | .root => ∅
  | .step p _center pivot cse _ns _φ =>
      (match cse with | StepCase.rollover => (∅ : Finset (Fin (flatDim d))) | _ => {pivot})
        ∪ accumulatedPivots d p

/-- **The invariant's edge-independent `IgnoresCoords` target** (§12/§7-family; L4D + Codex + cert §4
converged, controller-ruled): the accumulated blow-up exceptionals `∪` the current descending support
block. The invariant's clean coefficients ignore THIS set; every case11 `ed.center = {e₂} ∪ partial-block
⊆ ledgerTarget` (the HARD containment `case11_center_subset_ledgerTarget`), so IgnoresCoords-ledgerTarget
specializes to IgnoresCoords-ed.center at the read-off (via `ignoresCoords_of_subset`). Edge-INDEPENDENT:
`ed.center` changes per edge, this does not. The exact INV shape that carries it (the b-ledger
representation — explicit exponents vs an ∃-bound multiset) awaits pnp's Q2; the target itself is ruled
+ bankable now. -/
noncomputable def ledgerTarget (d : Fin (N + 1) → ℕ) (p : TreePath d) : Finset (Fin (flatDim d)) :=
  accumulatedPivots d p ∪ supportAt d p.conState.layer p.conState.cleared

/-- **The source-cleared Case-1(1) chart residual** (elder ruling §7's `sourceClearedResid`) — the raw fold
residual read on the ancestor-cleared input. The (D)-carrier: `Deg1SupportedOn … ed.center` holds on THIS,
not the raw fold. Recursion `foldResid` UNCHANGED (Option 2′). (A)-primary encoding (L4D def-owner
confirmed): the OBJECT is `foldResid|_{couplings=0}`; per-step structure is DERIVED, not baked. -/
noncomputable def sourceClearedResid (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    Fin (foldNR d p) → (Fin (flatDim d) → ℝ) → ℝ :=
  fun j u => foldResid d (canonFlatten d) p j (couplingClear d p u)

/-- **Root reduction** — at the root there are no ancestor clears, so the source-cleared residual is the
bare core generator `∏A`'s entries. -/
theorem sourceClearedResid_root (d : Fin (N + 1) → ℕ) :
    sourceClearedResid d (.root : TreePath d) = coreGen d (canonFlatten d) := by
  funext j u
  show foldResid d (canonFlatten d) .root j (couplingClear d .root u) = coreGen d (canonFlatten d) j u
  have hroot : couplingCoords d (.root : TreePath d) = ∅ := rfl
  have hclear : couplingClear d (.root : TreePath d) u = u := by
    funext k
    simp [couplingClear, hroot]
  rw [hclear]
  rfl

/-- **The (A)-characterization** (`sourceClearedResid_eq_restrict`, the fidelity anchor to the certificate's
verified `foldResid|_{couplings=0}`). Definitional under the (A)-primary encoding; kept as the NAMED anchor
tying the Lean object to pnp's exact-algebra facts (which are stated against the restriction). -/
theorem sourceClearedResid_eq_restrict (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (j : Fin (foldNR d p)) (u : Fin (flatDim d) → ℝ) :
    sourceClearedResid d p j u
      = foldResid d (canonFlatten d) p j (fun k ↦ if k ∈ couplingCoords d p then 0 else u k) :=
  rfl

/-- **The exceptional b-monomial** `∏_k (u k)^(m k)` of an exponent ledger `m` (Finsupp.prod). The
accumulated exceptional divisor factor `b_i` of certificate §4 is `bMon (μ i)`. -/
noncomputable def bMon {D : ℕ} (m : Fin D →₀ ℕ) (u : Fin D → ℝ) : ℝ :=
  m.prod (fun k e ↦ (u k) ^ e)

/-- **`bMon 0 = 1`** (empty ledger — the root has no exceptionals). -/
@[simp] theorem bMon_zero {D : ℕ} (u : Fin D → ℝ) : bMon (0 : Fin D →₀ ℕ) u = 1 := by
  simp [bMon]

/-- **The b-ledger invariant `SourceClearedInv`** (certificate §4; hybrid ∃-bound multiset, pnp Q2-confirmed
+ elder-delta will bless the boost conjunct's shape). Per slot: an exponent ledger `μ` (per support coord)
and clean coefficients `q`, with the source-cleared residual `= ∑_{i∈supportAt} bMon(μ i)·q i·u i`, where
(1) `q` is continuous, (2) `q` ignores the edge-independent target `ledgerTarget p`, (3) each `μ i` reads only
accumulated exceptionals, (4) THE BOOST LEDGER — at every real case11 extension the run-block coords carry
`e₂`-exponent 0 and the extension coords carry exactly 1 (certificate §4 iv / Q3 restriction laws; the
`u_{e₂}`-divisibility of the extra block). The step law (δ=1 subtracts / δ=0 adds the pivot exponent, the
complement of `foldB`'s recursion) is the transport proofs' constructive content.

⟨ELDER-DELTA FLAG⟩ conjunct (4) (the boost ledger) is the one design point: rendered here over real case11
extensions using `ed.pivot` (= `canonPivotOf` for a case11 real branch); the elder blesses this vs a
`StepChild`/`canonPivotOf` form vs a combinatorial run-relation. Conjuncts (1)-(3) + the decomposition are
the Codex+L4D+cert-converged core. -/
def SourceClearedInv (d : Fin (N + 1) → ℕ) (p : TreePath d) : Prop :=
  ∀ j : Fin (foldNR d p),
    ∃ (μ : Fin (flatDim d) → (Fin (flatDim d) →₀ ℕ))
      (q : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ),
      (∀ i, ContinuousOn (q i) (foldRegion d (canonFlatten d) p)) ∧
      (∀ i, IgnoresCoords (q i) (ledgerTarget d p) (foldRegion d (canonFlatten d) p)) ∧
      (∀ i, ((μ i).support : Finset (Fin (flatDim d))) ⊆ accumulatedPivots d p) ∧
      (∀ ed : TreeEdge d p, ed.case = StepCase.case11 →
        (p.extend ed).IsRealBranch (canonFlatten d) →
        ∀ i ∈ supportAt d p.conState.layer p.conState.cleared,
          (i ∈ ed.center → (μ i) ed.pivot = 0) ∧ (i ∉ ed.center → (μ i) ed.pivot = 1)) ∧
      (∀ u ∈ foldRegion d (canonFlatten d) p, sourceClearedResid d p j u
        = ∑ i ∈ supportAt d p.conState.layer p.conState.cleared, bMon (μ i) u * q i u * u i)

/-- **The invariant holds on every real branch** (certificate §4 induction: ROOT = `coreGen` at `μ=0`;
δ=1 strict-transform subtracts the pivot exponent; δ=0 pullback adds it). STATE-ONLY here (tracked
LIVE-frontier — the expedition's last hard proof, decomposed into root/δ=1/δ=0 in the fill). ⟨hpos may be
needed by the cap; reconcile with the content lemma's hyps at the delta⟩. -/
-- map: B-wall-sourceClearedInv-holds (the §4 b-ledger induction)
theorem sourceClearedInv_holds (d : Fin (N + 1) → ℕ) (p : TreePath d)
    (hbranch : p.IsRealBranch (canonFlatten d)) :
    SourceClearedInv d p := by
  sorry

/-- **The Q₁-lift bridge** (certificate §2 — STATE-ONLY, tracked LIVE-frontier). The raw fold and the
source-cleared residual are related by the parameter-space unipotent `Q₁` gauge (`A_L → Q₁·A_L`,
`A_{L+1} → A_{L+1}·Q₁⁻¹`), which is det-1 and product-preserving, so the square-Frobenius loss `∑F²` is
gauge-invariant and its global RLCT is literally preserved: `rlctGlobal(∑F²) = rlctGlobal(∑C²)`. The render
is a SEPARATE follow-on consuming the landed det-1-CoV machinery + pnp's `ψ_gen`; it is NOT this seat's §4
content-lemma induction. -/
-- map: B-wall-Q1-lift-bridge (certificate §2; det-1 param-space gauge; landed det-1-CoV machinery)
theorem rlctGlobal_sumSqFam_foldResid_eq_sourceCleared (d : Fin (N + 1) → ℕ) (p : TreePath d) :
    RLCT.Global.rlctGlobal (sumSqFam (foldResid d (canonFlatten d) p))
      = RLCT.Global.rlctGlobal (sumSqFam (sourceClearedResid d p)) := by
  sorry

/-- **The append's new consumed shape** (L4D def-owner note — the `sourceClearedResid` analog of
`Case1Wire.foldResid_stepMap_eq_pivot_mul`, `Case1Wire:36-72`). For a `(D)`-carrying source-cleared
parent, the pullback through `stepMap` (blow-up OUTERMOST) factors as `u_pivot ·` the residual at the
strict-transform (`blockBlowupCoordQuot`). This is what the δ=1 append (`stepInv_child_delta1_append`,
L4D-re-pointed) consumes on the ORIGINAL center. STATE-ONLY here (tracked LIVE-frontier): its content
reduces to the `couplingClear`/(step-map vs strict-transform) COMMUTATION plus the certificate's
`(D)`-over-`ed.center` — the load-bearing new content of the append re-point. -/
-- map: B-wall-sourceCleared-stepmap-pivot-mul (append re-point; couplingClear/step-map commutation)
theorem sourceClearedResid_stepMap_eq_pivot_mul (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hdeg1 : Deg1SupportedOn (sourceClearedResid d p) ed.center (foldRegion d (canonFlatten d) p))
    (j : Fin (foldNR d p)) (u : Fin (flatDim d) → ℝ) :
    sourceClearedResid d p j (stepMap d ed u)
      = u ed.pivot
        * sourceClearedResid d p j (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  sorry

/-- **Cap-frontier obligation (b), re-stated of `sourceClearedResid`** (§12.2 CLEARED-OBJECT route,
db7b8e123; pnp-cap verified on three cap-bite witnesses). At a FRESH child (`cleared = 0`, the J=0
descent) the source-cleared residual is `Deg1SupportedSlot` over the running-min-capped `blockCoords`
of the child layer (`= supportAt(child)` there). The raw fold's out-of-cap reading is the §9 artifact;
on the cleared object the residual IS confined to the cap. This is the §7 (D)-object move on the SUPPORT
side. STATE-ONLY here (tracked LIVE-frontier); the descent-slot rollover consumer (MultiAffineStepWire)
re-points to it — L4D / later-wiring territory, this statement is made consumable. Obligation (a) (the
J≥1 cleared child, `layerCoords(S+1)`) is a SEPARATE raw-fold fact via the homogeneity route
(`foldResid_layerHomogeneous'` + a bounded step-map lemma), NOT here. -/
-- map: B-L3T-appendResidDescent-fresh-sourceCleared ⟨FRONTIER LEAF — §12.2 (b)-restatement⟩
theorem realBranch_appendResidDescent_fresh_sourceCleared (d : Fin (N + 1) → ℕ) (hpos : ∀ k, 0 < d k)
    {p : TreePath d} (ed : TreeEdge d p)
    (hroll : ed.case = StepCase.rollover)
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∀ j, Deg1SupportedSlot d (sourceClearedResid d (p.extend ed)) j
      (blockCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  sorry

/-- **The hard containment `ed.center ⊆ ledgerTarget`** (§12 / L4D's hard constraint — the piece that lets
IgnoresCoords-`ledgerTarget` specialize to IgnoresCoords-`ed.center` at the read-off). At a case11 edge the
center `{e₂} ∪ (layer-S partial block)` sits inside `(accumulated pivots) ∪ (support block)`: `e₂ =
canonPivotOf` is a recorded ancestor blow-up pivot (the reused divisor's birth corner), and the layer-S
partial block sits in `supportAt(p) = blockCoords(S)` (`cleared = 0` via `hδ`). STATE-ONLY (tracked
LIVE-frontier): the `e₂ ∈ accumulatedPivots` step rides the construction structure (the reused divisor was
born at an ancestor blow-up edge, via `IsRealBranch`/`DescendView`); the partial-block ⊆ block bound rides
`runLen ≤ widthMinUpto`. Representation-independent (no INV reference) — banked ahead of the INV. -/
-- map: B-wall-case11-center-subset-ledgerTarget (the ed.center ⊆ T containment)
theorem case11_center_subset_ledgerTarget (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ed.center ⊆ ledgerTarget d p := by
  sorry

end DLNFibre.DLN.Aoyagi
