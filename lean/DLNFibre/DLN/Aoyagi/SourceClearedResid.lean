import DLNFibre.DLN.Aoyagi.MonumentAtlas

/-!
# `DLNFibre.DLN.Aoyagi.SourceClearedResid` — the Case-1(1) chart residual (the capstone object)

The wall's boost-center property `Deg1SupportedOn … ed.center` (property **(D)**, slots `∈ ⟨ed.center⟩`)
is **FALSE** on the raw shears-only `foldResid` (the (2,2,2,2) obstruction: an ancestor below-pivot input
coupling `u₀₁₀` survives, degree-1 (property **(B)**) but outside `⟨ed.center⟩`; (B) ⊬ (D)). It is **TRUE**
of the *source-cleared* chart residual — Aoyagi's Case-1(1) local coordinate, where that coupling is fixed
by the chart's `E_J = identity` structure. This file defines that object and the two facts it carries:

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
    (hfresh : (p.extend ed).conState.cleared = 0)
    (hlayer : (p.extend ed).conState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ∀ j, Deg1SupportedSlot d (sourceClearedResid d (p.extend ed)) j
      (blockCoords d (p.extend ed).conState.layer)
      (supportLayerOf (p.extend ed).conState)
      (foldRegion d (canonFlatten d) (p.extend ed)) := by
  sorry

end DLNFibre.DLN.Aoyagi
