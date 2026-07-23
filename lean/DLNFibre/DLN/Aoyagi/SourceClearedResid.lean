import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.Core.SubmultComp

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

/-! ### ROOT (b) — the CONTINUOUS layer decomposition of `coreGen`

`coreGen_layerHomogeneous'` (MultiAffineHomogWire, import-downstream) gives the layer decomposition but
only an `AffineOn` witness — no continuity of the coefficients. The ROOT base of `sourceClearedInv_holds`
needs continuous coefficients. We re-derive the decomposition here, tracking continuity via
`continuous_submult`. The small `canonFlatten`/`submult` congruence helpers also live downstream, so they
are re-derived as `private` locals (distinct names — no full-build clash). -/

private theorem canonFlatten_entry (d : Fin (N + 1) → ℕ) (u : Fin (flatDim d) → ℝ)
    (i : Fin N) (row : Fin (d i.succ)) (col : Fin (d i.castSucc)) :
    (canonFlatten d u) i row col = u (tupIdxEquiv d ⟨⟨i, row⟩, col⟩) := rfl

private theorem submult_interval_congr (d : Fin (N + 1) → ℕ) (A B : Tuple (k := ℝ) d)
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
        ih hic (fun q hq1 hq2 => h q hq1 (hq2.trans (Fin.castSucc_le_succ p))), h p hic le_rfl]

private theorem canonFlatten_layer_congr (d : Fin (N + 1) → ℕ) (p : Fin N)
    {u v : Fin (flatDim d) → ℝ} (h : ∀ x ∈ layerCoords d p, u x = v x) :
    (canonFlatten d u) p = (canonFlatten d v) p := by
  funext row col
  rw [canonFlatten_entry, canonFlatten_entry]
  refine h _ ?_
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨⟨p, row⟩, col⟩, rfl, rfl⟩

private theorem decode_layer_mem (d : Fin (N + 1) → ℕ) (ℓ : ℕ) (i : Fin (flatDim d))
    (hi : i ∈ layerCoords d ℓ) : (((tupIdxEquiv d).symm i).1.1 : ℕ) = ℓ := by
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨q, hq, hqi⟩ := hi
  rw [← hqi, Equiv.symm_apply_apply]
  exact hq

private theorem agree_layer_of_off (d : Fin (N + 1) → ℕ) (ℓ : ℕ) (p : Fin N)
    (hp : (p : ℕ) ≠ ℓ) {u v : Fin (flatDim d) → ℝ}
    (h : ∀ s, s ∉ layerCoords d ℓ → u s = v s) : ∀ x ∈ layerCoords d p, u x = v x := by
  intro x hx
  refine h x (fun hxℓ => hp ?_)
  rw [← decode_layer_mem d p x hx, decode_layer_mem d ℓ x hxℓ]

/-- **Continuous layer decomposition of `coreGen`** (ROOT (b)): each flat core generator at
`canonFlatten d` decomposes over `layerCoords d ℓ` with CONTINUOUS coefficients that IGNORE that layer.
The continuity (which `coreGen_layerHomogeneous'`'s `AffineOn` witness lacks) rides `continuous_submult`.
Consumed by the ROOT base of `sourceClearedInv_holds` at `ℓ = 0` (`supportAt d 0 0 = blockCoords d 0 =
layerCoords d 0`, `hN : 0 < N`). -/
theorem coreGen_layer_continuous_decomp (d : Fin (N + 1) → ℕ)
    (i : Fin (d (Fin.last N) * d 0)) (ℓ : ℕ) (hℓ : ℓ < N) :
    ∃ c : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ,
      (∀ x, Continuous (c x)) ∧
      (∀ x, IgnoresCoords (c x) (layerCoords d ℓ) Set.univ) ∧
      (∀ u, coreGen d (canonFlatten d) i u = ∑ x ∈ layerCoords d ℓ, c x u * u x) := by
  classical
  set ℓ' : Fin N := ⟨ℓ, hℓ⟩ with hℓ'
  have hℓ'v : (ℓ' : ℕ) = ℓ := rfl
  set a := (finProdFinEquiv.symm i).1 with ha
  set b := (finProdFinEquiv.symm i).2 with hb
  have hsuccL : ℓ'.succ ≤ Fin.last N := by
    rw [Fin.le_def, Fin.val_succ, Fin.val_last]; exact hℓ
  have h0cast : (0 : Fin (N + 1)) ≤ ℓ'.castSucc := Fin.zero_le _
  have h0succ : (0 : Fin (N + 1)) ≤ ℓ'.succ := Fin.zero_le _
  have hcastsucc : ℓ'.castSucc ≤ ℓ'.succ := Fin.castSucc_le_succ ℓ'
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
  have hencMem : ∀ p, enc p ∈ layerCoords d ℓ := by
    intro p
    simp only [henc, layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨⟨ℓ', p.1⟩, p.2⟩, rfl, rfl⟩
  have honelayer : ∀ u, submult d (canonFlatten d u) ℓ'.castSucc ℓ'.succ hcastsucc
      = (canonFlatten d u) ℓ' := by
    intro u
    rw [submult_succ d (canonFlatten d u) ℓ'.castSucc ℓ' le_rfl, submult_self, Matrix.mul_one]
  have hrepr : ∀ u, coreGen d (canonFlatten d) i u = ∑ p, coeff p u * u (enc p) := by
    intro u
    show (mult d (canonFlatten d u)) a b = _
    rw [mult_eq_submult, submult_comp d (canonFlatten d u) 0 ℓ'.succ h0succ (Fin.last N) hsuccL,
      submult_comp d (canonFlatten d u) 0 ℓ'.castSucc h0cast ℓ'.succ hcastsucc, honelayer u,
      Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c1 _ => ?_)
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c2 _ => ?_)
    rw [canonFlatten_entry]
    show M u a c1 * ((canonFlatten d u) ℓ' c1 c2 * R u c2 b) = M u a c1 * R u c2 b * _
    rw [canonFlatten_entry]; ring
  have hcoeff_ign : ∀ p, ∀ u v : Fin (flatDim d) → ℝ,
      (∀ s, s ∉ layerCoords d ℓ → u s = v s) → coeff p u = coeff p v := by
    intro p u v hag
    have hMe : M u = M v := by
      refine submult_interval_congr d _ _ _ _ _ (fun q hq1 _ => ?_)
      refine canonFlatten_layer_congr d q (agree_layer_of_off d ℓ q ?_ hag)
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc] at hq1; omega
    have hRe : R u = R v := by
      refine submult_interval_congr d _ _ _ _ _ (fun q _ hq2 => ?_)
      refine canonFlatten_layer_congr d q (agree_layer_of_off d ℓ q ?_ hag)
      rw [Fin.le_def, Fin.val_succ, Fin.coe_castSucc] at hq2; omega
    simp only [hcoeff, hMe, hRe]
  have hcanon_cont : Continuous (canonFlatten d) := (canonFlatten d).continuous
  have hcoeff_cont : ∀ p, Continuous (coeff p) := by
    intro p
    have hMc : Continuous (fun u => M u a p.1) :=
      ((continuous_submult d ℓ'.succ (Fin.last N) hsuccL).comp hcanon_cont).matrix_elem a p.1
    have hRc : Continuous (fun u => R u p.2 b) :=
      ((continuous_submult d 0 ℓ'.castSucc h0cast).comp hcanon_cont).matrix_elem p.2 b
    exact hMc.mul hRc
  refine ⟨bcoeff, ?_, ?_, ?_⟩
  · intro x
    simp only [hbcoeff]
    refine continuous_finset_sum _ (fun p _ => ?_)
    by_cases hpx : enc p = x
    · simp only [if_pos hpx]; exact hcoeff_cont p
    · simp only [if_neg hpx]; exact continuous_const
  · intro x
    refine (ignoresCoords_univ_iff_agree _ _).mpr (fun u v hag => ?_)
    simp only [hbcoeff]
    exact Finset.sum_congr rfl (fun p _ => by rw [hcoeff_ign p u v hag])
  · intro u
    rw [hrepr u]
    symm
    calc ∑ x ∈ layerCoords d ℓ, bcoeff x u * u x
        = ∑ x ∈ layerCoords d ℓ, ∑ p, (if enc p = x then coeff p u * u x else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [hbcoeff, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun p _ => by split_ifs <;> ring)
      _ = ∑ p, ∑ x ∈ layerCoords d ℓ, (if enc p = x then coeff p u * u x else 0) := Finset.sum_comm
      _ = ∑ p, coeff p u * u (enc p) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.sum_ite_eq (layerCoords d ℓ) (enc p) (fun x => coeff p u * u x),
            if_pos (hencMem p)]

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

/-- **The accumulated blow-up exceptionals of a path** (elder §9.2 REDEFINE, 2026-07-23 — was the stored
path pivots, which the free case12/case2 fan pivot need not put at the diagonal; the containment's
`e₂ ∈ accumulatedPivots` then failed). These are the **ledger birth-corner coordinates** of the node's
state: the flat coords `cornerToFlat (divBirthCoord k)` of every divisor `k` in `p.conState`'s ledger — the
exceptional divisor axes. `= { c | IsLedgerCorner d p.conState c }` (`mem_accumulatedPivots`). A case11
edge's reused-divisor birth corner `e₂ = canonPivotOf = cornerToFlat (divBirthCoord mergeIdx)` is one of
them BY CONSTRUCTION (`k = mergeIdx`), so the containment's leg-1 is immediate. `∅` at the root
(`conRoot.numDiv = 0`); the b-monomial exponents (conjunct (3)) read only these exceptional axes. -/
noncomputable def accumulatedPivots (d : Fin (N + 1) → ℕ) (p : TreePath d) : Finset (Fin (flatDim d)) :=
  Finset.univ.biUnion (fun k : Fin p.conState.numDiv =>
    (cornerToFlat d (p.conState.divBirthCoord k).1 (p.conState.divBirthCoord k).2).toFinset)

/-- **Membership in `accumulatedPivots`** — a flat coord is an accumulated exceptional iff some ledger
divisor's birth corner decodes to it (the ledger-corner characterization; `= IsLedgerCorner`). -/
theorem mem_accumulatedPivots (d : Fin (N + 1) → ℕ) (p : TreePath d) (c : Fin (flatDim d)) :
    c ∈ accumulatedPivots d p ↔
      ∃ k : Fin p.conState.numDiv,
        cornerToFlat d (p.conState.divBirthCoord k).1 (p.conState.divBirthCoord k).2 = some c := by
  simp only [accumulatedPivots, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset,
    Option.mem_def]

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

/-- **The canonical-pivot sub-family** (CAPR §9.4 spec; elder canonical-pin ruling). Along the path every
fan-free birth (`case12`/`case2`) stores the DIAGONAL counter corner `cornerToFlat (layer, cleared)` as its
pivot — Aoyagi's ledger is a canonical-frame object (Thm-3 WLOG + per-step Q,P reindex), and the fan is our
cover artifact. On this sub-family stored = diagonal = ledger corner, so all conjuncts + the read-off
coincide (the split/witness question dissolves). `case11`/`rollover` contribute nothing here (case11's pivot
is already `IsRealBranch`-pinned to `canonPivotOf`; rollover has no blow-up).

DEF-CHECK (CAPR-flagged, seat-INV resolved): the guard is δ-AGNOSTIC (NOT `edgeδ d p = true → …`). Rationale:
`foldB = ∏ u_pivot^(edgeδ)` so δ=0 steps add no `foldB` factor, BUT a divisor CAN be born at a δ=0 step (a
`case12`/`case2` fresh clear at `cleared > 0`), and the residual's b-ledger step law adds the pivot exponent
at δ=0 too (certificate §4, "δ=0 adds") — so a δ=0-born divisor's stored pivot enters `μ` and must be the
diagonal for `μ.support ⊆ accumulatedPivots` (ledger corners). Per CAPR's rule (δ=0-born possible ⟹ drop the
guard) the stronger δ-agnostic form is rendered; still satisfied by the canonical construction. -/
def CanonicalPivots {N : ℕ} (d : Fin (N + 1) → ℕ) : TreePath d → Prop
  | .root => True
  | .step p _center pivot cse _ns _φ =>
      CanonicalPivots d p ∧
        (match cse with
         | StepCase.case12 => cornerToFlat d p.conState.layer p.conState.cleared = some pivot
         | StepCase.case2 => cornerToFlat d p.conState.layer p.conState.cleared = some pivot
         | _ => True)

/-- **The invariant holds on every real branch of the canonical sub-family** (certificate §4 induction:
ROOT = `coreGen` at `μ=0` (`sourceClearedInv_root`, banked); δ=1 strict-transform subtracts the pivot
exponent; δ=0 pullback adds it). The `hcanon : CanonicalPivots d p` hypothesis (§9.4 canonical-pin) pins the
fan pivots to the diagonal so stored = ledger corner. STATE-ONLY here (tracked LIVE-frontier — the root arm
is `sourceClearedInv_root d hN`; the δ=1/δ=0 step arms are the L5-layer transport obligation consuming GM's
commutation core, wired at the full induction assembly). -/
-- map: B-wall-sourceClearedInv-holds (the §4 b-ledger induction)
theorem sourceClearedInv_holds (d : Fin (N + 1) → ℕ) (hN : 0 < N) (p : TreePath d)
    (hbranch : p.IsRealBranch (canonFlatten d)) (hcanon : CanonicalPivots d p) :
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

/-- **A case11 oracle child carries its merge-index bound and run-length cap.**
`sc.esubst.mergeIdx < s.numDiv` (the reused divisor exists) AND
`s.cleared + sc.esubst.runLen ≤ widthMinUpto d s.layer` (the run fits the layer's running-min block).
From the oracle's case-1 eligibility: the merge target `τ = s.divTilde f` satisfies `s.cleared + 1 ≤ τ`
and `τ + 1 ≤ widthMinUpto d s.layer` (the filterMap guard), `mergeIdx = f`, and `runLen = τ − s.cleared`,
so `s.cleared + runLen = τ < widthMinUpto d s.layer`. Dispatches the `conOracle` decision (terminal /
rollover / case2 give `sc.ecase ≠ case11`; case1's merge child carries both). Feeds the containment's leg-2
(the run-block ⊆ blockCoords) and ROOT's boost-vacuity (`conRoot.numDiv = 0` refutes a case11 child).
Mirrors `MultiAffineStepWire.conOracle_case11_mergeIdx_lt`'s dispatch (re-derived — that lemma is
import-downstream of this module). -/
theorem conOracle_case11_data (d : Fin (N + 1) → ℕ) (s : ConState N)
    (sc : StepChild d s) (hsc : sc ∈ (conOracle d s).stepChildren)
    (hc11 : sc.ecase = StepCase.case11) :
    sc.esubst.mergeIdx < s.numDiv ∧ s.cleared + sc.esubst.runLen ≤ widthMinUpto d s.layer := by
  by_cases h1 : N ≤ s.layer
  · have horacle : conOracle d s = oracleTerminal d s := by unfold conOracle; rw [dif_pos h1]
    rw [horacle] at hsc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
  · have hlive : s.layer < N := not_le.mp h1
    by_cases h2 : widthMinUpto d (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle d s = rolloverDecision d s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hsc
      simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hsc
      subst hsc; exact absurd hc11 (by simp)
    · have hlt : s.cleared < widthMinUpto d (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap d := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap d _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto d s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · have horacle : conOracle d s = case2Decision d s
            (widthMinUpto d s.layer - s.cleared) (d ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hsc
        simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hsc
        subst hsc; exact absurd hc11 (by simp)
      · have htar : s.cleared + 1 ≤ target ∧ target + 1 ≤ widthMinUpto d s.layer := by
          obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
          rw [List.mem_filterMap] at hmemtar
          obtain ⟨k0, -, hk0⟩ := hmemtar
          by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
              s.divTilde k0 + 1 ≤ widthMinUpto d s.layer
          · rw [if_pos hc0] at hk0
            have hdt : s.divTilde k0 = target := Option.some.inj hk0
            omega
          · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
        rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle d s = oracleTerminal d s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hsc
          simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hsc
        · have horacle : conOracle d s = case1Decision d s f (target - s.cleared)
              (widthMinUpto d s.layer - s.cleared) (d ⟨s.layer + 1, by omega⟩ - s.cleared)
              (not_le.mp h1) (by omega) (by rw [(chooseMin_spec s target hf).1]; omega) hcap := by
            unfold conOracle
            rw [dif_neg h1, dif_neg h2]
            split
            · rename_i target' heq
              obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
              split
              · rename_i f' hf'
                obtain rfl : f' = f := Option.some.inj (hf' ▸ hf)
                rfl
              · rename_i hf'
                exact absurd (hf' ▸ hf) (by simp)
            · rename_i heq
              exact absurd (heq ▸ hmin) (by simp)
          rw [horacle] at hsc
          simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
            List.not_mem_nil, or_false] at hsc
          rcases hsc with rfl | rfl
          · exact ⟨f.isLt, by show s.cleared + (target - s.cleared) ≤ widthMinUpto d s.layer; omega⟩
          · exact absurd hc11 (by simp)

/-- **The root emits no case11 child** (ROOT boost-vacuity): `conRoot.numDiv = 0`, so a case11 oracle
child would need `mergeIdx < 0` (`conOracle_case11_data`) — impossible. Powers the ROOT base of
`sourceClearedInv_holds`: the boost-ledger conjunct quantifies over real case11 extensions of the root,
of which there are none, so it is vacuous (at `μ = 0`). -/
theorem conOracle_conRoot_no_case11 (d : Fin (N + 1) → ℕ) (sc : StepChild d (conRoot : ConState N))
    (hsc : sc ∈ (conOracle d (conRoot : ConState N)).stepChildren) :
    sc.ecase ≠ StepCase.case11 := by
  intro hc11
  have hlt := (conOracle_case11_data d conRoot sc hsc hc11).1
  have h0 : (conRoot : ConState N).numDiv = 0 := rfl
  rw [h0] at hlt
  exact absurd hlt (Nat.not_lt_zero _)

/-- **The hard containment `ed.center ⊆ ledgerTarget`** (§12 / L4D's hard constraint — the piece that lets
IgnoresCoords-`ledgerTarget` specialize to IgnoresCoords-`ed.center` at the read-off). At a case11 edge the
center `{e₂} ∪ (layer-S partial block)` sits inside `accumulatedPivots ∪ supportAt`: `e₂ = canonPivotOf`
is a ledger birth-corner (`cornerToFlat (divBirthCoord mergeIdx)`, so `∈ accumulatedPivots` by the §9.2
redefine — `mem_accumulatedPivots`), and the layer-S partial block sits in `supportAt(p) = blockCoords(S)`
(`cleared = 0` via `hδ`, `runLen ≤ widthMinUpto` via `conOracle_case11_runLen_bound`).
Representation-independent (no INV reference). -/
-- map: B-wall-case11-center-subset-ledgerTarget (the ed.center ⊆ T containment)
theorem case11_center_subset_ledgerTarget (d : Fin (N + 1) → ℕ)
    {p : TreePath d} (ed : TreeEdge d p)
    (hδ : edgeδ d p = true) (hc11 : ed.case = StepCase.case11)
    (hbranch : (p.extend ed).IsRealBranch (canonFlatten d)) :
    ed.center ⊆ ledgerTarget d p := by
  classical
  obtain ⟨hrec, ⟨sc, hsc, hecase, hchild, hcenter, hpivpin⟩, hwc, hvpin⟩ := hbranch
  have hcl : p.conState.cleared = 0 := of_decide_eq_true hδ
  have hsce : sc.ecase = StepCase.case11 := hecase.trans hc11
  rw [hcenter]
  intro x hx
  simp only [canonCenterOf, hsce, Finset.mem_union] at hx
  rw [ledgerTarget, Finset.mem_union]
  rcases hx with hpiv | hrow
  · -- LEG 1: x is the reused-divisor birth corner ⟹ x ∈ accumulatedPivots (ledger corner)
    left
    rw [Option.mem_toFinset, Option.mem_def] at hpiv
    simp only [canonPivotOf, hsce] at hpiv
    rw [mem_accumulatedPivots]
    split_ifs at hpiv with hm
    exact ⟨⟨sc.esubst.mergeIdx, hm⟩, hpiv⟩
  · -- LEG 2: x in the run-block ⟹ x ∈ supportAt = blockCoords (cleared=0, runLen ≤ widthMinUpto)
    right
    rw [Finset.mem_image] at hrow
    obtain ⟨q, hq, rfl⟩ := hrow
    rw [Finset.mem_filter] at hq
    obtain ⟨-, hlayer, -, -, hqrun⟩ := hq
    have hbound := (conOracle_case11_data d p.conState sc hsc hsce).2
    rw [supportAt, if_pos hcl, blockCoords, Finset.mem_image]
    exact ⟨q, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlayer, by omega⟩, rfl⟩

/-- **ROOT base of the b-ledger invariant** (§4 (i), the induction's root case, factored standalone).
At `.root` there are no exceptionals: `μ = 0` (`bMon 0 = 1`), `accumulatedPivots = ∅` so conjunct-3 is
`∅ ⊆ ∅`, the boost conjunct is VACUOUS (`conOracle_conRoot_no_case11` — no case11 child off the root),
and `sourceClearedResid .root = coreGen` decomposes over `supportAt d 0 0 = blockCoords d 0 =
layerCoords d 0` with the CONTINUOUS `ledgerTarget`-ignoring coefficients of
`coreGen_layer_continuous_decomp` (needs `hN : 0 < N`, the ℓ=0 layer). Pivot-hypothesis-free (the root has
no pivots ⟹ the canonical-pivot sub-family is trivially met) — the turn-key root case of
`sourceClearedInv_holds` under §9.4. -/
theorem sourceClearedInv_root (d : Fin (N + 1) → ℕ) (hN : 0 < N) :
    SourceClearedInv d (.root : TreePath d) := by
  classical
  have hlayer0 : (TreePath.root : TreePath d).conState.layer = 0 := rfl
  have hcl : (TreePath.root : TreePath d).conState.cleared = 0 := rfl
  have hsupp : supportAt d (TreePath.root : TreePath d).conState.layer
      (TreePath.root : TreePath d).conState.cleared = layerCoords d 0 := by
    rw [supportAt, if_pos hcl, hlayer0, blockCoords_zero_eq_layerCoords]
  have haccum : accumulatedPivots d (TreePath.root : TreePath d) = ∅ := by
    haveI hIE : IsEmpty (Fin (TreePath.root : TreePath d).conState.numDiv) :=
      ⟨fun k => absurd k.2 (Nat.not_lt_zero _)⟩
    rw [accumulatedPivots, Finset.univ_eq_empty, Finset.biUnion_empty]
  have hlt : ledgerTarget d (TreePath.root : TreePath d) = layerCoords d 0 := by
    rw [ledgerTarget, haccum, Finset.empty_union, hsupp]
  intro j
  obtain ⟨c, hc_cont, hc_ign, hc_repr⟩ := coreGen_layer_continuous_decomp d j 0 hN
  refine ⟨fun _ => 0, c, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hc_cont i).continuousOn
  · intro i; rw [hlt, foldRegion_eq_univ (canonFlatten d) TreePath.root]; exact hc_ign i
  · intro i; rw [haccum]; simp
  · intro ed hc11 hreal
    exfalso
    obtain ⟨sc, hsc, hecase, -⟩ := hreal.2.1
    exact conOracle_conRoot_no_case11 d sc hsc (hecase.trans hc11)
  · intro u _hu
    rw [sourceClearedResid_root, hsupp, hc_repr u]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [bMon_zero, one_mul]

end DLNFibre.DLN.Aoyagi
