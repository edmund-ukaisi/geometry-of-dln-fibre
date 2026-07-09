import DLNFibre.DLN.RLCT.Validate.HeadlineGenAssembly

/-!
# `DLNFibre.DLN.RLCT.Validate.HeadlineGenBounds` — UNCONDITIONAL general-`L` headline bounds

The two general-`L` Aoyagi headline results that need **no** analytic gate: their sole open input —
the box-finiteness half `(□)` — feeds only the `≥` (equality) direction. The `≤` direction rides the
proven-`∀L` achiever box-divergence (`routeMCore_box_diverges_achiever_full'`), needing no `hbox`.

* **`aoyagi_deepest_reduction_gen`** (part (c)): the UNCONDITIONAL deepest reduction
  `⨅ w ∈ optimalSet, rlctAt (dlnLoss B) w = nRegGen/2 + rlctAtOn (dlnLoss (H−r) 0) 0`. Same
  WLOG → front-pivot → D1 `le_antisymm` fold as `aoyagi_learning_coefficient_gen`, but stopping at
  the FRONT normal form `deepest_regular_core_reduces_frontPivot_front` (gate-free).
* **`aoyagi_learning_coefficient_gen_le`** (part (b)): the UNCONDITIONAL upper bound
  `⨅ … ≤ ofReal (aoyagiLambda H r)`. Combines (c) with the reduced-core `≤`-half
  (`r1_resolution_general_le`) and the arithmetic recombination
  `reg_shift_add_core_eq_aoyagiLambda`.

The genuinely-new brick is `r1_resolution_general_le`: the `hbox`-free `≤` direction of
`r1_resolution_general`, obtained by feeding the `hdiv` box-divergence (no `hfin`) through the
`cover_ge_div` converter into `routeM_rlctAtOn_le_iInf` — the `≤` branch of
`routeM_rlctAtOn_eq_iInf` extracted so it consumes the divergence field alone. All three are
axiom-clean-three
`[propext, Classical.choice, Quot.sound]`: the `≤` lane never touches the RLCT-value axiom
`monomial_rlct` (which enters only the equality's `≥`/finiteness lane).
-/

open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The Route-M rlct-cover `≤`-half** (the divergence-only direction of the cover bridge).
From the `cover_ge_div` field alone — `|F|^{−c'}` diverges on every open `Ω ∋ 0` once `c'` is
at-or-above some leaf threshold — the local RLCT is bounded above by `⨅ᵢ monomialThreshold`. This is
the `≤` branch of `routeM_rlctAtOn_eq_iInf` (`RouteMBridge`) lifted out so it needs neither the
finiteness field `cover_le` nor the structural fields — only `[Nonempty ι]`; the `≥` branch (which
needs `cover_le`) is the half that carries the box-finiteness `(□)`. -/
theorem routeM_rlctAtOn_le_iInf {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (ι : Type) [Nonempty ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hge : ∀ c' : NNReal,
        (∃ i : ι, monomialThreshold (d i) (k i) (h i) ≤ (c' : ℝ≥0∞)) →
        ∀ Ω : Set (Fin N → ℝ), IsOpen Ω → (0 : Fin N → ℝ) ∈ Ω →
          ¬ IntegrableOn (fun x => |F x| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) x) Ω volume) :
    rlctAtOn F (0 : Fin N → ℝ) ≤ ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  apply rlctAtOn_le_of_adm_le F _
  intro c' hadm
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hgt
  obtain ⟨Ω, hΩopen, h0Ω, hint⟩ := hadm
  exact hge c' ⟨i, hi.le⟩ Ω hΩopen h0Ω hint

/-- **The R1 resolution `≤`-half at general `L`** (the `hbox`-free upper bound). For every
nondegenerate reduced-width vector `M : Fin (L + 1) → ℕ` (all layers `> 0`, at least one genuine
layer `1 ≤ L`), the deepest DLN core `dlnLoss M 0` at the origin has local RLCT AT MOST
`ofReal (lambdaCore M)`. This is the `≤` direction of `r1_resolution_general` with the
box-finiteness `hbox` DROPPED: it rides only the general-`L` `hNo`-free achiever box divergence
(`routeMCore_box_diverges_achiever_full'`, through the guard-bridge), converted to the
`cover_ge_div` shape (`routeM_coverGeDiv_of_boxDiverges`) and fed to `routeM_rlctAtOn_le_iInf`,
then transported to params and valued at `⨅ = ofReal(lambdaCore M)`. -/
theorem r1_resolution_general_le (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (hMid : ∀ s, 0 < M s) :
    rlctAtOn (fun A : Params M => dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A)
        (fun _ => 0 : Params M)
      ≤ ENNReal.ofReal (lambdaCore M : ℝ) := by
  have hpos : 1 ≤ minAdm M := one_le_minAdm_of_pos_general M hL hMid
  have hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty :=
    deepestCoords_nonempty_of_pos M hMid
  -- The box-divergence atom `hdiv`, general achiever through the guard-bridge (NO `hbox`).
  have hdiv : ∀ c' : NNReal,
      (∃ i : (routeLayerAtlas M).ι,
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
    intro c' hle ε hε
    obtain ⟨i, hi⟩ := hle
    have hguard : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞) := by
      rw [← routeLayerAtlas_value_eq_half_minAdm M hpos]
      exact le_trans (iInf_le _ i) hi
    exact routeMCore_box_diverges_achiever_full' M hpos hMid hne c' hguard ε hε
  -- Convert to the `cover_ge_div` shape and feed the `≤`-half; transport + value close it.
  have hge := routeM_coverGeDiv_of_boxDiverges (routeMCore M) (layerD M) (layerK M) (layerH M) hdiv
  rw [← rlctAtOn_routeMCore_transport M, ← routeLayerAtlas_value_eq_lambdaCore M hpos]
  exact routeM_rlctAtOn_le_iInf (routeMCore M) (routeLayerAtlas M).ι
    (layerD M) (layerK M) (layerH M) hge

/-- **(c) The UNCONDITIONAL general-`L` deepest reduction** (`∀ L ≥ 2`, all `r`, nondegenerate
widths). For a nondegenerate width vector (`r < H s`), the learning-coefficient infimum
`⨅ w ∈ optimalSet, rlctAt (dlnLoss B) w` equals the regular gauge shift `nRegGen H r / 2`
(`nRegGen H r = r·(H⁰ + Hᴸ − r)`) plus the reduced singular-core local RLCT
`rlctAtOn (dlnLoss (H−r) 0) 0`. NO analytic gate: the same WLOG → front-pivot → D1 `le_antisymm`
fold as `aoyagi_learning_coefficient_gen`, stopping at the FRONT normal form
`deepest_regular_core_reduces_frontPivot_front` (the front reduction is `hbox`-free — it is the
gauge-slice squeeze, not the reduced-core RLCT value). `aoyagiLambda`/`lambdaCore` are `B`-free, so
the WLOG transport is value-free on the right. -/
theorem aoyagi_deepest_reduction_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
      = (nRegGen H r : ℝ≥0∞) / 2
        + rlctAtOn
            (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0))
                  (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
            (fun _ => 0 : Params (fun s => H s - r)) := by
  -- STEP A: headline row/col-perm WLOG → front-pivot `B'` (+ `htop`/`hcolfront`).
  obtain ⟨P, R, hrn, hrH, hB'_rank, hB'_colfront, hB'_top, hinv⟩ :=
    headline_frontRowColPivot_exists H r B hB hL
  set B' : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
    B.submatrix (R : Fin (H 0) → Fin (H 0)) (P : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))
    with hB'def
  rw [hinv]
  -- LEAF (D1 ≥-leg at `B'`, unconditional): front deepest value + hAtV bound feed the wired core.
  have hGne := dlnLoss_deepest_core_ae_ne_zero (fun s => H s - r)
    (fun s => Nat.sub_pos_of_lt (hpos s))
  have hDeepest := deepest_regular_core_reduces_frontPivot_front H r B' hB'_rank hr hL hL2 hpos
    hB'_top hB'_colfront hGne
  have hD1ge : ∀ v ∈ optimalSet H B',
      rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL) ≤ rlctAt H (dlnLoss H B') v :=
    fun v hv => d1ge_deepestPoint_via_explicit_core_genL_wired H r B' hB'_rank hr hL v (nRegGen H r)
      hDeepest (d1ge_hAtV_explicit_close_gen H r B' v hv hB'_rank hpos hL)
  -- STEP B: D1 reduction — ⨅ over `B'` = rlctAt at the deepest point.
  have hD1 : (⨅ w ∈ optimalSet H B', rlctAt H (dlnLoss H B') w)
      = rlctAt H (dlnLoss H B') (deepestPoint H r B' hB'_rank hr hL) :=
    le_antisymm
      (iInf₂_le (deepestPoint H r B' hB'_rank hr hL)
        (deepestPoint_isDeep H r B' hB'_rank hr hL).1)
      (le_iInf₂ (fun v hv => hD1ge v hv))
  -- STEP C: front normal form (no value recovery, no `hbox`); `nRegGen` is defeq the raw product.
  rw [hD1]; exact hDeepest

/-- **(b) The UNCONDITIONAL general-`L` upper bound** (`∀ L ≥ 2`, all `r`, nondegenerate widths).
For a nondegenerate width vector, the learning-coefficient infimum is AT MOST Aoyagi's closed form
`ofReal (aoyagiLambda H r)`. NO analytic gate: (c) gives `⨅ = nRegGen/2 + rlctAtOn(core) 0`, the
`≤`-half `r1_resolution_general_le` gives `rlctAtOn(core) 0 ≤ ofReal(lambdaCore(H−r))`,
and the arithmetic recombination `reg_shift_add_core_eq_aoyagiLambda` reassembles the shift plus the
core bound into `ofReal (aoyagiLambda H r)`. The equality (not just `≤`) is the `hbox`-gated
`aoyagi_learning_coefficient_gen`; this bound is the half that needs no gate. -/
theorem aoyagi_learning_coefficient_gen_le (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) ≤ ENNReal.ofReal (aoyagiLambda H r) := by
  rw [aoyagi_deepest_reduction_gen H r B hB hr hL hL2 hpos,
    ← reg_shift_add_core_eq_aoyagiLambda H r hr hL]
  -- `nRegGen H r / 2` (LHS shift) is defeq the raw `r·(…)/2` (RHS shift); `le_refl _` unifies them.
  exact add_le_add (le_refl _)
    (r1_resolution_general_le (fun s => H s - r) hL (fun s => Nat.sub_pos_of_lt (hpos s)))

end DLNFibre.DLN.RLCT
