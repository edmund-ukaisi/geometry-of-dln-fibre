# Statement card — general-`L` smeared `hSmeared` FIN: uniform-hLam + waist + instantiation LANDED

**Status:** The last LOWER-leg branch (the general-`L` boundary-smeared `hSmeared` ∀L) is closed
**sorry-free**, on `origin/genm-smearfin` (based on `origin/genm-smearR2 @df92d727`). Three new modules
+ one 2-line spine edit; axiom footprint `[propext, Classical.choice, Quot.sound]` (forced
`#print axioms hSmeared_boxGen`, NO `sorryAx`/`native_decide`/`monomial_rlct`). All modules green in
their full import closures. Aggregator wiring left for the controller (see the `deepLayer` clash note).

This ties **R1** (`genm-smearbox`: the box determinants) + **R2** (`genm-smearR2`: the Field-A
`hSpre_gen`) into the per-ε `SmearedChartData` and thence the unconditional `hSmeared` ∀L.

## The three pieces (from the spawn brief)

### (1) Uniform-`u` `Λ₀`/Gram bounds — `DLNFibre/DLN/RLCT/Validate/RouteMSmearedUniformLam.lean` (sorry-free)
R2's `hSpre_gen` takes `hLam` (the `Λ₀`-entry bound uniform in `u` over the box). The banked
`Lam0uG_entry_bound` returns `γ, nb, Acc` as a PER-`u` existential, but the underlying suffix recursion
builds the scalars from `M, δ, η` only — never `u`. Exposed that `u`-independence, and (Codex Option-D)
also pulled the η-free `Acc` OUTSIDE `∀ η` so the box supplier can pick ONE `η*`.

- **`wideCarrierBound_suffix_uniform`** — `∃ scalars, ∀ A` (scalar witnesses OUTSIDE `∀ A`).
- **`waist_carrier_data_uniform`**, **`Lam0uG_entry_bound_uniform`** — the uniform (`∀ u`) `Λ₀` bound.
- **`wideCarrierBound_suffix_uniformEta`** — `∃ (pub Acc η-free), ∀ η, ∃ dlb nb, …` (the η-uniform
  suffix; re-runs the induction with `∀ η` inside, `pub`/`Acc` on the outside).
- **`gram_det_ne_uniformEta`** (Gram = the `p = 0` suffix, `prodAux 0 = 1`), **`waist_carrier_data_uniformEta`**,
  **`Lam0uG_entry_bound_uniformEta`** — the η-uniform `∃ Acc, ∀ η, …` det/`Λ₀` bounds; the latter also
  exposes the `u`-free γ lower bound `(δ/2)^{L−1−q} − η·Acc − (r−1)·nb ≤ γ`.

### (2) The width-`r` waist — `DLNFibre/DLN/RLCT/Validate/RouteMSmearedWaist.lean` (sorry-free)
- **`smeared_waist`** (`M hL hNo`): `∃ q ≤ L−1, ∃ hq, M ⟨q⟩ = deepRank M ∧ ∀ t < L, deepRank M ≤ Wext M t`.

**SOUNDNESS CORRECTION** (the spawn-prompt statement was WRONG): the width lower bound is over the
FRONT layers `t < L` ONLY — NOT `∀ t` (which is FALSE at `t = L`, counterexample `M = (2,3,1)`:
`deepRank = 2`, `M ⟨2⟩ = 1`). Numerically verified: `∀ t < L` form 0 fails; `∀ t ≤ L` form 148 fails
(L∈{2,3,4}, widths 1..5). The R1 carrier corridor lives in `frontProd = prodAux (L−1)`, which reads
only front layers, so the deepest width `M ⟨L⟩` is never needed (I weakened the uniform lemmas'
`hwidth` to `∀ t, t < L → r ≤ Wext M t` accordingly).

**HYPOTHESIS** (also a correction): the waist attainment `∃ q, M ⟨q⟩ = deepRank` rests on
`NoInteriorBothDrop M`, NOT the smeared `deepRank < deepRows`. (Attainment holds under
`NoInteriorBothDrop` + `0 < L` alone — 799 cases, 0 fails; it FAILS for `InteriorDrop` cases.) There is
NO banked `¬InteriorDrop → NoInteriorBothDrop` bridge (only L=1/L=2 specials); the two are independent
strata conditions. So the general-`L` `hSmeared` carries `NoInteriorBothDrop` explicitly — the SAME
hypothesis `minAdm_eq_deepRank_mul_last` and the whole chart assembly already thread.

Proof (Codex-reconciled, single vanishing instance): (A) `deepRank ≤ M ⟨t⟩` (`t < L`) from
`Text_tach_antitone` (weak decrease) + the per-layer `Text (t+1) ≤ Wext t` (`structAdm hub`); (B) the
least `k₀` with `Text k₀ = deepRank` (`Nat.find`): `k₀ = 0 ⟹ M 0 = deepRank`; `k₀ = 1` impossible
(identity boundary `Text 0 = Text 1`); `k₀ ≥ 2` ⟹ the row drop at chain boundary `j = ⟨k₀−2⟩` forces,
via `rBlock_cBlock_interior_eq_zero`, `M ⟨k₀−1⟩ = deepRank` (`cBlock = 0`).

### (3) The instantiation — `DLNFibre/DLN/RLCT/Validate/RouteMSmearedBoxSupply.lean` (sorry-free)
- **`smearedChartData_boxGen`** — the per-ε `SmearedChartData` (as `Nonempty`, for the `Classical`
  choose): picks a single `η*` (via **`exists_eta_margins`**, all margins monotone in `η`, `Acc`s
  η-free) making the Gram/waist det margin `r·(η*·Acc_G) < (δ/2)^{L−1}`, the `Λ₀`-dominance margin
  (`γ* > 0`, with `γ* ≥ (δ/2)^{L−1−q}/2`), and the Field-A margin `s·((1/γ*)·nb)·η* ≤ δ` (the
  `O(η²)` field-A term bounded via `η² ≤ η`) all hold on `boxGen r δ η*`; then feeds the uniform det
  bounds + the Field-A `hSpre_gen` into `smearedChartDataGen_of_dets`.
- **`condBox_boxGen_frontLayers`**, **`insertNth_hN_frontBox`** — the front-carrier layers of a peeled
  point `hN ▸ insertNth p z y` (its non-pivot coords lie in `boxGen`; front slots at `t < L−1` are not
  the pivot, so land in `slotBoxGen`).
- **`coordOfG_frontSlotG_ne_pivot`**, **`coordOfG_botSlotG_ne_pivot`** — front/bottom slots ≠ pivot.
- **`hSmeared_boxGen`** — the general-`L` boundary-smeared `hSmeared`: `(2 ≤ L) → BoundarySmeared M →
  ∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`, from the structural data (`hrs`/`hr`/`hc`/`hN`/`p`/`hp`),
  the waist (`q`/`hMq`/`hwidth`/`hr0`/`hrL`), and the `minAdm` match (`hminadm`/`hminpos`), threaded
  through `smearedChartGen` + the already-∀L `hSmeared_of_smearedChart`.

### Spine edit — `RouteMAchieverDispatch.lean` (2 lines)
Widened the `hSmeared` slot of `routeMCore_box_diverges_achiever_spine` from
`∀ _:2≤L, BoundarySmeared M → BoxDiverges` to `… → NoInteriorBothDrop M → BoxDiverges`, passing the
spine's own `hNo` at the dispatch. The smeared stratum is genuinely `BoundarySmeared ∧
NoInteriorBothDrop`. No live consumer of the spine exists, so nothing breaks (verified).

## Axiom footprint (better than the brief anticipated)
`hSmeared_boxGen`, `smearedChartData_boxGen`, `smeared_waist` are all `[propext, Classical.choice,
Quot.sound]` — NO `monomial_rlct`. The brief expected `monomial_rlct` "now that the box-div fires", but
the box-DIVERGENCE (`= ⊤`) does not depend on the S2 monomial axiom; `monomial_rlct` enters DOWNSTREAM
in the cover (per `AxCheck.lean`), not in this achiever branch.

## Integration notes for the controller
1. **Structural-data derivation ∀M**: `hSmeared_boxGen` takes `hrs`/`hr`/`hc`/`hN`/`p`/`hp` as
   hypotheses. The general-`L` derivation (deepRank>0 from `1≤minAdm=deepRank·M_L`, widths pos, the
   ambient peel `routeMAmbient = n+1`, the pivot `hN ▸ p = pivotCoordG`) is banked only at L=2
   (`Fin 3`, `RouteMSmearedSquareReduce`); the general-`L` versions are a separate structural step.
2. **`deepLayer` name clash** (PRE-EXISTING, not mine): two `def deepLayer` in namespace
   `DLNFibre.DLN.RLCT` — `RouteMSmearedDecodeGen.deepLayer (hL)` (my chain) and
   `RouteMBoundaryCleanChart.deepLayer (M) (hL)` (the clean chain / dispatch). Importing both closures
   into ONE file fails `environment already contains 'deepLayer.congr_simp'`. So the final wiring
   (`hSmeared_boxGen` → the spine's `hSmeared` slot, which pulls the clean chart) needs one of the two
   `deepLayer`s renamed/protected first. The spine's slot is stated abstractly (`BoxDiverges`, no
   `deepLayer`), so the CONCLUSION types match; only the co-import at definition level clashes.

## Branch / SHA
`origin/genm-smearfin @c91130d3` (fetch + this HEAD). Build: each module green (`scripts/lb`), full
`lake build DLNFibre` gate running.
