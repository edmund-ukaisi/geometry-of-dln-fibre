# genm-corankrec — item-4 `hfin` (coupled per-cell finiteness), Route A

**Seat:** formaliser (tide). **Base:** `origin/genm-3abase` (@91ace5118). **Branch:**
`origin/genm-corankrec`. **Design:** `genm-couplerad/couplerad-cert.md` §2/§4/§5/§8 (Route A, SVD-free
corank recursion). **Interface consumer:** arch1build's `routeMBox_arity4_lt_top_of_coupled` (via G2
`frontChargeBox_lt_top_of_hfin` + the LINK `shellSpine_le_frontCharge_binding`).

## What landed (green, pushed @84d335b2b)

`RouteMSJCorankRec.lean` — the item-4 INTERFACE, staked at the exact G2 shape:
- `BindingShell M t j` — the in-scope predicate (binding cut + interior shell `1≤j<r` + rankgen).
- `coupled_hfin_cell` / `coupled_hfin` — per-cell / `∀ i` coupled finiteness at a binding shell.
- in-file `example`: `frontChargeBox_lt_top_of_hfin M (t+j) c' (coupled_hfin …)` typechecks — the
  interface is EXACTLY G2's `hfin` slot (fidelity-witnessed; arch1build composes with no bridge).

Green-gated (`lean/scripts/lb`, exit 0), NATIVE, no name clash. One documented `sorry`
(`coupled_hfin_cell:70`) — the mountain.

## The mountain (`coupled_hfin_cell`) — decomposition roadmap

Target: `∫_{p ∈ box ∩ deepCell i} frontChargeIntegrand M u c' p < ⊤`, `u=t+j`, per rank-flag cell `i`.
`frontChargeIntegrand = ∫_{x∈outerDom} det(Q_bQ_bᵀ)^{−a/2}·Cresid·(E_top+E_tr)^{−q}`, `q=c'−ab/2`,
`Q_b = A_cor·deeperFlagZdeep(z)` (coupled). The coupling of charge·loss through `Q_b` is ESSENTIAL — it
does NOT factor into "charge finite × loss finite" (couplerad's central point). The resolution introduces
coordinates (Stage A) where both become tractable jointly.

Steps (couplerad §2, with banked/NEW status):

1. **Charge factoring** — `frontCharge_factor` (BANKED, exact): `frontChargeIntegrand = ofReal(det^{−a/2}
   ·Cresid)·frontLossIntegrand` (pointwise in `p`; charge is `x`-independent, pulls out of `∫_x` only —
   NOT out of `∫_p`). `frontLoss_pivotPoly_eq` (BANKED): E_top → polynomial form on `outerDom`.

2. **Fubini/Tonelli** (NEW plumbing): reorganize `∫_p ∫_x` to expose the front-block `x`-peel.

3. **Stage A — raw pivot/Schur split of the reduced deep factor `Q`** (NEW, the hardest): on the pivot
   chart, `Q = [[P,B],[C,D]] → E := D−C·P⁻¹·B` (Jac-1 translation `D↦E`), turning `{rank ≤ s}` into
   `{E=0}`; the front weights split into surviving `y = Front_surv` (Morse) + `Front_lost·E`. Matrix CoV
   → hits the `Matrix.module` diamond, transcribe raw-pi (`RouteMSJDecoratedPeelMeas.mulLeftₚ` pattern).

4. **Move 1 — y-Morse peel** (BANKED atom A): `radial_morse_residual_power_le` / `core_T_peel_le` — peel
   `∫_y (|y|²+core)^{−q}`, shift `q → q − u(ρ−k)/2`, leave residual power of the lost-block core.

5. **Move 2 — lost-block bilinear corank recursion** on `frobSq(Front_lost·E)^{−q'}·charge`:
   - front fibre peel: `fibre_lintegral_mul_le` (BANKED atom B, threshold = current row-count/2).
   - **SQUARE sub-family** (`u=M₂=n`): `routeMBoxThresholdFinite_rrp` / `core_schurGen_lt_top` (BANKED)
     closes it — lands `(4,4,4,4)`, `(5,5,5,5)`, `(3,3,4,4)`.
   - **NON-SQUARE** (`exc>0` or `u≠M₂`, e.g. `(3,4,5,4)`): NEW non-square per-corank `SchurRecStep`
     (analog of `routeMBoxThresholdFinite_rrp`), reusing the banked `core_schurGen_lt_top` wrapper.
     A fibre-peel-to-square does NOT reach the floor (couplerad §3, refuted — factor-of-2 undershoot).

6. **Charge domination** (NEW lemma; couplerad ★4): `det(Q_bQ_bᵀ)^{−a/2}` dominated per-corank on the
   binding-shell scope. Cauchy–Binet is UNAVAILABLE in Mathlib v4.29 (coordinator correction) — use
   arch1build's banked a.e.-PosDef `hGae` (det > 0 a.e.) + the `γ^hier` exponent domination.

**arity≥5** (couplerad §6, Codex-sharpened): the single-matrix reduced-bilinear model is arity-4-specific;
arity≥5 uses the banked CR-path multi-layer descent to the terminal single-matrix coupling (the deep-
stratum codim accumulates across CR-path cells). Flag if arity≥5 needs more than [arity-4 core + descent].

## Build order (couplerad §8)

(a) SQUARE sub-family FIRST (steps 1–5 with the banked RRP endpoint) — real win, no new corank lemma but
genuine new plumbing (Fubini + Stage A + A/B + charge domination). (b) NON-SQUARE per-corank `SchurRecStep`.

## Open items

- **Rankgen form** (flagged to arch1build + couplerad): `BindingShell.hrankgen` carries the STRICT
  `a+b+1 ≤ ρ`; arch1build's BackPeel derives `M₁−t ≤ ρ` (= `b ≤ ρ`, weaker). Resolve the weakest
  sufficient rankgen with couplerad (does charge-domination need `a+b ≤ ρ−1` or only `b ≤ ρ`?).
- **c'-window**: `hc'lo`/`hc'hi` carried; confirm assembly supplies both (`hc' j` + a `c' < carrierThreshold`).

## Banked-piece inventory (recon — the mountain is largely the PENDING step 2–5 chart-wiring)

The coupled-incidence route's `RouteMSJIncidenceAssembly` docstring itself lists steps 2–5 as **pending**
(the coupled Γ-peel is banked as `frontChargeIntegrand`; the chart resolution of its `∫_x` + the finite
cover are the deferred work). That pending work IS `coupled_hfin_cell`. The pieces it wires are BANKED:

- **Charge factor (step 1)** — `frontCharge_factor` (EXACT), `frontLoss_pivotPoly_eq` (E_top → polynomial):
  `frontChargeIntegrand = ofReal(det(Q_bQ_bᵀ)^{−a/2}·Cresid)·frontLossIntegrand`, and `frontLossIntegrand`
  in polynomial front-block form. Both in `RouteMSJIncidenceAssembly`.
- **Chart algebra (step 3)** — `RouteMSJIncidenceChart`: `det_chartGram`, `chartNull_Qb/_Qp/_gram`,
  `chartProj_Dcancel`, `chartProjRed_block`, `chartSwap` — the transverse-Schur `E_tr` chart reductions.
- **Front-block fibre finiteness (step 3)** — `chart4_Htilde_fibre_lt_top {N}{τ>0}{q}(hq:(N:ℝ)<2q) :
  ∫(‖H‖²+τ²)^{−q} < ⊤` (`RouteMSJIncidenceChart4Polar`); `chart5_bigcell_cov` / `chart5_rank_le_iff_schur`
  (`RouteMSJIncidenceChart5BigCell`, the big-cell coverage + rank↔Schur).
- **Exponent gate (step 4)** — `clsCodim_gate_genL` + `stratum_corner_lt_top` (`RouteMSJArity4Assembly`,
  general-L: `minAdm M ≤ clsCodim + ab`, feeding `2q < C_{ℓ,s}`); `clsCodim`/`clsCodim_gate`/`minAdm_arity3`
  (`RouteMSJIncidenceExponent`); the corner blow-up `corner_block_cube_lintegral_lt_top`.
- **Atoms** — `radial_morse_residual_power_le` / `core_T_peel_le`(`_ae`) (A, y-Morse);
  `fibre_lintegral_mul_le` (B, front fibre); `routeMBoxThresholdFinite_rrp` / `core_schurGen_lt_top` (RRP).
- **Conditional inner finiteness** — `freedSchurLoss_inner_peel_lt_top` / `_bounded_lt_top`
  (`RouteMSJFreedPeel`): per-point `∫_Γ (freedSchurLoss)^{−c'} < ⊤` given pivot-energy>0, Q_bQ_bᵀ PosDef,
  c'>ab/2 — the interface hypotheses arch1build's `hGae` + `pivotEnergy` supply a.e.
- **Cover gluing (step 5)** — `lintegral_lt_top_of_finite_cover` / `_finset_cover`
  (`RouteMSJIncidenceGluing`); the deep-cover `deepCover_aux` / `deepRankLE_eq_iUnion_cells` (`RouteMSJDeepCoverage`).

**The genuinely-NEW wiring (no cheap green sub-commit — hard multi-step lemmas):**
(w1) map `frontLossIntegrand`'s `∫_x` onto the chart-algebra + `chart4`/`chart5` H̃-fibre form, per deep-cell
rank-flag stratum; (w2) the deep-cell (CR-path rank flag) → (ℓ,s) stratum + `chart5` big-cell dispatch;
(w3) the NEW charge-domination lemma (couplerad ★4 `γ^hier`; via arch1build's a.e.-PosDef `hGae` + exponent
domination — Cauchy–Binet UNAVAILABLE v4.29); (w4) the finite-cover gluing over CRIndex. Square sub-family
(u=M₂=n) AND non-square (exc>0/u≠M₂) both land on the SAME banked terminal `routeMBoxThresholdFinite_mnp`
(schurrec's non-square SchurRecStep was REDUNDANT — `mnp` already banks the uncharged non-square terminal;
the charge is w3). RankGEN (`a+b+1≤ρ`): arch1build's `bindingShell_rankgen` LANDED @a176c92b8 (arity≥4,
`NondegBindingCut` + interior `1≤j<r`); the caller fills `BindingShell.mk`'s `hrankgen` via the L-offset.

**NATIVE-footprint note (for the fresh tide):** the terminal `routeMBoxThresholdFinite_mnp` + its chain
(`rectSchurRecStep_mnp`, `rectCore_schurGen_lt_top`, `schurCoreRect_capA_interior`, `schurCoreRect_directMorse`)
are forced-`#print axioms` `[propext, Classical.choice, Quot.sound]` — NATIVE, no `sorryAx`/`cited_aoyagi_dln`/
`monomial_rlct` (schurrec-confirmed, fresh scratch). So w1–w4 + w3 built on these + the atoms keep
`coupled_hfin_cell` NATIVE once its `sorry` is filled — verify via a force-elaborated `#print axioms
coupled_hfin` (must lose the lone `sorryAx`, gain nothing).

## Consults

- couplerad (a0bd7f4f9aa5ce4f8): confirmed the reduction is genuine multi-lemma new work even square
  (Fubini + A/B + NEW charge-domination); Cauchy–Binet unavailable v4.29.
- arch1build (a51f2dfc18c325767): hfin needed ONLY at `1≤j<r`; boundary is their `hbdryFin`; will make
  their hypothesis defeq to `coupled_hfin`'s signature.
