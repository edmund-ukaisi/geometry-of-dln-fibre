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

## ★★ ARCHITECTURE SETTLED (2026-07-16, coordinator adjudication) — READ FIRST

**Route B (coupledBox) is CANONICAL.** The shell bound is `shell → ∫ coupledBoxIntegrand = ∑cells →
per-cell coupledBox finiteness` — NOT the frontCharge/G2 detour (which only works at interior cuts). The
per-deep-cell dispatch (cells indexed by `CRIndex`, cell deep-rank `ρ_i`; `a=M₀−u`, `b=M₁−u`,
`ρ=deepTailMin M`; stratum `k := a+b−ρ_i`):

- **ALL non-generic cells (`ρ_i < deepTailMin`): NULL** ⟹ `∫ coupledBox = 0` (via
  `deepFactor_rank_ge_deepTailMin_ae` (RouteMSJDeepRankGen:163) ⟹ only the generic cell `ρ_i=deepTailMin`
  is positive-measure + the deepCell node forces rank EXACTLY `ρ_i` via `isUnit_submatrix_le_rank`, +
  `setLIntegral_measure_zero` (scratch-confirmed, ∫=0 even for +∞ integrand)). **dbuild builds this
  null-disposal** (disposes the "ρ_i<b gap" + all deficient strata at once — the corankrec null insight,
  adopted for Route B).
- **GENERIC cell (`ρ_i = deepTailMin`), by cut:**
  - **INTERIOR (`a+b ≤ ρ` = `a+b ≤ deepTailMin`, `k≤0`): MY piece.** `coupledCell_le_frontCell` VALID
    (frontCharge FINITE here) → schurrec's **interior `ChargedRectSchurCore`** (scoped `a+b ≤ ρ`, finite
    `c'<½·minAdm(![m,n,p])`; endpoint + 5-step resume ladder at `RouteMSchurWishartWeight.lean` docstring
    @847e71039; schurrec banked (A) det-monotone COMPLETE + brick 1 Gram-bridge, handed (B) to coordinator).
  - **EDGE / deep-corank (`a+b ≥ deepTailMin+1`, `k≥1`): dbuild's (D).** frontCharge is `+∞` here (the
    Wishart weight `∫_{A_cor} det(Q_bQ_bᵀ)^{−a/2}` log-diverges at `a=ρ−b+1`, super-diverges beyond;
    triply-corroborated — satred D-cert TRAP #1, edgebrick numerics, schurrec Wishart) — so NO frontCharge,
    NO ChargedRectSchurCore (its `a+b≤ρ` scope EXCLUDES the edge); coupledBox-DIRECT per-stratum instead.

**My `coupled_hfin_cell` STATEMENT (frontCharge, rankgen-scoped) stands + is reviewed** — it is TRUE at
interior cuts (its `hrankgen: a+b+1≤deepTailMin` correctly EXCLUDES the divergent edge/deep-corank cuts, e.g.
dbuild's CE `M=(2,3,2,2) u=1` violates it). But as the TOP-LEVEL route it is SUPERSEDED by Route B; my LIVE
contribution is the INTERIOR `ChargedRectSchurCore` consumption via `coupledCell_le_frontCell`. Exact interior
slot signature of `coupledBox_lt_top_of_cells`: PENDING arch1build's pin.

**Corrections folded in (were live-explored below):** (1) `ChargedRectSchurCore` is scoped `a+b≤ρ`, EXCLUDES
the edge (schurrec Wishart: charge `+∞` at `a+b=ρ+1`); (2) the corankrec null argument's step-3 assumed the
INTERIOR rankgen — at edge cuts the GENERIC cell is positive-measure + divergent, so null-disposal does NOT
rescue the frontCharge route there (Route B needed); (3) the null insight itself is CORRECT + adopted by
dbuild. The route-A / w1–w4 / w3-charged-terminal material below is **SUPERSEDED exploration** — kept for the
null-insight derivation + the banked-piece inventory + the corrections; the SETTLED architecture is this block.

## The mountain (`coupled_hfin_cell`) — decomposition roadmap [SUPERSEDED top-level route; see SETTLED block above]

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
(w3) the charge threaded THROUGH the corank recursion — a CHARGED `RectSchurCore` (see the ★ CORRECTION
below; NOT a bolt-on fold onto the uncharged `mnp`); (w4) the finite-cover gluing over CRIndex.
RankGEN (`a+b+1≤ρ`): arch1build's `bindingShell_rankgen` LANDED @a176c92b8 (arity≥4, `NondegBindingCut` +
interior `1≤j<r`); the caller fills `BindingShell.mk`'s `hrankgen` via the L-offset.

**★ w3 CORRECTION (couplerad §w3, 2026-07-16 — REFUTES the earlier "fold onto uncharged `mnp`" plan; the
fresh tide must NOT build the folded shape).** The charge does NOT fold into the loss at a shifted exponent,
and the terminal is NOT the uncharged `routeMBoxThresholdFinite_mnp`:
- Pointwise `det(Q_bQ_bᵀ)^{a/2} ≥ c·frobSq^δ` is FALSE — Front ⊥ A_cor, so the charge → ∞ on
  `{A_cor·Z_deep rank-deficient}` while the loss stays order 1; charge and loss vanish on DIFFERENT loci, no
  loss power dominates the charge.
- Any `δ>0` fold `det^{−a/2}·frobSq^{−q'} ≤ C·frobSq^{−(q'+δ)}` shifts the loss threshold to `½floor−δ`,
  which UNDER-proves on TIGHT shells (`floor = 2·T1q ⟹ ½floor = T1q`, zero slack). 396/761 in-scope shells
  are tight, INCLUDING ALL 4 dispatch witnesses ((4,4,4,4),(3,4,5,4),(5,5,5,5),(3,3,4,4)) — so a fold fails
  on exactly the targets.
- The exact fact (★4): charged codim = uncharged codim = floor, i.e. **exponent shift δ = 0** — the charge
  costs the loss NOTHING, but via CODIM, not a fold. Precise: `N_loss(e) − γ^hier(e) ≥ floor/2` for every
  ray `e`, `γ^hier(e) = max_h[a(e₁+..+e_h) − h(s−b+h)]`.

⟹ **w3 = a CHARGED `RectSchurCore`** (the charge lives IN the per-corank step, not separate). Per-corank
inequality to prove: at each rank-drop the charge exponent `a·e_h ≤` the measure/Jacobian the corank step
already frees (`γ^hier ≤ freed measure`), absorbing at δ=0. Cauchy-Binet-FREE via the Gram Schur-complement
det identity (`Matrix.det_fromBlocks`) along the recursion's pivots — NOT the spectral det-monotonicity bound
(it reintroduces a `det(Z_deepZ_deepᵀ)` charge = option-2 compounding). Square case `a=b=1`:
charge = `‖A_cor·Z_deep‖^{−1}` (concrete). ⟹ **schurrec's rect step is NOT redundant** — the terminal needs
a CHARGED variant of `mnp` (charge in the per-corank step). Banked: `hGae` (det>0 a.e., Card 2),
`Matrix.det_fromBlocks`, the uncharged `mnp` chain (to extend). Full detail + tightness data: couplerad cert §w3.

**Terminal interface (LOCKED with schurrec, 2026-07-16).** schurrec builds (scaffold underway) the charged
terminal, PARAMETRIC:
`ChargedRectSchurCore (m n p a b : ℕ) (c' T : ℝ) := ∫_{Δ∈matBox m n T} ∫_{Acor∈matBox b n T} ∫_{S∈matBox n p T}
ofReal( det((Acor·S)·(Acor·S)ᵀ)^(−a/2) · frobSq(Δ·S)^(−c') ) < ⊤`, finite for `c' < ½·minAdm(![m,n,p])`
(δ=0, UNSHIFTED). Dimensionally = `frontChargeIntegrand`'s charge exactly (Δ=Front, Acor free `b×n`, S=Z_deep;
`Acor·S = Q_b`, Gram `b×b`, a=M₀−u, b=M₁−u). **Contract:** schurrec keeps it PARAMETRIC in (m,n,p,a,b,c',T);
w1/w2 dispatches EACH deep-cell rank-flag stratum to `ChargedRectSchurCore` at that stratum's own (m,n,p) —
all (m,n,p)/exponent/shift bookkeeping is w1/w2's, not the terminal's. Deepest cell (k=ρ): (m,n,p)=(u,M₂,n_last),
terminal exp = c'−ab/2. **Threshold closes** (banked): `c' < ½·minAdm M ⟹` terminal exp `< ½·minAdm(![m,n,p])`
— deepest cell via `minAdm_le_peelCharge_add_redChain` (`minAdm M − ab ≤ minAdm(redChain u M) = minAdm(![u,M₂,n_last])`
at arity-4), per-stratum via `clsCodim_gate_genL`. **Recursion-invariant** (schurrec): dropping the shared middle
`n` keeps Q_b `b×p` (Gram always `b×b`) — so rankgen `a+b+1≤ρ` is a FIXED top-level side-hypothesis (my
`BindingShell` carries it), the wrapper stays rankgen-free, rankgen lives only in the per-corank step + endpoint.
The per-corank Gram-Schur inequality on the sum-form `Q_b = A_top·S_top + A_bot·S_bot` (NOT a block form) is
couplerad's pending §w3 input to schurrec.

**NATIVE-footprint note (for the fresh tide):** the uncharged `routeMBoxThresholdFinite_mnp` + its chain
(`rectSchurRecStep_mnp`, `rectCore_schurGen_lt_top`, `schurCoreRect_capA_interior`, `schurCoreRect_directMorse`)
are forced-`#print axioms` `[propext, Classical.choice, Quot.sound]` — NATIVE (schurrec-confirmed, fresh
scratch). The CHARGED variant (w3) must preserve this — built from `det_fromBlocks` + `hGae` + the rect chain,
all NATIVE. So once `coupled_hfin_cell`'s `sorry` is filled, verify via a force-elaborated `#print axioms
coupled_hfin` (must lose the lone `sorryAx`, gain nothing — no `cited_aoyagi_dln`).

**★ w2 dispatch must be EXHAUSTIVE by cell deep-rank ρ_i (dbuild-surfaced, 2026-07-16).** `coupled_hfin_cell`
is `∀ i : CRIndex`. The `∀ i` PROOF partitions the cells by the cell's deep-rank `ρ_i` (the CRPath descent-node
`r.1`; arity-4: `(prod (dropHead (redChain u M)) A).rank ≤ ρ_i` on the cell, read off the `deepCell` node
conjunct — NO banked `cellRank` extractor exists, rg-verified; deepatlas owner for a named one / the multi-layer
case). With `a = M₀−u`, `b = M₁−u`:
- (i) `ρ_i < b`: `Q_b = A_cor·Z_deep` has `rank ≤ ρ_i < b` for ALL `A_cor` ⟹ `Q_bQ_bᵀ` singular ⟹ `det ≡ 0` ⟹
  charge `det^(−a/2) = 0` a.e. (`Real.zero_rpow`, confirmed v4.29, a≥1) ⟹ integrand vanishes a.e. ⟹ `∫ = 0 < ⊤`
  TRIVIALLY (a Lean-convention freebie — NO charge argument needed). w2 must dispatch this branch explicitly.
- (ii) `ρ_i = a+b−1` (`a+b = ρ_i+1`; `ρ_i ≥ b` since `a≥1`): `det > 0` a.e., the TIGHT boundary — dbuild's (D)
  edge brick (`hedge` slot of arch1build's `coupledBox_lt_top_of_cells`).
- (iii) `ρ_i ≥ a+b`: interior, slack — MY route (w3 charged `ChargedRectSchurCore`, `hcell` slot).
- (iv) `b ≤ ρ_i ≤ a+b−2` (nonempty only if `a≥2`): `det > 0` a.e., `a+b ≥ ρ_i+2` — OPEN which brick covers it
  (is the edge exactly `ρ_i=a+b−1`, or `a+b ≥ ρ_i+1` covering (iv)?). couplerad's per-cell accounting must
  confirm (iv) is covered so no cell falls through — the load-bearing EXHAUSTIVENESS of the split (flagged to
  dbuild + arch1build + coordinator). The `coupled_hfin_cell` STATEMENT (∀ i) stands (reviewed); this refines
  its PROOF-dispatch plan.

## Consults

- couplerad (a0bd7f4f9aa5ce4f8): confirmed the reduction is genuine multi-lemma new work even square
  (Fubini + A/B + NEW charge-domination); Cauchy–Binet unavailable v4.29.
- arch1build (a51f2dfc18c325767): hfin needed ONLY at `1≤j<r`; boundary is their `hbdryFin`; will make
  their hypothesis defeq to `coupled_hfin`'s signature.
