# #112 Phase-1 builder brief — the self-contained faithful (3,3,4) composite chart + two-sided hideal

Dispatch input for a fresh `lean-formaliser`. Self-contained: everything needed is below or at the cited
paths. The MATH is verified GREEN (sympy + Gröbner) and the three recursion mechanisms are proven — this is
detail-at-scale, Codex's flagged biggest Lean risk, NOT open math.

## Goal
Build the SELF-CONTAINED faithful (3,3,4) t=(1,0) composite chart `g` + its TWO-SIDED `hideal`, end-to-end,
sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`), packaged toward a `Chart (coreGen
(3,3,4) e) 0` / `exists_coreResolution`.
- `hideal_fwd : RegionRepresents (fun i ↦ coreGen (3,3,4) e i ∘ g) (monomialFam bexp) nbhd`
- `hideal_bwd : RegionRepresents (monomialFam bexp) (fun i ↦ coreGen (3,3,4) e i ∘ g) nbhd`

## Branch / base
Off `expedition/aoyagi-engine-gate2` (tip `d960bd1ea`) — carries the value engine (Objects A/C/D:
`MonomialRLCT`, `CThetaQIPConverse`) + the four proven mechanism modules. Branch
`expedition/aoyagi-engine-routeP`; commit + push incrementally (feature branch; NEVER dev/main). Never
touch `expedition/aoyagi-full`. Build via `scripts/lb` from `lean/`; `source ~/.elan/env`.

## READ FIRST
1. `expeditions/2026-07-17-aoyagi-engine/gate3-tax-report.md` (full plan + verdicts + the composition
   finding; READ THE ADDENDA — ADDENDUM 2 locates the crux).
2. MATH blueprint (RUN, exit 0): `gate3-codex/faithful_composite_tripwire.py` (the FAITHFUL multi-term
   composite + the #124 pivot-survival tripwire, GREEN) and `theory/aoyagi-2023-reproduction/
   g-coupled-334-diagb.py` + `.../corank2-cert/cert_334_corank2.py`.
3. Four PROVEN mechanisms (committed on -gate2 — REUSE): `Core/Aoyagi/Corank2Proto.lean` (symbolic Schur
   spine), `Corank2HidealProto.lean` (L-A block-elim ℝ²¹: `blockElim_step_fwd`/`_bwd`, `cc`, `C2conc`,
   `flat`), `Corank2MaintenanceProto.lean` (L-B: `maintenance_step_two_sided`),
   `Corank2TerminalProto.lean` (L-C: `terminal_bezout`, `hideal_terminal_both`).
4. The composition primitive (UNCOMMITTED — recreate as your first routeP commit; read from
   `/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/gate2/lean/DLNFibre/Core/
   Aoyagi/Corank2CompositeProto.lean`): `regionRepresents_comp` (precompose a RegionRepresents with a
   continuous chart map `g` — ABSENT from the banked API) + `blockElim_under_chart`.
5. `Core/Aoyagi/ProductResolution.lean:80-140` (`Chart`); `DLN/Aoyagi/LeafChartWire.lean`
   (`chart_of_collapse` — RegionRepresents→`Chart` assembly, M'=1); `Core/Aoyagi/PrincipalInv.lean:293-348`
   (`terminal_bezout`); `Core/Aoyagi/BlockBlowup.lean` (`blockBlowupMap`); `DLN/Aoyagi/
   LearningCoefficient.lean:50` (`coreGen`, `flatDim`).

## The build — compose the three proven mechanisms on the literal chart
THREE composition ops (all in hand): (1) `regionRepresents_comp` [precompose g], (2)
`RegionRepresents.trans` [banked, IdealInvariance:529], (3) `terminal_bezout`. The chain:
- Connect `coreGen (3,3,4) e ∘ g` to `flat(C1·C2)∘g` — self-contained `e`; `mult`-unfold is `rfl`-cheap;
  flatten = documented dependent-width HMul tax (CLAUDE.md `abbrev`-dim-vector / literal-width mitigations).
- L-A: `⟨(∏C)∘g⟩ = ⟨peeled∘g⟩` (`regionRepresents_P_peeled` via `regionRepresents_comp`).
- **CRUX — radial factorisation of the CONCRETE `peeled∘g`**: `⟨peeled∘g⟩ = ⟨monomialFam [E]⟩` (M'=1,
  b1=E). `peeled=[T;ΔS]`; the faithful `g` makes `peeled∘g = E·q`, pivot entry = E. Reverse via
  `terminal_bezout`. Build `g` explicitly (reuse `blockBlowupMap`; the faithful multi-term shear as an
  explicit map). THE LARGE 21-var part, not covered by the isolated mechanisms (L-C was on an abstract
  residual block; this is the concrete `peeled`).
- `.trans` → both `hideal` directions; package toward `Chart`/`exists_coreResolution`.

## GUARDS (non-negotiable)
1. **FAITHFUL multi-term, NO proxy.** Shear = faithful multi-term normalization (Schur cross-term + the
   Lemma-2 recoord `C₂'=Q₂⁻¹C₂`, both layers), NOT single-term `outerShear`. A proxy = false-GREEN
   (re-commits rev-render fidelity #7). Blueprint confirms the faithful structure.
2. **#124 pivot-survival tripwire** at each terminal intersection incl. the pivot-less deepest: after
   factoring the monomial, a residual quotient has nonzero constant term. Blueprint verifies PASS. Trips →
   STOP + report.
3. **Sorry-free + `#print axioms` clean-three** (force-elaborated: delete olean + rebuild) on the delivered
   fields; green-gate full `scripts/lb DLNFibre` (name-clash guard).
4. **STOP + report on a genuine wall** (Mathlib cast/plumbing at 21 vars / coreGen flatten / radial
   self-contained; or tripwire trips) — the honest objects-only signal. Do NOT push through, proxy, or
   leave a broken build. If a break resists 3-4 fixes, revert (`git checkout -- <file>`). Report tax as you
   go; flag EARLY if larger than detail-at-scale.

## Report
Branch + SHA(s); pieces sorry-free; `#print axioms` verbatim; the tax (Mathlib machinery that fought at 21
vars, LoC, heaviest obligation); verdict GREEN (two-sided (3,3,4) hideal + fields sorry-free) or WALL/RED.
