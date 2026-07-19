# Fold-Jacobian SPECIFY — t11 addendum (findings + re-scope + the invariant statement)

*Author: `architect-t11`. Records the three findings from grinding the PROVE (all team-lead-ACCEPTED,
Codex-corroborated `codex/fold-jacobian-scoping-answer.md`), the re-scoped headline (finding-1), and the
STATEMENT-FIRST design of the finding-2 tree-walk invariant to be gated by team-lead + counter-signed by
coverage-t08 before the maintenance grind. Companion to `fold-jacobian-specify.md` (coverage-t08).*

## Finding-1 — the `∀ t` statement is false at root-leaves (the (1,1,1)-style witness)

**Counterexample.** Take `t = .leaf l` with `l.numDiv = 1`, `l.divExp 0 = 3`. Then
`geometricLeafPaths (dCenterOfNode M) (qNodeOf M) id (.leaf l) = [(l, id)]`, so the composite is `id`:

    |det D(id) w| = |det (ContinuousLinearMap.id ℝ (Params M))| = 1

while the SPECIFY's RHS is `∏_{k} |z_{l.divCoord k}(w)|^{l.divExp k − 1} = |z_{l.divCoord 0}(w)|^2`,
which is `0` at any `w` with `z_{l.divCoord 0}(w) = 0`. So LHS `= 1 ≠ 0 =` RHS. The original `∀ t` quantifier
admits this root-leaf, so the statement is false as written.

**Re-scope (team-lead-APPROVED).** The only consumer (`chartBridge_buildTree`) needs the ROOT build. The
sibling cover SPECIFY `geoAtlas_imageCover` already carries `htree`; the fold SPECIFY omitting it was the
defect. Honest scope:

    t = buildTree M (conOracle M) (conRoot M)

`conRoot` has `numDiv = 0`, so the root-leaf degeneracy cannot occur (an empty analytic ledger ⟹ empty
product `= 1 = |det id|`). Codex sharpened: `buildTree … s` at an *arbitrary* `s` is insufficient (a non-root
`s` already carries divisors the composite does not blow up) — the specialization must be `conRoot`.

## Finding-3 — per-pivot `divCoord`/`divExp` (upstream, co-designed here)

`geoAtlas` currently sets each piece to `{ leaf with chartMap := composite }`, so every fan-out copy of a
leaf shares the leaf's `divCoord`/`divExp`; but the fan-out over `p : Fin (dCenterOfEdge …)` gives each copy
a distinct exceptional coordinate `cNodeOf … (offset+p)` (`cNodeOf` injective). So `LeafJacobian`/`LeafPullback`
(which read the piece's `divCoord`) fail for every non-birth-corner piece.

**#35 IS THE SEAM-FIX UNIFICATION (elder ruling, compass fork 14) — NOT a bolted-on override.** The elder
diagnosed the emission seam as MIS-FACTORED: the ledger (`{lc.1 …}`) and the geometry (`chartMap := lc.2`) are
two structures reconciled after the fact, which is the root of BOTH drift defects (finding-1 falsity and
finding-3 mismatch). The fix is to correct the SEAM itself, not to add a per-pivot `divCoord` override on top
of `{lc.1 with chartMap := lc.2}` (a bolted-on override is GATED-REJECTED at review). Concretely:
`geometricLeafPaths` emits, per path, **ONE record whose `chartMap` AND per-pivot `divCoord`/`divExp` all
derive from the SAME path fold**; `geoAtlas` just reads that record. The payoff is direct: the finding-2
cocycle then becomes **near-definitional maintenance of that one recursion** (each fold step extends `chartMap`
by `geoChartMap` AND the ledger by the step's pivot in lockstep), instead of a reconciliation theorem against a
possible ledger↔geometry mismatch — the wall gets structurally smaller. The co-folded per-path ledger:

- `divCoord (piece) = ` the birth-corner flat coords `cNodeOf n_j (pivot_j)` of the divisors born on the piece's
  root→leaf path (one per path level that births/merges a divisor) — emitted by the SAME recursion that builds
  `chartMap`, so they cannot drift;
- `divExp (piece) = ` the **accumulated** exponents (per `stepUpdate`), NOT a uniform value.

Sequenced: only after t10's countersigned clause-(A) batch lands (`GeoChart.lean` ownership; do NOT edit before).

**Design-note-(i) answer (co-design with finding-2):** the per-EDGE Jacobian exponent is *uniform*
(`dCenterOfNode n − 1`, from `geoChartMap_fderiv_det`), but the per-PIVOT `divExp` is *not* uniform — it
accumulates per `stepUpdate` case (see the exponent bookkeeping below). So the finding-3 emission must carry a
per-pivot `divExp` computed from the case, not a single `dCenterOfNode`-derived number.

**Design-note-(ii) (clause C at assembly):** the fix changes ledger FIELDS, not `chartMap`, so t10's cover
proof (images only) is unaffected; but clause (C) (`divExp ∈ terminalExponents t`) must be re-verified for the
per-pivot pieces at assembly (the per-pivot `divExp` values must lie in `terminalExponents`).

## Finding-2 — the maintenance invariant. CERT-CORRECTED (pnp-fold, `threads/18-fold-regroup/cert-fold-regroup.md`).

The regrouping cert is back (7/7 sympy, Codex-blind agreement). The three per-case exponent identities are
CONFIRMED (case-2 clean; case-1(1) re-merges onto the mergeIdx diagonal birth corner; case-1(2) inherits
`divExp(mergeIdx)+runLen·resCols`). Two STATEMENT-LEVEL corrections to the shape gated earlier, plus a binding
kill-condition — all caught pre-grind (the cert did its job).

**CORRECTION 1 — state the invariant as the relative-Jacobian COCYCLE, not the subtree-relative `pieceLedger`
motive above.** My addendum's structural-induction-on-`t` (node `n` OUTERMOST, subtree-relative ledger) does
NOT close case-1(1)/(2): the inherited/merged divisor `mergeIdx` is born OUTSIDE the subtree, so a
subtree-relative ledger cannot carry its inheritance. This lands back on the ORIGINAL finding-2 framing (the
one-step relative-Jacobian cocycle telescoping from `conRoot = 1`); the addendum's subtree refinement was the
wrong turn. The closable form (cert §2), adding a chart `B` (center `C`, pivot `p`) at the INNERMOST position to
a composite `Φ'` whose ledger monomial is `L`:

    |det D(Φ' ∘ B)| w = L(B w) · |det DB| w = L(B w) · |z_p(w)|^{|C| − 1}      (chain rule + the banked atom)

The three `stepUpdate` cases are then ELEMENTARY substitution algebra on `L(B w)` (the incoming ledger pulled
back through `B`), with `b := runLen·resCols`:
- **birth (case-2):** ledger cells are spectators of `B` ⟹ `L(B w) = L(w)`; append the fresh factor `|z_p(w)|^{b_birth − 1}`.
- **merge (case-1(1)):** `p = μ` is `B`'s pivot ⟹ `L(B w) = L(w)`; new atom `|z_μ|^b`; `μ`-exponent `(D−1)+b = (D+b)−1`.
- **split (case-1(2)):** `B` sends `z_μ ↦ z_p·z_μ`, so `L(B w)` turns `|z_μ|^{D−1}` into `|z_p·z_μ|^{D−1}`; times
  the new atom `|z_p|^b` gives `|z_μ|^{D−1}·|z_p|^{(D+b)−1}` — the OLD divisor `μ` (exp `D`) and the NEW divisor
  `p` (exp `D+b`), exactly `stepUpdate.case12`.

The `L(B w)` pullback is where the case-1(2) inheritance becomes LOCAL — this is the honest content of "cocycle
telescoping from `conRoot = 1`", stronger than chain-rule + atoms (chain rule carries no `stepUpdate` info).
This cocycle is **construction-INDEPENDENT** (my Phase-2 `abs_det_fderiv_foldr_comp` style — a ledger-threaded
`foldr` over the chart list) and is SAFE to adopt under every construction-fix option. It supersedes the
subtree-relative motive and the `acc`-generalization above (which was for the outermost-on-`t` induction; the
cocycle folds innermost-first and threads `acc` as `Φ'`'s outermost prefix).

**CORRECTION 2 — case-1(2)'s inherited `divExp(mergeIdx) − 1` is NON-LOCAL** (cert §3). It is NOT realized at the
case-1(2) node's own atom (which carries only `|z_p|^{runLen·resCols}`). It is realized at `mergeIdx`'s ANCESTOR
birth atom, whose read of the u-corner `z_μ` sees the case-1(2) node's scaling `z_μ ↦ z_p·z_μ` and so spawns
`z_p^{divExp(mergeIdx)−1}` — captured exactly by the `L(B w)` pullback of split above. The addendum's row-3
"comes from the [case-1(2)] intermediate-point substitution" was the wrong attribution.

### KILL-CONDITION (cert §4) — BINDING, gate item upstream of #35

The identity **FAILS** on the current shared-child `geometricLeafPaths` for a fan-out copy that births a
NON-terminal divisor at an OFF-diagonal pivot cell. Exact discrepancy: `J_Φ = L · (z_diag / z_pivot)^{runLen·resCols}`
— the merge/split power lands on the mergeIdx DIAGONAL birth corner `z_{divBirthCoord(mergeIdx)}` (the state-level
u-corner every descendant references), not on the off-diagonal pivot the per-pivot ledger names. So **per-pivot
`divCoord` (finding-3) is NECESSARY but NOT SUFFICIENT** — a descendant's u-corner reference is `divBirthCoord`
(state-level, diagonal) and cannot be made per-pivot; an off-diagonal non-terminal copy's `|det Dβ|` is a
two-cell monomial no single-cell `divExp` can express. Terminal off-diagonal fan-out charts are FINE.

**Scoped condition (the sharp line):** the fold-Jacobian holds iff every divisor a descendant references is born
at its `divBirthCoord` diagonal — equivalently, off-diagonal fan-out charts are TERMINAL. HOLD #35's final shape:
the construction fix that secures this is elder-adjudicated now (options: diagonal-normalization — compose the
pivot↔diagonal transposition into `geoChartMap`, `|det swap| = 1` so my atom is untouched, ledger stays
state-level, shared child honest; vs per-copy child-relabeling; vs proving off-diagonal-non-terminal
unreachable). The Lean statement must carry this (a `DivBirthInv` extension: geometric birth pivot of any
subsequently-referenced divisor `= divBirthCoord` diagonal) OR the construction must enforce it.

## §4 RESOLVED — elder ruling fork 15: DIAGONAL-NORMALIZATION (supersedes finding-3 per-pivot ledger)

The kill-condition is resolved by **diagonal-normalization** (elder fork 15; supersedes the fork-14 co-folded
per-piece ledger). Compose the cube-invariant SOURCE swap `S = (cNodeOf(pivot) ↔ divBirthCoord diagonal)` into
`geoChartMap` (inside the existing `dite`); then birth = reference = diagonal for every fan-out copy, the
off-diagonal discrepancy `(z_diag/z_pivot)^b` vanishes, and the STATE-LEVEL leaf ledger `{lc.1 with chartMap :=
lc.2}` is correct for every copy. **finding-3 DISSOLVES** — no per-pivot `divCoord`/`divExp` anywhere; the child
stays shared; the symmetric quotient survives. **My spine is UNTOUCHED**: the swap is additive and `|det S| = 1`
(it is a coordinate transposition, hence an involution — `clm_involutive_abs_det_one`, banked in
`GeoJacobianFold.lean`), so the per-edge atom reads `z_diag` where it read `z_pivot`, and the parametric fold is
unchanged.

**Fidelity grounding (for docstrings):** Aoyagi's `u_{s,k}` is ONE abstract, chart-local coordinate per divisor,
never reified to a matrix cell — the diagonal-vs-pivot distinction was OUR reification artifact; the swap picks
the canonical cell representative (`|det| = 1`, geometry-isomorphic), keeping the ledger a symmetric quotient.
Cite `worked.tex:483-508`.

**#35 RESHAPED (three small pieces, `GeoChart.lean`, on t10's merge):** (1) compose `S` into `geoChartMap`
inside the `dite`; (2) the swap-composition-clean lemma — deeper swaps never disturb an ancestor's diagonal —
discharged from BANKED `DivBirthInv` freshness (`cleared ⊥ un-cleared` cells); (3) the thin wrapper reusing the
per-edge atom through `S` (`|det S| = 1` via `clm_involutive_abs_det_one`, so the atom reads `z_diag`).

## Fill-target status

Banked NOW (construction-stable, additive, no GeoChart conflict): `clm_involutive_abs_det_one`
(`GeoJacobianFold.lean`) — the swap's det-neutrality atom, which #35's wrapper consumes. The cocycle-form
maintenance statement (§2) is adopted (construction-independent). Deferred to t10's GeoChart merge (file-lock):
the three #35 pieces above, then the §0 chart-action lemma (now against the NORMALIZED `geoChartMap`) + the §2
cocycle maintenance against the STATE-LEVEL ledger (the cert's diagonal-control scenario — no off-diagonal
discrepancy remains). The banked spine — per-edge atom (`GeoJacobianSpec.lean`) + parametric fold + the
involution atom (`GeoJacobianFold.lean`) — is all construction-stable and unaffected by the normalization.
COORDINATE with team-lead at t10's landing: t10 has a post-swap cover VERIFY (threads `S`; superset route is
swap-invariant, cheap) — sequence the re-green, not simultaneous.

**pnp-loss impact on #35 scope (`threads/19-loss-factorization/cert-loss-factorization.md`).** LeafPullback
HOLDS-WITH-CONDITIONS: it CONFIRMS the Jacobian-vs-loss split (terminal divisors are loss-power exactly 2; the
case-1(1) re-merge accumulates in the JACOBIAN `divExp`, not the loss — exactly this addendum's picture), but
it is FALSE for the PURE-β `chartMap` at every depth (already L=2) — the R-b source gauge `α` (the det-1 Schur
shear on ratio coords, `ShearReconcile.elemShear`) must be IN the chart, else the residual keeps the
determinantal singularity and the lower squeeze `0 < lo` dies. So #35's chart composition may GROW from `S`
alone to `S + α` (elder charge-3 reconciles S+α-in-one-pass vs α-as-its-own-rung, and the swap/shear
composition-cleanliness interaction; #35 start HELD for that ruling). **The spine covers `S + α` with no new
atom:** both gauges are det-neutral — `|det S| = 1` (`clm_involutive_abs_det_one`) and `|det α| = 1`
(`abs_det_fderiv_elemShear`, banked) — so the per-edge det through `geoChartMap ∘ S ∘ α` is
`|z_diag|^{dCN−1} · 1 · 1` by the chain rule (`clm_det_comp`), unchanged. Cert condition (2) (gauges compose
coherently: `chartMap`, `srcBox` AND `resCoord` all transformed across the fold) is a #35/construction concern.

## FINAL SCOPE — charge-3, PARAMETRIC-GAUGE FORM (fork 15 re-amended). Settled.

`geoChartMap_e = (β ∘ S) ∘ g` — **S concrete** (the diagonal-placement permutation,
`clm_involutive_abs_det_one`; S fixes WHICH cell the monomial lands in — without it the cocycle statement
is false, charge-2) and **g a COMPOSABLE det-1 source-gauge SLOT** (`g = id` NOW; the incidence shear
`α = ShearReconcile.elemShear`, `|det Dα| = 1`, instantiated LATER), with `srcBox = g⁻¹(cube)`. Strictly
better than baking α in (my parametric-design pattern applied to the last piece, elder-endorsed):
- **(i) the fold-det cocycle is g-det-1-TRANSPARENT** — proven parametric in a det-1 `g` via the banked
  `abs_det_fderiv_comp_det_one_gauge` (`|det D((β∘S)∘g) w| = |det D(β∘S) (g w)|` for any det-1 `g`) +
  `clm_det_comp`. **PLAN: prove the cocycle parametric-in-det-1-`g`** (robust; no re-work when α lands).
- **(ii) t10's cover is g-IMAGE-INVARIANT** — `(β∘S)(g(g⁻¹(cube))) = (β∘S)(cube)`; its proof transfers
  verbatim under any `g`.
- **(iii) α's later instantiation is a parametric FILL, no redefinition ripple** — the cert's coherence
  condition is satisfied STRUCTURALLY (gauge designed into `chartMap` + `srcBox` from the start).

BANKED for this form (all sorry-free, axiom-clean, `GeoJacobianFold.lean`): `clm_involutive_abs_det_one`
(S det-1), `abs_det_fderiv_comp_det_one_gauge` (g/α transparency), `clm_det_comp` — so the Jacobian side of
#35 is reduced to wiring + the cocycle maintenance; every det atom it consumes is in hand.

The `srcBox = g⁻¹(cube)` coherence (`(β∘S∘g)(g⁻¹(cube)) = (β∘S)(cube)`) keeps the IMAGE unchanged (cover
verbatim, clause A) while `srcBox ⊆ cube` of radius `R(1+R)` keeps clause B — the R2-pre-rung
"localSub = ψ∘β" plan with `ψ = S ∘ g`, one definition, no two-pass domain re-shape.

**CLAUSE FACTORING (the Jacobian side is untouched):** `|det D(β ∘ S ∘ α)| = |det Dβ| · 1 · 1` — α is
PURELY LeafPullback's concern. The split:
- **`{β + S + the cocycle fold}` → LeafJacobian** — my scoped work, unchanged (the per-edge atom reads
  `z_diag` through S; the §2 cocycle maintenance against the STATE-LEVEL ledger closes it).
- **`{α}` → the LeafPullback squeeze** — build-against-spec (cert-specified exact `lo/hi`; `lo = 1` at
  `resRank = 0`). OWNER decided at my #35 landing (me or a fresh loss-seat).

**`resRank = 0` is PROVEN** (`leaves_resRank_zero`, `EngineConstruction:2545`): the spine fully
diagonalizes (Aoyagi's `diag(b)` terminal). Consequences: the cert's "transform `resCoord`" coherence is
VACUOUS on the spine (`resCoord` empty); `baseForm = 1`, `lo = 1` in the squeeze; the Morse clauses are
carried-for-generality. **No-circularity (docstrings):** the LEDGER asserts `resRank = 0` (proven);
LeafPullback + α proves the GEOMETRY realizes it — α is load-bearing precisely to make the pure-β
residual actually diagonalize.

**Composition-cleanliness:** charge-2's obligation generalized to a det-1 gauge, discharged from the SAME
`DivBirthInv` freshness (S and α are step-local to the current block, disjoint from ancestor cleared
diagonals — effectively disjoint supports within a step; the within-step order is an implementation
detail against the cert's coherence identity).

**Build order on t10's merge:** (1) `geoChartMap` ← β+S+α with `srcBox' = g_e⁻¹(cube)` (GeoChart, +the
coherence identity `(β∘g_e)(srcBox') = β(cube)`); (2) the composition-clean lemma (DivBirthInv freshness);
(3) the per-edge wrapper (`|det D(β∘S∘α)| = |z_diag|^{dCN−1}` via the banked det-neutral atoms + `clm_det_comp`);
(4) §0 chart-action against the normalized `geoChartMap`; (5) the §2 cocycle maintenance → LeafJacobian.
Then re-green coordination with t10's post-swap cover VERIFY.

## HANDOFF to t14-regroup (t11 stand-down; what's in my head, not yet in artifacts)

**STATE AT HANDOFF.** #35 construction fix DONE + merged (88525bf3b): the atlas chart is
`geoChartMapNorm (fun _ => id) = (β∘S)∘id`, exceptional divisor on the `divBirthCoord` diagonal. All
det atoms + the S primitive + the per-edge diagonal wrapper are banked (sorry-free, axiom-clean). The
LOCKED TARGET (statement-untouchable) is `geoAtlas_fold_det` (`GeoLeafJacobian.lean`), one tracked
frontier sorry = the regrouping cocycle. t14's job: fill that sorry.

**(i) INDUCTION SHAPE (the regrouping cocycle).** Do NOT use structural-on-`t` OUTERMOST with a
subtree-relative ledger — the cert (correction 1) refuted it (case-1's `mergeIdx` is born OUTSIDE the
subtree, so a subtree ledger can't carry its inheritance). Use the **relative-Jacobian cocycle, threaded
`L`, INNERMOST-first** (cert §2): `|det D(Φ' ∘ B)| w = L(B w) · |det DB| w`. Concrete route:
1. **Bridge** `c.chartMap` (baked in `geoAtlas` = `leaves (tGeo id t)`) to a `foldr (·∘·) id` LIST of the
   path's `geoChartMapNorm` charts. `tGeo_coherence` (already in `GeoChart`) gives `c.chartMap =` its
   `leafPaths id` composite; you then need a `leafPaths`-composite → `foldr`-list bridge (likely a small
   new helper — the composite is `acc ∘ localSub ∘ …`, and `localSub = geoChartMapNorm (fun _=>id) ⟨…⟩`).
2. `|det D(c.chartMap) w| = foldrCompAbsDet (pathCharts) w` via **`abs_det_fderiv_foldr_comp`** (needs each
   path chart `Differentiable ℝ` — prove `geoChartMapNorm_differentiable`: on-cone `β∘S∘id` diff via
   `geoChartMap_differentiable` + `flatSwapCLE_differentiable` + `Differentiable.comp`; off-cone `id`).
3. Each factor = `|z_{diagTargetOf}(intermediate)|^{dCN−1}` via **`geoChartMap_swap_fderiv_det`** (on-cone)
   / `= 1` (off-cone `id`-passthrough, `abs`/`fderiv_id`).
4. **Regroup** `foldrCompAbsDet` (intermediate-point diagonal factors) onto `∏_k |z_{c.divCoord k}(w)|^{c.divExp k−1}`
   by the cocycle threading `L` (birth/merge/split, below). The `acc`-generalized clause enters as: prove the
   cocycle for a general outer prefix `Φ'` (its ledger monomial `L`), the headline is `Φ' = id` (`L = 1` at
   `conRoot`) — this is where t10's rollover `id`-passthrough (forwards `acc`) is absorbed (`id` factor = 1).

**(ii) DEAD-ENDS / notes from the locking pass.** I only locked the STATEMENT (no regrouping attempt), so
no tactic dead-ends there — but two REFUTED design turns to avoid: (a) the subtree-relative `pieceLedger`
motive (§ correction 1); (b) per-pivot `divCoord`/`divExp` (finding-3, DISSOLVED by fork-15 — do NOT
reintroduce it; the STATE-LEVEL ledger `c.divCoord`/`c.divExp` from `leafOfState` is correct now). KEY
missing sub-lemmas you'll need: (α) `geoChartMapNorm`'s **§0 chart-action** (how it moves flat coords) —
compose `geoChartMap`'s action (`z_π(βy)=z_π(y)`; `z_c(βy)=z_π(y)·z_c(y)` for other center cells;
spectators fixed) with `flatSwapCLE_apply_flat` (the S relabel) — this is the workhorse for step 4; (β) the
**coherence** `c.divCoord = diagonal = diagTargetOf`: `leafOfState.divCoord = birthFlatCoord(divBirthCoord)`
(`DivBirthReach`/`EngineConstruction:1796`) must equal `diagTargetOf`'s `flatCoordOf(a,b,b)` — a
`birthFlatCoord = flatCoordOf-diagonal` + `diagTargetOf = same` equality (on-cone via `DivBirthInv`
validity). The headline elaborated with NO timeout; the atoms are all fast.

**(iii) cert §1's THREE identities → Lean case split** (`match e.case`, `EngineDefs stepUpdate`):
- `StepCase.case2` ↔ cert (1) CLEAN: `z_diag(intermediate)=z_diag(w)` (terminal) ⟹ atom
  `|z_diag|^{resRows·resCols−1}` = new divisor's `divExp−1`. Atom: `geoChartMap_swap_fderiv_det`.
- `StepCase.case11` ↔ cert (3) RE-MERGE: `S = id` (pivot 0 = `mergeIdx` diagonal already), atom
  `|z_{mergeIdx diag}|^{runLen·resCols}` ADDS to `mergeIdx`'s exponent (`divExp += runLen·resCols`).
  Sum with `mergeIdx`'s birth/earlier atoms → `divExp(mergeIdx)−1`.
- `StepCase.case12` ↔ cert (2) INHERITED-THREADING (non-local): the node's own atom is only
  `|z_p|^{runLen·resCols}`; the inherited `divExp(mergeIdx)−1` comes via the **`L(B w)` pullback** (B scales
  `z_μ ↦ z_p·z_μ`, so the ancestor `mergeIdx` birth atom, read after B, spawns `z_p^{divExp(mergeIdx)−1}`).
  THIS is why the cocycle must thread `L` (not per-node-local) — do not try to close case-1(2) with the
  node's own atom alone.
Each identity's substitution `z_{diagTargetOf}(B w) = <source monomial>` is a consequence of sub-lemma
(α) above (the §0 chart-action), no analytic content beyond the substitution algebra (cert §1 (R)).

**(iv) STAGED-MODULE WIRING (when the sorry closes).** `GeoLeafJacobian.lean` is NOT in the `DLNFibre.lean`
aggregator (staged). On discharge: the assembly batch (coverage / #34) adds `import …Engine.GeoLeafJacobian`
to the aggregator and consumes `geoAtlas_fold_det` in the per-piece `LeafJacobian` discharge (`∀ c ∈ atlas,
LeafJacobian c`), wrapping the β-det with the ψ=id boilerplate (`β := c.chartMap`, `ψ = ψsymm = id`,
`Dψ = ContinuousLinearMap.id`, `|det Dψ| = 1`, `lo = hi = 1`); add `geoAtlas_fold_det` to `AxCheck` once
load-bearing (forced `#print axioms`). The **α gauge** (LeafPullback, fresh loss-seat) fills
`geoChartMapNorm`'s gauge slot by changing `fun _ => id` in `fannedEdges` to the α family — a LOCALIZED
`fannedEdges` edit, no `geoChartMapNorm` redefinition; `resRank = 0` (`leaves_resRank_zero`) makes the
`resCoord`-coherence obligation vacuous.

*t11 stands down here. Seat stays addressable for one question if t14 needs it.*

## §t14 — STATEMENT CORRECTION: the locked binder was `(s)`, honest scope is `conRoot` (2026-07-19)

**What drifted.** The locked Lean headline read `geoAtlas_fold_det (s : ConState L) (c ∈ geoAtlas
(buildTree M (conOracle M) s)) …`, quantifying over a GENERIC `s` with no hypothesis. That form is
FALSE — exactly the class finding-1 predicted (lines 8-27). The design had `conRoot` EVERYWHERE (finding-1's
adjudication, lines 23-27; this file's own scope; the docstring's line 9); only the Lean binder drifted to
`(s)`. Caught by the check-provability-before-grinding pass (a named miss-class now: the design was right,
the transcription drifted past the gate + elder audit + the lock).

**The witness** (machine-checked, `GeoLeafJacobianDisproof.geoAtlas_fold_det_generic_false`, axiom-clean
`[propext, Classical.choice, Quot.sound]`). For any `M` with `0 < flatDim M` and `L ≥ 1`, take the terminal
state `s = csWitness L` (`layer = L`, so `L ≤ layer` ⟹ `oracleTerminal`; one divisor of exponent `2`,
all-zero profile ⟹ `t̃ = 0`, analytic). Then `buildTree = leaf (leafOfState M s)`, so
`geoAtlas = [{leafOfState M s with chartMap := id}]` — a single leaf with `chartMap = id`. Hence
LHS `= |det D id w| = 1`, while RHS `= |z_{divCoord 0}(w)|^{2−1}` vanishes at `w = 0` (`paramsEquivFlat`
is linear, `0 ↦ 0`). `1 ≠ 0`. The mechanism: a non-root `s` already carries divisors the fold-from-`s`
does not blow up (their birth charts are ABOVE `s`), but the leaf's `divExp` accumulates them — so the
per-`s` identity holds only at `numDiv = 0`, i.e. `conRoot`.

**Why the naive form cannot even be its own induction motive.** A WF induction on `s` (the `DivBirthReach`
template) visits terminal descendants as base cases; the real tree's leaves ARE terminal states with
`numDiv > 0` and `divExp ≥ 2`, so the base case is exactly the false terminal statement above. The true
motive is the acc + incoming-ledger-threaded cocycle (cert §2, standing counsel): true at terminal `s`
(the incoming ledger `L_s` is threaded; the born-below-`s` product is empty), and `conRoot` instantiates
it with `L = 1`, `acc = id`. This is precisely why that form was adopted over the subtree-relative motive.

**Resolution (team-lead ruling (A), no new elder gate — a transcription of an already-settled ruling).**
Headline specialized to `conRoot`; internal cocycle over generic `s` under `DivBirthInv`. The formalized
disproof is kept as an off-critical-path tripwire (`GeoLeafJacobianDisproof.lean`, nothing imports it).
