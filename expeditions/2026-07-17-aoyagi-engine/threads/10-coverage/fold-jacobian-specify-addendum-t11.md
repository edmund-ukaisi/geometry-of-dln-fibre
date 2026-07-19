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
