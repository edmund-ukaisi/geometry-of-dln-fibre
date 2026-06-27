# Statement card — R1 `routeStep` binding-coupled `diag(b)` anchors

Thread: `15-r1-routestep-diagb-anchors` (formalisation tide).
Branch: `expedition/r1-routestep-support-334` (off `expedition/aoyagi-full` @ `8026c80d`).
SHA to be pinned at integration (this thread does not commit).

---

## What this thread delivered

A reconciliation (task A) + three decidable fidelity anchors (task B) for the committed
`RouteStep` value-fold against the certified `diag(b)` resolution mechanism
(`theory/aoyagi-2023-reproduction/verify-r1-diagb-334.md`, `-4422.md`). The general dispatcher
(task C) stays the honest named `sorry` — the blocker is reported below, unchanged in count.

---

## Card 1 — the binding coupled witness `(3,3,4)`

> **Claim.** The committed `Mval`-anchored `RouteStep` value-fold computes the *certified-correct*
> core RLCT `4` for the reduced-width vector `M = (3,3,4)` — the genuinely-binding coupled `diag(b)`
> witness, where a per-row-multiplicity recursion gives the WRONG value `3`.

- **Lean:** `DLNFibre.DLN.RLCT.case334_routeStep_value`
  (`lean/DLNFibre/DLN/RLCT/Validate/Case334RouteStep.lean`)
- **Gloss.** Over the one-leaf family with codim-list `[9, 8]` (root stratum `T=(0,0)`, `Mval=9`,
  non-binding; achiever `T*=(1,0)`, `Mval=8=minAdm`, binding), the `⨅` of the `foldDivisors`
  monomial-thresholds is `½·minAdm = ½·8 = 4 = lambdaCore(3,3,4)`. Both codims carry a root-anchored
  `PivotWitness M334route` (`decide`-checked `T ∈ Adm M334route` and `codim = (Mval M334route T).toNat`).
  A genuine `RouteStep M334route M334route` BRANCH term is exhibited (`case334_routeStep_branch`).
- **Proved.** The value fold lands on `4` over the committed `PivotWitness`/`foldDivisors` machinery.
  The `(3,3,4)` `RouteStep.branch` is inhabited with genuine root-anchored data.
- **Assumed.** none beyond the committed `RouteStep`/`PivotWitness`/`foldFamily` interface.
- **Cited.** `monomial_rlct` (the S2 threshold interface — `monomialThreshold = ⨅ axisRatio`),
  the SAME axiom the existing `(2,2,2)`/`(3,2,3)` anchors use. `#print axioms` →
  `[propext, Classical.choice, Quot.sound, monomial_rlct]` — **no `sorryAx`, no `native_decide`.**
- **Deferred.** This is the VALUE-fold on a single binding leaf, NOT the general dispatcher's
  realizability that the chart path reaches the stratum (the named `sorry` in `routeStep`).
- **Status.** sorry-free + reviewed (thread reviewer, fidelity PASS on all 6 questions + decorrelated
  Codex; independent `#eval` of every `Mval`/`minAdm`; axiom set confirmed `sorryAx`-free).

## Card 2 — the non-binding contrast `(4,4,2,2)`

> **Claim.** For `M = (4,4,2,2)` the corank-2 `diag(b)` branch is present (`Mval=7`) but NON-binding;
> the value-fold lands on `2` via the CLEAN binder `t=(4,2,0)` (`Mval=4`), NOT `7/2`.

- **Lean:** `DLNFibre.DLN.RLCT.case4422_routeStep_value` (same file).
- **Gloss.** Over the family with codim-list `[7, 4]` (corank-2 cell `Mval=7` non-binding; clean
  binder `t=(4,2,0)` `Mval=4=minAdm`), the `⨅` is `½·4 = 2 = lambdaCore(4,4,2,2)`. The `min` correctly
  takes the clean binder. The corank-2 cell `T=(2,1,0)` is `decide`-checked admissible with `Mval=7`.
- **Proved / Cited / Status.** as Card 1 (`#print axioms` identical). **Deferred.** as Card 1.
- **Note.** This is the certificate's CORRECTION of the original brief (which targeted `7/2`):
  `(4,4,2,2)` must NOT be used as a binding `7/2` witness — used here correctly as the non-binding
  contrast to `(3,3,4)`.

## Card 3 — the deep-sharing `L=3` anchor `(3,3,5,4)`

> **Claim.** For `M = (3,3,5,4)` (`L=3`) the value-fold lands on `4` on a coupled minimiser
> `T=(1,1,0)` with an INTERIOR nonzero entry — NOT reducible to the `L=2` RRR closed form.

- **Lean:** `DLNFibre.DLN.RLCT.case3354_routeStep_value` (same file).
- **Gloss.** Over codim-list `[9, 8]` (root `Mval=9`; achiever `T*=(1,1,0)`, `Mval=8=minAdm`, the
  UNIQUE minimiser, interior partial drop `T₁=1>0`), the `⨅` is `½·8 = 4 = lambdaCore(3,3,5,4)`.
- **Proved / Cited / Deferred / Status.** as Card 1. Added in response to a decorrelated-Codex
  red-team ("11 spot-checks are evidence, not a theorem"; proposed this `L=3` deep-sharing case),
  and addresses the `(3,3,4)` certificate §6 "next construction" (the deep-factor sharing leg).

---

## The reconciliation (task A) — verdict

The certified spec says a **per-row multiplicity** datum loses the sharing identity
(`I_shared` rlct ½ vs `I_indep` rlct 1, same multiplicity) and a recursion built on it computes the
wrong value (`3` on `(3,3,4)`). **The committed `RouteStep` datum does NOT carry a per-row
multiplicity.** Its per-cell `codim : ℕ` is the GEOMETRIC `(Mval M₀ T).toNat` (the `PivotWitness M₀`
field), read from the CLOSED Aoyagi `Mval` form ROOT-anchored at the fixed `M₀` — NOT re-derived by a
row-wise resolution recursion. So:

- the value-fold reads `Mval M₀ T*` directly and is CORRECT on `(3,3,4)` (`= 4`, Card 1);
- the sharing identity is never re-derived per-row; it is encoded once, globally, in `Mval`;
- no-undershoot (`codim ≥ minAdm`) is AUTOMATIC: `minAdm = inf_{T∈Adm M₀} Mval M₀ T`, so any
  `PivotWitness M₀ c` gives `minAdm ≤ c` (`PivotWitness.minAdm_le`, `Finset.inf'_le`). A per-row-style
  error in the (unbuilt) dispatcher CANNOT undershoot the binding value — only over-emit non-binding
  cells, which the cover `≤`-leg catches.

**The committed `RouteStep` therefore does NOT need a `support : Gen → Finset DivVar` field.** The
spec's `support`+sharing field is the datum a *per-row resolution recursion* would need to compute the
RLCT correctly; the committed datum sidesteps that recursion entirely by reading the closed `Mval`.
Decorrelated-Codex confirmed (red-team, conclusion withheld): "sound as a value-fold claim; the residual
risk is the dishonest/incomplete dispatcher reachability, not per-row undershoot."

## The general dispatcher (task C) — the blocker, unchanged

`routeStep`'s general BRANCH arm is the named `sorry` (`RouteMRecursion.lean`). NOT fillable this thread
without fabrication:
- The realizability tie `#121-(ii)` IS proven (`CascadeAchiever`) and the achiever's binding
  `PivotWitness` IS constructible (`achieverPivotWitness`).
- The residual gap is the **general-M rank-pattern READ producer**: emitting, for arbitrary non-leaf
  `M`, the genuine multi-cell decomposition (`RouteMBranchRead M₀ M`) — the complement cover of
  non-binding cells + the proof the recursion's `routeAtlas` data folds to the right codims.
- A value-correct DEGENERATE fill (single achiever cell, empty complement) type-checks and folds to
  `½·minAdm`, but is the controller-ruled (2026-06-23) **trap-(iii) smuggle**: degenerate-as-cover +
  redundant-as-value. Explicitly forbidden; the genuine read is gated on the general-M `hnode` producer
  (#135), built there, not stubbed.

So the honest artifact is the named `sorry` + this precise blocker. The sorry count is UNCHANGED
(8 total, 1 `axiom`); this thread added zero sorries.
