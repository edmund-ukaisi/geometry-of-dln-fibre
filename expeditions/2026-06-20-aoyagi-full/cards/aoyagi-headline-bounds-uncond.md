# Statement card — the UNCONDITIONAL general-`L` headline bounds (b)+(c)

**Status:** sorry-free + **reviewed FAITHFUL**, **clean-three**, **UNCONDITIONAL** (no analytic gate).
Built on branch `genm-headlines` off `expedition/aoyagi-full @42b1b5e6`, committed `@8a2b5776`
(precision fix `@278eb936`). New module `lean/DLNFibre/DLN/RLCT/Validate/HeadlineGenBounds.lean`.
Decorrelated fidelity+soundness reviewer (with Codex xhigh on the `≤`-half extraction): VERDICT
FAITHFUL on all four results — hbox-free confirmed, non-vacuous, axioms force-recompiled clean-three;
its one report-only escalation (the stale `monomial_rlct` mis-attribution) is folded in above.

These are the two general-`L` headline results the gated equality `aoyagi_learning_coefficient_gen`
did NOT reach unconditionally: its sole open input `(□) = RouteMBoxThresholdFinite (H−r)` feeds only
the `≥` direction of the reduced-core RLCT value, so the `≤` direction — and everything that consumes
only it — needs no gate. The `≤` direction rides the proven-`∀L` achiever box-divergence, not the
box-finiteness.

---

## (c) — the deepest reduction (UNCONDITIONAL)

```
theorem aoyagi_deepest_reduction_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hpos : ∀ s, r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
      = (nRegGen H r : ℝ≥0∞) / 2
        + rlctAtOn (fun A : Params (fun s => H s - r) => dlnLoss (fun s => H s - r) 0 A) (fun _ => 0)
```
- **Lean:** `DLNFibre.DLN.RLCT.aoyagi_deepest_reduction_gen`
  (`lean/DLNFibre/DLN/RLCT/Validate/HeadlineGenBounds.lean` @ `8a2b5776`).
- **Gloss.** For general depth `L ≥ 2`, any rank `r`, nondegenerate widths `r < H_s`, and any target
  `B` of rank `r`: the global infimum over the optimal set (the fibre `mult⁻¹(B)`) of the local RLCT
  of the square-Frobenius DLN loss equals the regular gauge shift `nRegGen H r / 2`
  (`nRegGen H r = r·(H⁰ + Hᴸ − r)`, the count of nondegenerate gauge directions) **plus** the local
  RLCT of the reduced singular core `dlnLoss (H−r) 0` at the origin.
- **Proved.** The full equality, unconditionally. The depth-`L` learning-coefficient problem reduces
  (with no analytic gate) to computing ONE reduced-core local RLCT.
- **Assumed.** `hpos : r < H_s` (nondegenerate reduced widths, `0 < H_s − r` at every layer incl.
  endpoints — refines the paper's non-strict `r ≤ min H`; excludes the `prod ≡ 0` degeneracy the
  combinatorial `lambdaCore` cannot see); `hL2 : 2 ≤ L`; `hr`, `hL`, `hB` structural. Same
  nondegeneracy scope as `aoyagi_learning_coefficient_gen`.
- **Cited.** none in the axiom closure. Forced `#print axioms` = `[propext, Classical.choice,
  Quot.sound]` — no `sorryAx`, no `monomial_rlct`, no `cited_aoyagi_dln`.
- **Deferred.** none for THIS statement. The reduced-core `rlctAtOn (dlnLoss (H−r) 0) 0` is left as an
  explicit term — computing its VALUE (`= ofReal(lambdaCore (H−r))`) is the `(□)`-gated step, and is
  NOT part of this reduction (by design).
- **Route.** Same WLOG → front-pivot `B'` (`headline_frontRowColPivot_exists`, ⨅-invariant) → D1
  `le_antisymm` fold as `aoyagi_learning_coefficient_gen`, stopping at the FRONT normal form
  `deepest_regular_core_reduces_frontPivot_front` (`hGne` from `hpos`) — the gauge-slice squeeze,
  which is `hbox`-free. (The general non-front `deepest_regular_core_normal_form`, Skeleton:1124, is
  sorried and unused.)

## (b) — the learning-coefficient upper bound (UNCONDITIONAL)

```
theorem aoyagi_learning_coefficient_gen_le (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hpos : ∀ s, r < H s) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) ≤ ENNReal.ofReal (aoyagiLambda H r)
```
- **Lean:** `DLNFibre.DLN.RLCT.aoyagi_learning_coefficient_gen_le`
  (`lean/DLNFibre/DLN/RLCT/Validate/HeadlineGenBounds.lean` @ `8a2b5776`).
- **Gloss.** Under the same hypotheses, the learning-coefficient infimum is AT MOST Aoyagi's closed
  form `aoyagiLambda H r`. This is the achievability / upper-bound direction: the deepest point of the
  fibre achieves a local RLCT no larger than Aoyagi's value.
- **Proved.** The inequality `⨅ … ≤ ofReal(aoyagiLambda H r)`, unconditionally.
- **Assumed.** Same nondegeneracy scope as (c).
- **Cited.** none. Forced `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- **Deferred.** The reverse inequality `≥` (hence the full EQUALITY `aoyagi_learning_coefficient_gen`)
  is what carries the box-finiteness gate `(□)`; (b) is exactly the half that needs no gate. Do NOT
  read (b) as the equality.
- **Route.** (c) gives `⨅ = nRegGen/2 + rlctAtOn(core) 0`; the reduced-core `≤`-half
  `r1_resolution_general_le` bounds `rlctAtOn(core) 0 ≤ ofReal(lambdaCore (H−r))`; the arithmetic
  recombination `reg_shift_add_core_eq_aoyagiLambda` reassembles `nRegGen/2 + ofReal(lambdaCore)` into
  `ofReal(aoyagiLambda H r)`. Closed with `add_le_add (le_refl _)` (the shift `nRegGen H r / 2` is
  defeq the recombination's raw `r·(…)/2`).

---

## The genuinely-new brick — the `hbox`-free `≤`-half

```
theorem routeM_rlctAtOn_le_iInf {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    (ι : Type) [Nonempty ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hge : ∀ c', (∃ i, monomialThreshold (d i) (k i) (h i) ≤ c') →
        ∀ Ω, IsOpen Ω → 0 ∈ Ω → ¬ IntegrableOn (fun x => |F x| ^ (-c') * 1) Ω volume) :
    rlctAtOn F 0 ≤ ⨅ i, monomialThreshold (d i) (k i) (h i)

theorem r1_resolution_general_le (M : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (hMid : ∀ s, 0 < M s) :
    rlctAtOn (fun A : Params M => dlnLoss M 0 A) (fun _ => 0) ≤ ENNReal.ofReal (lambdaCore M)
```
- **`routeM_rlctAtOn_le_iInf`** is the `≤` branch of `routeM_rlctAtOn_eq_iInf` (`RouteMBridge`) lifted
  out so it consumes the divergence field `cover_ge_div` ALONE — it needs neither the finiteness field
  `cover_le` (the half that carries `(□)`) nor the structural fields, and only `[Nonempty ι]` (drops
  `[Fintype ι]`). Same tactic script as that branch (`rlctAtOn_le_of_adm_le` +
  `exists_lt_of_ciInf_lt` + the divergence hypothesis) — a branch-lift of already-reviewed code, not
  new analysis.
- **`r1_resolution_general_le`** is the `≤` direction of `r1_resolution_general` with the
  box-finiteness `hbox` DROPPED: reconstruct the achiever box-divergence `hdiv`
  (`routeMCore_box_diverges_achiever_full'` through the guard-bridge — the same `hdiv` the equality
  builds, `hbox`-independent), convert to the `cover_ge_div` shape
  (`routeM_coverGeDiv_of_boxDiverges`), feed `routeM_rlctAtOn_le_iInf`, then transport to params and
  value the `⨅` at `ofReal(lambdaCore M)` (`routeLayerAtlas_value_eq_lambdaCore`).
- **The distinction from the gated equality is the DROPPED `(□)` hypothesis, NOT an axiom footprint.**
  Both these bounds AND the gated equality (`r1_resolution_general` / `aoyagi_learning_coefficient_gen`)
  are clean-three `[propext, Classical.choice, Quot.sound]` — force-recompiled verification, 2026-07-09
  (the `monomial_rlct` mentions in several upstream R1 docstrings, incl. `R1ResolutionGeneral.lean:50`,
  are STALE relics of the pre-S2-free footprint, not live proof terms; flagged to the controller for a
  docstring sweep). The genuine win of (b)/(c) is that they carry NO `RouteMBoxThresholdFinite`
  argument: the `≤`-lane uses only that box-divergence forces `rlctAtOn ≤ threshold` (measure theory)
  and the combinatorial `⨅ monomialThreshold = lambdaCore` (the QIP identity), whereas the equality's
  `≥`-lane needs the box-finiteness `(□)`.

## Kill-conditions
- (c) dies if the deepest-point decomposition is wrong (checked: `deepest_regular_core_reduces_…`
  is the gauge-slice squeeze, `#120` closed ∀L; `nRegGen = r·(H⁰+Hᴸ−r)` is defeq-matched).
- (b) dies if it secretly assumes `hbox`: verified — neither (b) nor `r1_resolution_general_le`
  carries a `RouteMBoxThresholdFinite` argument, and the clean axioms confirm no laundered gate.
- Both die if `aoyagiLambda`/`lambdaCore` mis-encode the paper's closed forms (established when A1
  `lambdaCore_eq_clean` was built).
- Non-vacuity: the same satisfiable scope as `aoyagi_learning_coefficient_gen` (witness `H=(3,3,3),
  r=1`); `hge` is genuinely supplied from `routeMCore_box_diverges_achiever_full'`, a non-vacuous ∀L
  theorem.

## Verification
Forced `#print axioms` (force-recompiled scratch) on all four —
`routeM_rlctAtOn_le_iInf`, `r1_resolution_general_le`, `aoyagi_deepest_reduction_gen`,
`aoyagi_learning_coefficient_gen_le` — each `[propext, Classical.choice, Quot.sound]`. No name clashes
with sibling modules. `HeadlineGenBounds` import-closure builds green. `aoyagi_learning_coefficient_L2`
re-confirmed clean-three (the full RRR equality, unconditional). Aggregator/AxCheck wiring is the
controller's (this module is not yet imported by `DLNFibre.lean`).
