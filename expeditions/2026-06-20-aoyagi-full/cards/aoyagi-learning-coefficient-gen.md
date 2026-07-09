# Statement card — ★ the FULLY-GENERAL headline `aoyagi_learning_coefficient_gen`

**Status:** EXPEDITION CAPSTONE. Proven in honest Lean 4 + Mathlib, **sorry-free, clean-three**,
**conditional on a single hypothesis `hRValue`** (= the R1-LOWER resolution value at the reduced
widths, the operator gate #72). Integrated in canonical `expedition/aoyagi-full @4687aed6`
(cosmetic longline fix `@e3d68e32`). Triple-verified (see below).

## The result
`lean/DLNFibre/DLN/RLCT/Validate/HeadlineGenAssembly.lean`:

```
theorem aoyagi_learning_coefficient_gen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hpos : ∀ s, r < H s)
    (hRValue :
      rlctAtOn (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r) 0 A) (fun _ => 0)
        = ENNReal.ofReal (lambdaCore (fun s => H s - r))) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)
```

The global infimum of the local RLCT of the square-Frobenius DLN loss over the optimal set (the
fibre `mult⁻¹(B)`) equals Aoyagi's closed form `aoyagiLambda H r` — the geometric learning
coefficient / `½·codim` content — for **general depth `L ≥ 2`, any rank `r`, nondegenerate widths
`r < H s`, and any target `B` of rank `r`**.

## Scope (exactly what is claimed)
- **General `L ≥ 2`** (`hL2`), any `r`, `B.rank = r`, **nondegenerate reduced widths** `r < H s`
  (`hpos`, i.e. `0 < M_s = H_s − r` at every layer incl. endpoints — refines the paper's non-strict
  realisability `r ≤ min H`; excludes the `prod ≡ 0` degeneracy the combinatorial `lambdaCore`
  cannot see).
- WLOG-transported from an arbitrary rank-`r` `B` to a front-pivot `B'` via
  `headline_frontRowColPivot_exists` (the ⨅ is invariant; `aoyagiLambda` is `B`-free).
- Produces the codim/`lambdaCore` **geometry**. The Aoyagi `rlct = ½·codim` equality itself is a
  SEPARATE Cited interface elsewhere (`RlctInterface.cited_aoyagi_dln`); this theorem does NOT cite
  it (no `cited_aoyagi_dln` in its axiom closure).

## The single open input — `hRValue` = the #72 gate
`hRValue` is the reduced-core RLCT value: `rlctAtOn(dlnLoss (H−r) 0)@origin = ofReal(lambdaCore (H−r))`.
This is EXACTLY the general-`L` R1-LOWER resolution value at `M = H−r` (the same value-statement the
L=2 assembly discharged via `r1_resolution_interface_L2_generic`). At general `L` it is **#72** — the
sub-generic `addlongest` wall (discuss-at-close #72, operator build-vs-cite). When #72 lands, `hRValue`
is discharged and the headline is **unconditional**.

## Proof architecture (all dependencies PROVEN clean-three unless noted)
1. **WLOG** `headline_frontRowColPivot_exists` → front-pivot `B'` + `htop`/`hcolfront` + ⨅-invariance.
2. **D1 ≥-leg** (⨅ = `rlctAt(deepestPoint)`, via `le_antisymm`): the sorry-free explicit-Schur chart
   `d1ge_hAtV_explicit_close_gen` (germ `schur_loss_germ_gen_at_pivot` + seam
   `schurReadout_germ_eq_gen` + residual `qResidGen`/`qResid_slice_value_gen` →
   `d1ge_hAtV_of_qResid_chart_genL`) + `deepest_regular_core_reduces_frontPivot_front` for hDeepest.
   **Cleaner than L=2** (whose D1 crux `d1ge_L2_hAtV_explicit` is still `sorryAx`).
3. **D1 "=" side / value:** `aoyagi_learning_coefficient_frontPivot_front` — the hcolfront-based
   hJfront-FREE front normal form (`deepest_regular_core_reduces_frontPivot_front`, built on the
   statement-preserving refactor `deepest_gauge_construction_ofBundle`; **#120 CLOSED** — the L≥3
   gauge diffeo is clean-three ∀L) fed `hRValue`, ▸ the PROVEN arithmetic recombination
   `reg_shift_add_core_eq_aoyagiLambda`.

## Verification (triple)
- Forced `#print axioms aoyagi_learning_coefficient_gen` = `[propext, Classical.choice, Quot.sound]`
  — **no `sorryAx`, no `monomial_rlct`, no `cited_aoyagi_dln`** (`hRValue` is a hypothesis, not an
  axiom). Full-aggregate green-gate 8793 jobs (the load-bearing `DeepestL2Wiring` refactor broke no
  consumer). AxCheck entries wired.
- geleg8's decorrelated **fidelity reviewer: FAITHFUL** (5 checks — fidelity-vs-`_L2` byte-identical
  conclusion + intended-only divergences; `hRValue` = exactly #72, not circular/stronger; NON-VACUOUS
  witness `H=(3,3,3), r=1`, `hRValue` at `(2,2,2)` provable via `case222`; axioms clean re-verified
  fresh; soundness — `le_antisymm` directions + `m = nRegGen H r` defeq-match). Codex-concurred.
- Controller decorrelated fidelity/vacuity check: PASS.

## Kill-condition
Dies if `hRValue` is NOT the genuine reduced-core RLCT value (checked: it is the exact value-statement
the L2 assembly used at `M = H−r`; the `(3,3,3)/r=1` witness confirms the whole hypothesis set is
satisfiable, so no laundered/vacuous hypothesis — the failure mode that bit the earlier `.choose`
`hJfront`). Also dies if `aoyagiLambda`/`lambdaCore` mis-encode the paper's closed forms (established
when A1 `lambdaCore_eq_clean` was built).

## What finishes the expedition
**#72 alone.** Discharging `hRValue` at general `L` (operator picks: (A) build `addlongest`, or (B)
cite it) makes `aoyagi_learning_coefficient_gen` unconditional — completing the from-scratch
cite-only-S2 mission (or cite-S2+`addlongest` under (B)). L=2 (`aoyagi_learning_coefficient_L2`) is
already unconditional (its R1 is done).

## Naming (report-only, operator — ties to discuss-at-close #73/#74)
`aoyagi_learning_coefficient_gen` is an honest conditional node (`hRValue` explicit + docstring
co-locates the gate). A scope-tagged name for conditional assembly nodes is a taste-call deferred to
the operator + a consolidation pass; not renamed mid-flight.
