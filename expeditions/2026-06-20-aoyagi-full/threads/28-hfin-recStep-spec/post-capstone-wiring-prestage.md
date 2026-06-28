# Pre-stage: post-capstone R1-UPPER wiring readiness

**Author:** genm-carving (read-only audit of `origin/genm-firing @ e2941aa1`).
**Question (team-lead):** once `schurRatioResidGen_mid` closes, is the chain
`schurRatioResidGen_mid ⟹ schurRecStep_four ⟹ schurGen_lt_top_modulo_recStep ⟹ R1-UPPER capstone`
ready to flip green, or are there OTHER sorries/gaps ABOVE it?

## Verdict: **NOT ready-to-flip — 1 genuine gap + 1 trivial stub-swap.**

Closing `schurRatioResidGen_mid` makes `schurRecStep_four` and `∀r SchurCore 4 r c' T` green, but the
paper-level R1-UPPER headline `routeMCore_threshold_lt_top` carries its **own separate `sorry`** and is
**not yet wired** to the `SchurCore` chain. So R1-UPPER does NOT go green automatically on the carve close.

## The chain, link by link (read-only trace)

| link | file:line | status when carve closes |
|---|---|---|
| `schurRatioResidGen_mid` | RouteMSchurFiring:1403 (sorry @1425) | **the carve sorry** (genm-firing closing) |
| `schurRatioResidGen` (subcritical fold) | RouteMSchurFiring:1430 | green (consumes `_mid`) |
| `schur_matBoxG_chart_lt_top` | RouteMSchurFiring:1510 | green |
| `schurCoreGen_firing` | RouteMSchurFiring:1660 | green |
| `schurRecStep_four : SchurRecStep 4 schurLambda` | RouteMSchurFiring:1673 | green (dispatch r=0/1/2/≥3) |
| `core_schurGen_lt_top` (wrapper, takes `hstep` hyp) | RouteMSchurGeneral:115 | **already green, axiom-clean** |
| `schurGen_lt_top_modulo_recStep (hstep)` | RouteMSchurGeneral:236 | **already green** |

So within the Schur firing, the ONLY sorry below R1-UPPER is `schurRatioResidGen_mid`. The wrapper is
sorry-free and `hstep`-parametrised — feeding `schurRecStep_four` in gives the UNCONDITIONAL
`∀ r c' T, 0<c' → c'<schurLambda r → 0<T → SchurCore 4 r c' T`. **That application is not yet written
anywhere** (`schurRecStep_four` is referenced only in its own docstring) — a 1-line wire, trivial.

## Gap 1 (TRIVIAL — stub swap): `schurRecStep4_stub`
`RouteMSchurGeneral:144` has `theorem schurRecStep4_stub (lam) : SchurRecStep 4 lam := by sorry`.
It is **deliberately OUT of `core_schurGen_lt_top`'s dependency graph** (the wrapper takes `hstep` as a
hypothesis), so it gates nothing and keeps `#print axioms core_schurGen_lt_top` clean. Action at close:
delete the stub (or replace its uses, if any) by `schurRecStep_four`. Not a blocker.

## Gap 2 (GENUINE — the second sorry): `routeMCore_threshold_lt_top`
`RouteMSchur:426` —
```lean
theorem routeMCore_threshold_lt_top {L : ℕ} (M : Fin (L + 1) → ℕ) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤ := by
  sorry
```
This is the generic ∀M R1-UPPER headline (the analog of the **done** `routeMCore_M334_threshold_lt_top`
and `routeMCore_M4422_threshold_lt_top`). It is a **SKELETON with its own sorry** and its docstring still
describes the OLD corank-2 `schurSplit_*` (RouteMSchurDepth2) reduction route — it has **not** been
re-pointed at the new `SchurCore` / `schurRecStep_four` chain. It is the R1-UPPER terminal that the
Skeleton's `resolution_charts` (R1) rung ultimately needs (RouteMSchur docstring line 24).

**What Gap 2 needs (the missing bridge `SchurCore → routeMCore_threshold_lt_top`), reading off the
corank-3 template `routeMCore_M334_threshold_lt_top` (RouteM334Ratiofin:1033):**
1. `c' = 0`: volume bound (trivial — `routeMBaseNbhd ⊆ cubeBox 1`, compact, `measure_lt_top`). Copy
   verbatim from M334.
2. `0 < c'`: `routeMCore M le_matBox` (M-dependent: `routeMCore M = frobSq(A0·A1)` on the open box) then
   `lt_of_le_of_lt` the matBox finiteness.
   - **`routeMCore_le_matBox` GENERIC does NOT exist** — only `routeMCore_M334_le_matBox` (RouteM334Hfin:788).
     This M-shape-dependent reduction (routeMCore ↦ the two-matrix-box `frobSq`) is the **genuinely new
     brick** of Gap 2, independent of the carving. (It is the `routeMCore`-definition unfolding + the
     rank-stratified blow-up reframing, per the N4 docstring.)
   - the matBox finiteness = `SchurCore 4 r c' T` (after the radial-Δ flatten that
     `matBox334_blowup_lt_top` does for r=3) — THIS is what the carve close delivers generically via
     `schurGen_lt_top_modulo_recStep schurRecStep_four`. So half of step 2 is unblocked by the carve;
     the `routeMCore_le_matBox` half is the separate gap.

## Sorry tally on `origin/genm-firing` (the firing tree)
- RouteMSchurFiring: 1 (`schurRatioResidGen_mid` — the carve, closing).
- RouteMSchurGeneral: 1 (`schurRecStep4_stub` — out-of-graph, trivial swap).
- RouteMSchur: 1 (`routeMCore_threshold_lt_top` — **Gap 2, genuine**).
- RouteMSchurRecStep: 0. RouteMSchurDepth2: 0.

## Scope note: "R1-UPPER" = the R1 **hfin** (upper-bound finiteness) ladder
Per `RouteMSchur` top docstring, "R1-UPPER" is the rank-stratified R1 **hfin** ladder: the terminal
`routeMCore_threshold_lt_top` discharges the **`hfin` field of `routeMLayerCover_of_atoms`**
(RouteMLayerCover:155, the R1 `IsRouteMCover` assembler) — NOT the Skeleton's `resolution_charts`.
`resolution_charts` (Skeleton:1228, **also `sorry`** @1234) is the SEPARATE higher RLCT-=-monomialThreshold
layer (the full charts decomposition / payoff), downstream of and bigger than the hfin atom; it is not the
immediate carve target and is out of scope for "does the carve close R1-UPPER hfin". The carve + Gap 2
close the **hfin** atom; `resolution_charts` remains its own (larger) open layer.

## Ready-to-flip summary
- **Schur `∀r SchurCore` finiteness:** ready-to-flip the moment the carve closes (1-line wire of
  `schurRecStep_four` into `schurGen_lt_top_modulo_recStep`; drop the stub).
- **R1-UPPER headline `routeMCore_threshold_lt_top`:** **1 genuine gap** — needs the generic
  `routeMCore_le_matBox` (M-dependent routeMCore→frobSq-box reduction) + re-pointing the proof at the
  `SchurCore` chain. This is a separate, M-shape brick (the N4 "long pole" the docstring flags), NOT
  delivered by the carve. Recommend it be scoped as its own follow-up task now so it lands in parallel
  with / right after the carve close.

**Bottom line: the carve close unblocks the Schur half but R1-UPPER needs ONE more brick
(`routeMCore_le_matBox` generic) + the wire. Not auto-green; 1 gap.**
