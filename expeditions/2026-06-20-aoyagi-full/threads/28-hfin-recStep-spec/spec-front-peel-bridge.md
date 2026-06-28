# SPEC — the front-peel-bridge: `routeMLayerBoxIntegral M → SchurCore 4 r`

**Status:** DESIGN-ONLY (gated, not built). Diff-gate to controller before any build.
**Author:** genm-n4. **Decorrelated check:** Codex `xhigh` (`codex/genm-binding-p4-discharge-{prompt,answer}.md`).
**Numerics:** the real `minAdmRec` recursion + the `fibre_lintegral_mul_le` thresholds (Python, below).

The bridge that would discharge the named gap `RouteMBoxThresholdFinite M` (= `routeMLayerBoxIntegral M
c' 1 < ⊤` for `c' < ½·minAdm M`) for a family of `M`, by reducing the L-fold layer-product box integral
to the carve's `SchurCore 4 r`. This SPEC adjudicates the design, the coverage, and the build size.

---

## (i) The bridge DESIGN

`routeMLayerBoxIntegral M c' 1 = ∫_{A∈paramsBoxM M 1} frobSq(prod M A)^{−c'}`, where `prod M A =
A0·A1·…·A_{L-1}` (an L-fold product; `A_s : M_s × M_{s+1}`). Two stages.

### Stage 1 — the iterated-fibre FRONT-PEEL (the paper's method; BANKED engine)
The banked `fibre_lintegral_mul_le {p n q} : ∫_{X∈matBox p n T} frobSq(X·Y)^{−c'} ≤ fibreConst · frobSq
Y^{−c'}`, valid for `c' < p/2` (`p` = #rows of the peeled left factor `X`). Peeling `A0, A1, …` front
layers one at a time collapses `frobSq(A0·…·A_{L-1})` down to a residual two-matrix product
`frobSq(A_{L-2}·A_{L-1})`, each peel multiplying in a finite `Y`-independent `fibreConst`. This is exactly
the `(4,4,2,2)` route `triple_fibre_lt_top` (BANKED, sorry-free). **The peel imposes the threshold cap
`min_s (M_s / 2)` over the peeled layers** (the `min`, because every peel's `fibreConst` must be finite).

### Stage 2 — the rank-stratification to `SchurCore 4 r` (the carve's method; LANDED for r×r·r×4)
The residual two-matrix core `frobSq(A_{L-2}·A_{L-1})` over `matBox M_{L-2} M_{L-1} × matBox M_{L-1} M_L`
is `SchurCore p r` ONLY when it has the carve's shape: `A_{L-2}` square `r×r` (`M_{L-2}=M_{L-1}=r`) and
`A_{L-1}` the `r×p` free block (`M_L = p`). With the carve fixed at `p = 4`, this needs `M_{L-1}=M_{L-2}=r`
and `M_L = 4`. Then `SchurCore 4 r c' 1 < ⊤` for `c' < schurLambda r` (`schurGen_lt_top_modulo_recStep
schurRecStep_four r`). For a depth-2 `M = (r,r,4)` Stage 1 is EMPTY (`prod = A0·A1` already two-matrix),
and the bridge is the pure reshape `routeMLayerBoxIntegral (r,r,4) c' 1 = SchurCore 4 r c' 1`.

### The threshold reconciliation (the load-bearing arithmetic)
The overall reach is `min(stage-1 cap, stage-2 threshold) = min(min_{s peeled} M_s/2, schurLambda r)`. For
the gate to FIRE up to `½·minAdm M`, this must be `≥ ½·minAdm M`. **Two facts decide coverage:**
- **`minAdm(r,r,4) = 4r−4 = 2·schurLambda r`** (verified `t`-min of `(r-t)²+4t` over the real
  `minAdmRec`, exact r=0..7: `0,1,4,8,12,16,20,24`). So for `(r,r,4)` Stage 2 reaches EXACTLY `½·minAdm`,
  Stage 1 is empty — the gate fires perfectly.
- For L ≥ 3, `min_s M_s/2` UNDERSHOOTS `½·minAdm M` (worked cases below). The front-peel is strictly
  weaker than `½·minAdm` once any front layer must be peeled.

---

## (ii) WHICH M's it covers — the binding family

**Covered (gate fires to `½·minAdm`, BUILDABLE now gated on `schurRecStep_four`):** the depth-2 family
`M = (r,r,4)` for all `r`. Verified gate-fires-to-`½·minAdm` = True for (2,2,4),(3,3,4),(4,4,4),(5,5,4).
This GENERALISES the `(3,3,4)` anchor (`r=3`) to all `r`, plus subsumes `(2,2,4)`. It is exactly the
`SchurCore 4 r` shape — no front-peel, no shape massage.

**NOT covered — two independent obstructions (the research wall):**
1. **Depth-2 shape mismatch.** `M = (a,b,c)` with `(a,b,c) ≠ (r,r,4)` leaves `A0·A1` of shape
   `(a×b)(b×c)` — not square-Δ × `r×4`. E.g. `(3,4,4)`/`(4,3,4)` (`½minAdm=5`): the core isn't the carve
   shape; transposing a `p=4` need to a `p≠4` Schur shape the carve doesn't provide. `(r,r,c)` with `c≠4`
   needs `SchurCore c r` (a DIFFERENT carve, not built).
2. **Depth-`≥3` threshold undershoot.** Even when the TAIL is `(·,r,r,4)`, the front-peel cap `M_0/2`
   (and inner peels) undershoots `½·minAdm`. Worked: `(4,4,4,4)` reach `min(M_0/2, schurLambda 4) =
   min(2,6) = 2` vs `½minAdm = 5.5`; `(3,3,3,4)` reach `min(1.5,4)=1.5` vs `½minAdm=3.5`. The peel route
   gives only `min_s M_s/2`, the iterated-fibre's intrinsic ceiling — STRICTLY below `½·minAdm`.

**Why the undershoot is fundamental (not a proof gap):** the iterated-fibre bounds the codimension by the
SINGLE most-binding layer (`min_s M_s/2`), whereas `½·minAdm` is the FULL multi-layer codim of the
binding rank stratum (a SUM over the binding path, `Σ (M_s−t)(M_{s+1}−t)/2`). Reaching `½·minAdm` for
L≥3 requires the rank-stratified radial blow-up across ALL layers jointly — the carve's machinery
generalised from the 2-layer SchurCore to an L-layer joint resolution, which is genuine new geometry, NOT
the iterated-fibre.

---

## (iii) Bounded-build vs research-wall

| Target | Method | Status | Size |
|---|---|---|---|
| `(r,r,4)` ∀r | direct reshape + `SchurCore 4 r` | **BOUNDED BUILD** | ~150-220 lines |
| depth-2 `(r,r,p)` ∀p | needs `SchurCore p r` (general-p carve) | research (new carve) | the named ∀p gap |
| depth-`≥3` to `½·minAdm` | L-layer joint rank resolution | **RESEARCH WALL** | the genuine ∀M content |

**The `(r,r,4)` build (BOUNDED, the recommended deliverable):**
- `minAdm_rr4_eq (r) : (minAdm (![r,r,4]):ℝ)/2 = schurLambda r` — `minAdm = minAdmRec` (keystone), unfold
  to `inf'_{t≤r}((r-t)²+4t)`, `le_antisymm`: witness `t=r-2` (r≥2) for `≤`, `((r-t)-2)² ≥ 0` for `≥`;
  r=0,1 boundary by `decide`/direct. ~50-70 lines (the `inf'` computation is the only friction).
- `eParamsRR4 r : Params (![r,r,4]) ≃ᵐ (Fin r → Fin r → ℝ) × (Fin r → Fin 4 → ℝ)` — generalise
  `eParams334`'s `piFinSuccAbove`+`piUnique` reshape to arbitrary `r` (the widths are abstract `r`, the
  pattern is identical). ~40-60 lines.
- `routeMLayerBoxIntegral_rr4_eq (r c') : routeMLayerBoxIntegral (![r,r,4]) c' 1 = ∫_{Δ∈matBox r r 1}
  ∫_{S∈matBox r 4 1} frobSq(Δ·S)^{−c'}` — the reshape + `prod_two_layer334` (already generic over
  `M:Fin 3`) + Tonelli. Mirrors `routeMLayerBoxIntegral_M334_eq`. ~40-50 lines.
- `routeMBoxThresholdFinite_rr4_of_schurRecStep (hstep) (r) : RouteMBoxThresholdFinite (![r,r,4])` —
  the assembly: `c'<½·minAdm = schurLambda r` (via `minAdm_rr4_eq`) ⟹ `SchurCore 4 r c' 1` (via
  `schurGen_lt_top_modulo_recStep hstep r`) ⟹ the box integral `< ⊤` (via `routeMLayerBoxIntegral_rr4_eq`);
  `c'=0` volume bound. ~30-40 lines. Carries `hstep : SchurRecStep 4 schurLambda` as a hyp (discharges
  when the carve merges; `e06554c7` pending review).

Total `(r,r,4)` family: **~160-220 lines, all bricks banked** (the carve is the only gated input). The
iterated-fibre front-peel itself (Stage 1, for the BROADER non-`(r,r,4)` depth-2 / shape-matching tails)
is ALSO bounded-buildable (the `(4,4,2,2)` `triple_fibre_lt_top` is the template) — but it does NOT reach
`½·minAdm`, so it would discharge a WEAKER threshold gap, not `RouteMBoxThresholdFinite` as stated.

**The research wall is depth-`≥3` to `½·minAdm`** — the L-layer joint rank-stratified resolution. The
iterated-fibre is the paper's method and IS established/break-down-able, but its `min_s M_s/2` ceiling is
strictly below `½·minAdm`; closing the gap is the carve's radial-blow-up generalised across all layers
(a multi-tide expedition, not a bounded build).

---

## Recommendation

Build the **`(r,r,4)` family** discharge now (gated on `schurRecStep_four`) — the honest, bedrock,
non-vacuous generalisation of the M334 anchor to all `r`, with the threshold proven to match exactly.
Leave the broader binding family (depth-2 ∀p, depth-≥3 to `½·minAdm`) as the precisely-named open gap
`RouteMBoxThresholdFinite` for general `M`. Statement diff-gated:

```lean
theorem routeMBoxThresholdFinite_rr4_of_schurRecStep
    (hstep : SchurRecStep 4 schurLambda) (r : ℕ) :
    RouteMBoxThresholdFinite (![r, r, 4] : Fin 3 → ℕ)

theorem minAdm_rr4_eq (r : ℕ) : (minAdm (![r, r, 4] : Fin 3 → ℕ) : ℝ) / 2 = schurLambda r
```
