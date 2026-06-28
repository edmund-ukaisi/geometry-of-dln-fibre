# Pre-stage: `resolution_charts` TOP layer (R1 core resolution) readiness

**Author:** genm-carving (read-only audit of `origin/genm-firing @ e2941aa1`).
**Question (team-lead):** once R1-UPPER hfin (`routeMCore_threshold_lt_top`) + R1-LOWER (box-divergence
atom) land, is `resolution_charts` (Skeleton:1234, a `sorry`) **ready-to-wire**, or does it need NEW
bricks (the way hfin needed `routeMCore_le_matBox`)?

## Verdict: **READY-TO-WIRE once {hfin atom, hdiv atom} land — NO new top-layer bricks.**

The value-reconstruction layer above the two atoms is **already built, sorry-free, generic ∀M**. The
ONLY opens between `resolution_charts` and rock are the same two analytic atoms the rest of the R1 work
already targets (R1-UPPER + R1-LOWER). `resolution_charts` is a thin wrapper over them.

## The dependency chain (DOWN from `resolution_charts`), each link verified read-only

`resolution_charts M hMid` (Skeleton:1234, `sorry`) — the R1 CORE form
`rlctAtOn(dlnLoss M 0) 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)` (an EQUALITY, the value-match; over
`dlnLoss M 0`, deepest point `0`).

reduces, by ONE sorry-free generic theorem, to building the cover:

1. **`resolution_charts_of_layerCover M (hcover : IsRouteMCover (routeMCore M) …)`**
   (RouteMLayerValue:162) — **sorry-free, generic ∀M**. Its body:
   `routeM_rlctAtOn_eq_iInf` (RouteMBridge:79, sorry-free generic: `IsRouteMCover F U … → rlctAtOn F 0
   = ⨅ monomialThreshold`) + `rlctAtOn_routeMCore_transport M` (the generic `dlnLoss M 0 ↔ routeMCore M`
   RLCT bridge, via `routeMCore_comp_paramsEquivFlat`, RouteMExtraction:94, generic ∀M). So
   **`resolution_charts` = `resolution_charts_of_layerCover` applied to `IsRouteMCover (routeMCore M)`** —
   a 1-line wire once the cover exists.

2. **`IsRouteMCover (routeMCore M) …`** ← **`routeMLayerCover_of_atoms M hfin hdiv`**
   (RouteMLayerCover:155) — **sorry-free generic assembler**. The 3 structural fields
   (`Fmeas`/`Uopen`/`Umem`) + RHS-positivity are supplied generically; it needs exactly TWO analytic
   atom hypotheses:
   - **`hfin`** = `∀ c', (∑leaf monomialIntegrand < ⊤) → (∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} < ⊤)`.
     This IS R1-UPPER. `routeMCore_threshold_lt_top` (the genm-n4 target) gives the conclusion from
     `c' < minAdm/2`; discharging `hfin` needs it + a small "leaf-sum-finite ⟹ `c' < minAdm/2`" step
     (monomial-threshold = leaf finiteness boundary; the `(2,2,2)` template `routeM222_cover_le` does
     exactly this M-specifically). **No new brick beyond R1-UPPER + that small premise-reduction.**
   - **`hdiv`** = `∀ c', (∃leaf threshold ≤ c') → ∀ε>0, ∫_{cubeBox ε} |routeMCore M|^{−c'} = ⊤`.
     This IS R1-LOWER. Discharged by `layerCover_hdiv` (RouteMLayerCoverGE:25, **wiring sorry-free**)
     from the atom `routeMCore_box_diverges_achiever` — the file's single `sorry` (RouteMLayerCoverGE),
     reduced M-agnostically (sorry-free) to "construct one `NodeAchieverChart M`"
     (`routeMCore_box_diverges_of_nodeChart`). Anchors built for `(4,4,2,2)` + one other.

## Template confirmation: the `(2,2,2)` anchor fires through this EXACT path (sorry-free)
`Case222RouteMValidation`: `isRouteMCover_222` (cover_le = hfin half, cover_ge_div = hdiv half) →
`routeM_rlctAtOn_eq_iInf` → transport → `case222_rlctAtOn_eq_routeM : rlctAtOn(dlnLoss H222 0) = 3/2`.
This is the generic chain instantiated — the engine demonstrably works end-to-end; the generic ∀M version
is the same wire with `routeMLayerCover_of_atoms` in place of the hand-built `isRouteMCover_222`.

## Sorry/gap inventory between `resolution_charts` and {hfin, hdiv}
| object | file | status |
|---|---|---|
| `resolution_charts` | Skeleton:1234 | `sorry` (the wrapper — closes via `resolution_charts_of_layerCover (routeMLayerCover_of_atoms hfin hdiv)`) |
| `resolution_charts_of_layerCover` | RouteMLayerValue:162 | **sorry-free, generic** |
| `routeM_rlctAtOn_eq_iInf` | RouteMBridge:79 | **sorry-free, generic** |
| `rlctAtOn_routeMCore_transport` / `routeMCore_comp_paramsEquivFlat` | RouteMExtraction:94 | **sorry-free, generic** |
| `routeMLayerCover_of_atoms` | RouteMLayerCover:155 | **sorry-free, generic** |
| `layerCover_hdiv` (hdiv wiring) | RouteMLayerCoverGE:25 | **sorry-free wiring** |
| `hfin` atom (= R1-UPPER) | (genm-n4: `routeMCore_threshold_lt_top` + premise-reduction) | open — commissioned |
| `hdiv` atom (= R1-LOWER) | `routeMCore_box_diverges_achiever` (RouteMLayerCoverGE) | open — `sorry`, reduced to "one NodeAchieverChart M" |

## Bottom line
**No second surprise at the top layer.** Unlike hfin (which needed the NEW `routeMCore_le_matBox`
brick), `resolution_charts` needs **zero new bricks** above the two atoms — the entire
cover→value→`resolution_charts` machinery is already sorry-free and generic. R1 closes when:
1. **hfin / R1-UPPER**: genm-n4's `routeMCore_le_matBox` + re-point `routeMCore_threshold_lt_top` at the
   `SchurCore`/`schurRecStep_four` chain (post-carve) + the small leaf-sum⟹minAdm premise-reduction.
2. **hdiv / R1-LOWER**: the generic `routeMCore_box_diverges_achiever` = "construct one `NodeAchieverChart
   M`" (the in-flight R1-LOWER work, Items #78/#142).
3. Then: `resolution_charts := resolution_charts_of_layerCover (routeMLayerCover_of_atoms hfin hdiv)`
   (a few-line wire) + drop the Skeleton `sorry`.

Verdict: **ready-to-wire once {R1-UPPER hfin, R1-LOWER hdiv} land; 0 new top-layer bricks.**
