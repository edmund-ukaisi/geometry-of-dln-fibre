# DIRECTED-EXACT GATE — the EXACT residual of Skeleton #44 at L = 2

Scratch gate `lean/DLNFibre/P44Gate.lean` (genm-p44c, NOT canonical, NOT in aggregator). Chains the
PROVEN `deepest_regular_core_normal_form_of` (DeepestL2Wiring:1047) — which routes through
`deepest_regular_core_reduces` → the gauge chart `deepest_gauge_chart_construct` (:996, clean-three at
L=2) — with the leaf hypotheses as explicit `sorry` stubs. The chain typechecks (build confirms; the
residual is EXACTLY the 4 leaves below). NO canonical edit.

## The residual set (MINIMAL) + classification

The Skeleton #44 conclusion at L=2 closes via TWO proven assemblers, leaving exactly FOUR leaves:

`deepest_regular_core_normal_form_of … hcore hGne` (the value-form, PROVEN body `rw[reduces, hcore]`),
whose `reduces` consumes the gauge chart built by `deepest_gauge_chart_construct … hJfront htop`
(hL2/hpos free at L=2).

| Leaf | What | Classification |
|---|---|---|
| **hcore** | R1 core-value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` | **R1 LANE — DEFER** (per controller; R1/detfderiv collision). Exists as `routeLayerAtlas_value_eq_lambdaCore` modulo the cited S2 axiom; in R1's flight. Do NOT dive. |
| **hGne** | reduced-core germ-nonvanishing: `dlnLoss M 0 ∘ flatSymm ≠ 0` a.e. near 0 | **BOUNDED, largely BANKED.** `DeepestCoreNonvanishing.dlnLoss_deepest_core_*` (∀ s, 1≤M s) is exactly this content; the primitive `RouteMSchurFiring.n_fintype` (`MvPolynomial p ≠ 0 ⟹ a.e. nonzero`) drives it. `dlnLoss M 0` is a nonzero polynomial (M widths ≥ 1 at the deepest interior, from hpos ⟹ M s = H s − r ≥ 1). Bounded measure-theory, NOT a wall. |
| **hJfront** | front-pivot col-alignment (`#100`): the chosen frame pivot embeds as `frontEmbed` | **BANKED via B·Π WLOG transfer** (NOT free-direct). `HeadlineRowColPermWLOG` supplies the row/col-perm WLOG (`hBpr_rank`/`hBpr_top`); `FrontPivotRowWLOG`/`DeepestPivotFrame`/`FrontPivotProducer` produce the front-pivot. The caller applies the perm to `B` first (the b-wlog-spec) — so it's a WIRING (perm-transfer) task, not new math. |
| **htop** | row-alignment (`#154`): the top-`r` row submatrix of `B` has rank `r` | **BANKED via the SAME B·Π WLOG transfer.** Dual of hJfront; `HeadlineRowColPermWLOG`'s `hBpr_top` is exactly this shape. Wiring (perm-transfer), not new math. |

## Verdict (the genuinely-live question, answered exactly)

#44 at L=2 does NOT need the shelved gauge core-comparability (my earlier stale-docstring read) — the
L=2 gauge chart is clean-three (`deepest_gauge_construction_L2`). The EXACT residual is:
- **1 deferred** (hcore — R1's lane, by controller instruction).
- **1 bounded measure-theory** (hGne — banked in `DeepestCoreNonvanishing` + the MvPolynomial primitive).
- **2 WLOG-transfer wirings** (hJfront/htop — banked in `HeadlineRowColPermWLOG` + the front/row-pivot
  producers; the caller threads the B·Π perm).

So #44@L2 is **WIRING-BOUNDED**, not a research wall: 3 of 4 leaves are banked/bounded; the 4th (hcore)
is R1's in-flight lane. The non-R1 residual = {hGne, hJfront, htop} = a measure-theory leaf + two
perm-transfer wirings. Route the R1 value (hcore) separately to avoid the detfderiv collision; the other
three are closeable here (or by whoever owns the L2-Skeleton wiring) without new math.

Artefacts: `lean/DLNFibre/P44Gate.lean` (the gate, 4 sorry stubs).
