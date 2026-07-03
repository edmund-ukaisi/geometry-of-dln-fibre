# genm-d1build: the D1 ≥-leg general-L targets are NOT leaf-closable — precise blocker map

Branch `genm-d1build` off canonical `origin/expedition/aoyagi-full` @e6fcd3cc. Baseline build GREEN
(`scripts/lb DLNFibre.DLN.RLCT.Skeleton`, 2671 jobs, exit 0; only style warnings). No code edited —
this hand is a verified-state report, not a close. Decorrelated Codex xhigh CONFIRMED the verdict
(`codex/route-{prompt,answer}.md`).

## VERDICT: both general-L Skeleton sorries are WALLED for a leaf executor; the brief's "consume banked pieces / bounded build" premise does NOT hold against the current Lean architecture.

The three D1 de-risk certs give a sound PEN-AND-PAPER verdict (the ≥-leg math is a bounded
finite-atlas + Thm4 argument, not Morse-Bott). But the CURRENT LEAN wiring realizes the OLD abstract
IFT/splitting route, which is (a) hard-walled at L≥3 and (b) gated on an open per-v producer with a
middle-stratum obstruction. Adopting the cert's finite-atlas route is a RE-ARCHITECTURE, not a fill —
above a leaf executor's remit. Grinding the existing route's #120 geometry is a research-level build.

## (a) `deepest_regular_core_normal_form` (Skeleton:1124, GENERAL L, hypothesis-free on L)

Proof chain that WOULD discharge it:
`deepest_regular_core_normal_form_of` (PROVEN, `DeepestL2Wiring:1116`)
  ⟸ `deepest_regular_core_reduces` (PROVEN modulo one sorry, `DeepestGaugeChart:524`)
  ⟸ `deepest_gauge_squeeze_exists` (BARE `sorry`, `DeepestGaugeChart:357`) — produces
     `Nonempty (DeepestGaugeChart H r B ...)`
  ⟸ `deepest_gauge_chart_construct` ⟸ `deepest_gauge_construction` (`DeepestL2Wiring:704`).
`deepest_gauge_construction` DISPATCHES on L: the `L < 3` arm is sorry-free but CONDITIONAL on
`hJfront` (front-pivot WLOG) + `htop` (row WLOG); the **`L ≥ 3` arm has 3 real geometry `sorry`s**
(`DeepestL2Wiring:913,916,1058` — the interior-frame-triviality / grouped-G0 diffeo, roadmapped #120).

Why NOT leaf-closable: the Skeleton statement has NO `L < 3` hypothesis, so it MUST cover L≥3 ⟹ it
cannot be discharged by the L=2-clean path. Reducing it to `assume Nonempty (DeepestGaugeChart …)`
would be **wall-laundering** (Codex trap: renaming the unresolved #120 wall as a hypothesis).

## (b) `rlctAt_deepest_le_of_optimal` (Skeleton:1172, GENERAL L, ∀ v ∈ optimalSet)

Banked skeleton: `deepest_le_of_optimal_via_L2_ge` (PROVEN, `DeepestMinRlct:227`) reduces it to (★)
`nReg/2 + coreV ≤ Lv` at v + the deepest equality + Thm4 core comparison (`deepest_le_of_homogeneous_core`,
PROVEN). The L=2 route (`deepest_le_of_optimal_of_chart_certificate`, `D1ChartProducerL2:271`) reduces
the per-point ≥-leg to a `GeneralVChartL2` certificate Γ at v — PROVEN GIVEN Γ. The open piece is
PRODUCING Γ at an arbitrary optimal v, which needs:
 - the IFT-chart geometry at v (bounded-unit local diffeo — the abstract splitting the cert says to
   avoid, but the Lean route still uses); AND
 - `hRform` (the residual germ-factorization), which is **PROVEN at deepest-type v** but **FALSE at a
   MIDDLE-STRATUM v** (`nReg_v > nReg`, e.g. (3,3,3)/r=1, A₁=diag(1,1,0), A₂=diag(1,0,0), nReg_v=7>5):
   the constant-nReg peel leaves a degree-2 Morse part with `det DΦ(0) ≠ 1`. `hCore` STILL HOLDS there
   (verified `rlctAtOn R 0 = coreDeepest` EXACT) but only via a Morse-with-parameters VALUE argument —
   an OPEN producer obligation (`D1ChartProducer.lean` "kill residual gap", surfaced to controller).

Codex (decorrelated, Q4): nReg-constancy + banked Thm4 alone do NOT deliver general-L (b); a pointwise
local normal-form bridge at v (= a splitting statement, Mathlib-lacking) is still required — the
finite-atlas route only supplies it CHARTWISE, i.e. a re-architecture, not a fill.

## Current axiom footprint (forced `#print axioms`, olean-forcing scratch)
`deepest_regular_core_normal_form` : [propext, sorryAx, Classical.choice, Quot.sound]
`rlctAt_deepest_le_of_optimal`     : [propext, sorryAx, Classical.choice, Quot.sound]
(both bare, as expected — these ARE the two Skeleton sorries.)

## Where the honest banked progress ALREADY sits (NOT this hand's work)
The L=2 headline `aoyagi_learning_coefficient_L2` (`HeadlineL2Assembly:78`) is ONE sorry from complete:
LEAF 1 (R1) is LANDED (`r1_resolution_interface_L2_generic`); the value side (a)-at-L2 is wired via
`deepest_regular_core_normal_form_L2_front` + WLOG + R1; the SOLE open leaf is LEAF 2 = the ∀-v D1
≥-leg slot at the front-pivoted B' (`HeadlineL2Assembly:107` sorry) — i.e. (b) at L=2, blocked by the
same middle-stratum per-v producer as above.

## Recommendation to controller (a scope decision, not a leaf task)
1. To move the HEADLINE: the highest-value open target is the L=2 ∀-v D1 ≥-leg producer (LEAF 2) —
   specifically the MIDDLE-STRATUM `hCore` VALUE discharge (`Morse-with-parameters`, the D1ChartProducer
   "kill residual") + the general-v IFT-chart producer Γ. This is a focused (large) tide, L=2-scoped.
2. To move GENERAL L: either commission the #120 L≥3 interior-frame geometry (3 sorries in
   DeepestL2Wiring), OR the cert's finite-atlas re-architecture — both are multi-tide, not a fill.
3. This hand did NOT edit Skeleton (single-writer) and banked no false progress. The two Skeleton
   sorries remain, correctly stated.
