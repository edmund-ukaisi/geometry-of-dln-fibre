# corank-3 design — the recursion's first real firing, with the threshold trap caught (2026-06-28)

**Context.** O1/O2 cleared by the controller's decorrelation (`n4-o2-adjudicate`: O2 HOLDS via pure
translation Jac≡1; O1 a build cost). The corank-2 weld (`core_schur2_lt_top`) is the validated base case.
Charge: the corank-3 instance — the recursion's FIRST real firing (Sc becomes 2×2, NOT a scalar).

## THE THRESHOLD (the load-bearing knowing-decision — Codex hit the undershoot trap)

Codex (xhigh) answered "corank-3 inner threshold c' < 2, reuse `schurInner_S_le` verbatim." **WRONG —
the undershoot trap.** Codex reused my r=2-HARDCODED lemmas (`schurInner_S_le`/`schurSplitD_lintegral_lt_top`
are Fin-4-Morse, threshold 2) for the corank-3 leaf. The cert is ground truth:
**λ_{3,4} = 4** (not 2) — the (3,3,4) cell is `‖T‖²(rlct 2) ⊕ ‖Δ·S‖²(λ_{2,4}=2)` = 4 = ½·minAdm(3,3,4).
The corank-3 target threshold is **c' < 4**, via the SHIFTED-EXPONENT Morse peel (NOT the threshold-2
verbatim reuse).

## THE corank-3 MECHANISM (c' < 4, matches "keep both blocks")

Target: `∫_{R∈matBox 3 3 T} ∫_{S∈matBox 3 4 T} ‖R·S‖_F^{−2c'} < ⊤` for `0 < c' < 4 = λ_{3,4}`.
1. **Radial blow-up**: cover R by the 9 entry-charts (`recStep`/`argmaxCellOn` on `Fin 9`), radial
   `Δ = a·R`, Jac `|a|⁸` (`pivotBlowupOnDeriv_det`, card 9 → 8); a-axis threshold `r²/2 = 9/2`.
2. **N2b j=1 split** (general-r, PROVED): `‖R·S‖² ≳ ‖(R·S)_row0‖²(Morse, p entries) + ‖Sc·S_bot‖²`, Sc
   now **2×2** (corank-2 — the recursion's first non-scalar residual), S_bot = rows 1,2 of S (a 2×p block).
3. **Shifted-exponent Morse peel** (the existing `radial_morse_residual_power_le`/`core_T_peel_le`,
   `RadialResidualPower`): peel the top block `‖(R·S)_row0‖²` (Morse, threshold (jp)/2 = ... the spectator
   T block, threshold 2 for (3,3,4)), leaving the corank-2 residual at the SHIFTED exponent `c' − 2`.
4. **Close the residual** `∫_Δ ∫_{S_bot} frobSq(Δ·S_bot)^{−(c'−2)}` by `core_schur2_lt_top` (my closed
   corank-2 lemma, needs `c'−2 < 2`) ⟹ **c' < 4**. The translation-domination (`M22 ↦ Sc`, Jac≡1, via
   `lintegral_translate_le_local` + `rowShear_entry_le_one`) confines Sc to the fixed box first.

So corank-3 BOTTOMS OUT in `core_schur2_lt_top` (no fresh general-r induction yet) — but the leaf is
`core_schur2_lt_top` AT THE SHIFTED EXPONENT `c'−2`, NOT `schurInner_S_le` at threshold 2.

## Genuinely-new pieces (vs corank-2)
- The JOINT-core SHIFTED peel (corank-2 had both blocks Morse → both leaves; corank-3 has a Morse top +
  a corank-2 residual → peel top, recurse-via-core_schur2 the residual at the shifted exponent).
- The 9-chart outer cover (mirrors the corank-2 4-chart `matBox2_*`; mechanical mirror, threshold-agnostic).
- The shifted-exponent atom `radial_morse_residual_power_le` (in `RadialResidualPower`/`RouteM334Hfin`,
  not yet in my module's closure — import or copy).

## Status
Design sharp + cert-grounded (threshold 4, Codex's 2 rejected). Surfaced the threshold knowing-decision to
the controller before sinking the ~350-line build. The corank-2 base case stands closed/reviewed/integrated.
Building corank-3 with the c'<4 target pending the controller's threshold confirmation (or proceeding if
no objection — the cert λ-values are unambiguous).
