# corank-3: the EXACT inner statement (fixed-R vs R-integrated for the residual) — Lean design

I'm building the corank-3 finiteness and found a subtlety in the inner statement. Confirm the right shape.

## Established
- `core_schur2_lt_top : ∫_{Δ∈[-T,T]^{2×2}} ∫_{S∈[-T,T]^{2×4}} ‖Δ·S‖^{-2c'} < ⊤` for c'<2 (R AND S integrated).
- `schurInner_S_le (R fixed, R₀₀=1, |R i k|≤1) : ∫_{S∈[-T,T]^{2×4}} ‖R·S‖^{-2c'} < ⊤` for c'<2 — a
  FIXED-R, S-integrated bound. This worked at corank-2 because the N2b residual ‖Sc·S_bot‖² with Sc a
  1×1 SCALAR is a Morse block in S regardless of Sc's value (even Sc=0 leaves the top Morse block).
- corank-3 target (CONFIRMED): `∫_{Δ∈[-T,T]^{3×3}} ∫_{S∈[-T,T]^{3×4}} ‖Δ·S‖^{-2c'} < ⊤` for c' < 4 = λ_{3,4}.

## The subtlety I found
The corank-3 N2b (j=1) split: ‖R·S‖² ≳ ‖(R·S)_row0‖²(Morse, p=4) + ‖Sc·S_bot‖², Sc now 2×2, S_bot 2×4.
At FIXED angular R: ∫_S ‖R·S‖^{-2c'} — the top block gives only c'<2 (4-entry Morse); the residual
‖Sc·S_bot‖² needs Sc full-rank to add more, but Sc CAN be rank-deficient at fixed R. So a FIXED-R inner-S
lemma "∫_S < ⊤ for c'<4" is FALSE (fails when Sc degenerate). The c'<4 must come from INTEGRATING the
R-angular block too (the {Sc degenerate} sub-locus is handled by the residual's own corank-2 integration).

So unlike corank-2, the corank-3 residual after the split is NOT a fixed-R Morse leaf — it is the corank-2
JOINT ∫_Δ∫_S core (both integrated), = core_schur2_lt_top at the shifted exponent.

## The structure I think is correct (CONFIRM or fix)
The corank-3 cover decomposes the OUTER R (3×3) into radial × angular via the 9-chart blow-up. The inner
per-chart is `∫_{R-ang over bounded chart} ∫_S ‖R·S‖^{-2c'}` (R-angular INTEGRATED over the chart, NOT
fixed). Then:
1. N2b j=1 split + shifted-peel the top Morse block ‖(R·S)_row0‖² (threshold 2) → residual at exponent c'-2.
2. The residual `∫_{R-ang}∫_{S_bot} ‖Sc·S_bot‖^{-2(c'-2)}` — Sc varies with R-ang. Via the translation
   M22 ↦ Sc (Jac≡1, the M22-block of R-ang maps to Sc), this is dominated by the corank-2 JOINT
   `∫_{Sc∈box}∫_{S_bot∈box} ‖Sc·S_bot‖^{-2(c'-2)}` = core_schur2_lt_top at exponent c'-2 (needs c'-2<2).

## QUESTIONS
1. **Is the corank-3 inner per-chart genuinely `∫_{R-ang INTEGRATED}∫_S` (not fixed-R)?** I.e. the
   residual's R-angular block (the M22 part that becomes Sc) must be INTEGRATED for the c'<4 to hold,
   because at fixed R the residual threshold drops to 2 when Sc degenerates. Confirm the corank-3 cover
   does NOT factor through a fixed-R inner-S lemma (the way corank-2 did), but keeps R-ang integrated and
   feeds the residual to core_schur2_lt_top (R-and-S integrated). Yes/no + why.
2. **The shifted-peel ordering.** I peel the top Morse block ‖(R·S)_row0‖² FIRST (it depends on R-row0 +
   shear of R-other-rows, and S-row0). Does peeling it (via radial_morse_residual_power_le, the
   shifted-exponent atom, over the S-row0 Morse coords) leave a clean residual `‖Sc·S_bot‖^{-2(c'-2)}`
   that no longer involves S-row0 or R-row0 — so the residual is purely (R-other-rows = M21,M22) × S_bot,
   matching core_schur2's (Δ,S)? Or does the top-block peel entangle with the residual (shared R/S rows)?
3. **The cleanest Lean target.** Given (1), is the corank-3 headline best stated as the FULL
   `∫_{Δ∈box 3 3}∫_{S∈box 3 4} ‖Δ·S‖^{-2c'} < ⊤, c'<4` (mirror core_schur2's statement, one r up), with
   the proof = 9-chart cover → radial → N2b+shifted-peel → core_schur2 at c'-2? And is the per-chart inner
   the object `∫_{R-ang∈chart}∫_S` that I should NOT try to make a reusable fixed-R lemma for (since it's
   R-integrated)?
4. **Does the translation M22↦Sc need M22 to be a FREE block of R-ang?** R-ang on the chart has pivot
   entry=1, other entries ≤1 (the ratios). The M22 block (rows/cols 1,2 of R-ang, for the (0,0) pivot) —
   are these free coordinates of the chart (so the translation M22↦Sc is a CoV on free coords, Jac≡1) or
   are they constrained by the chart/pivot? (M11=R₀₀=the pivot=1 after radial; M21=R-rows-1,2-col-0,
   M12=R-row-0-cols-1,2, M22=R-rows-1,2-cols-1,2 — all ratios, free in [-1,1] except the pivot.)

Be concrete + skeptical. The key risk: whether the corank-3 residual genuinely reduces to core_schur2 via
the translation (needs M22 free + integrated), or whether the fixed-R-then-integrate ordering of corank-2
breaks at corank-3. Flag if I need a DIFFERENT inner statement than corank-2's.
