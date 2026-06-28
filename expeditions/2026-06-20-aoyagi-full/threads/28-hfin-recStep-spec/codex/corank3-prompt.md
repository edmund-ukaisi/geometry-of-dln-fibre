# Design: corank-3 JOINT-core finiteness via the translation-domination recursion (Lean 4)

I have CLOSED the corank-2 case and need the cleanest corank-3 target (the recursion's FIRST real firing)
before sinking a build. The controller corrected my earlier framing: the recursion is translation-
domination, NOT a R→Sc change of variables. Confirm the cleanest Lean shape + flag any residual gap.

## CLOSED base case
`core_schur2_lt_top : ∫_{R∈[-T,T]^{2×2}} ∫_{S∈[-T,T]^{2×p}} ‖R·S‖_F^{-2c'} < ⊤` for `0<c'<2`. (My file
proves p=4; the proof is p-generic modulo the Morse-dimension = p threshold.)

## The corrected recursion (controller + minorpivot-cert)
Hold R, N2b-sandwich, Fubini over S, recurse on S_bot. The IH CARRIER is the JOINT free-box corank-m core:
  Jcore(m) := ∫_{C∈[-T,T]^{m×m}} ∫_{V∈[-T,T]^{m×p}} (‖W‖² + ‖C·V‖²)^{-c'}   -- W a FREE Fin(jp) Morse block
Keep BOTH blocks (the Morse top ‖W‖² AND the residual ‖C·V‖²); recurse on the JOINT core, not C alone.
The binding threshold is jp/2 + λ_{m,p}; dropping the core (as corank-2 did, scalar non-binding) silently
undershoots at corank ≥ 3.

The Sc-core outer-R domination: at fixed spectators, `M22 ↦ Sc = M22 − M21·M11⁻¹·M12` is a PURE
TRANSLATION (Jac ≡ 1) of the M22-block into the fixed box `[-2,2]^{(r-j)²}` (the shear `M21·M11⁻¹` has
entries ≤ 1 by the PROVED Cramer bound `rowShear_entry_le_one`, so |Sc entry − M22 entry| ≤ (r-j)·1·1·… ≤
bounded), giving spectator-uniform domination `∫_{M22∈box} f(Sc) ≤ ∫_{Sc∈bigbox} f` by the translate-
box-enlarge lemma (I have `lintegral_translate_le_local`).

## The corank-3 target (r=3, j=1 — the recursion FIRST fires, Sc is 2×2 NOT scalar)
`∫_{R∈[-T,T]^{3×3}} ∫_{S∈[-T,T]^{3×p}} ‖R·S‖^{-2c'} < ⊤` for c' < 9/2, via:
cover R by 9 entry-charts → radial blow-up (Jac |a|⁸, threshold 9/2) → N2b j=1 split
  ‖R·S‖² ≳ ‖(R·S)_row0‖²(Morse, p entries) + ‖Sc·S_bot‖²(Sc 2×2, S_bot 2×p)
→ the corank-2 residual `‖Sc·S_bot‖²` is dominated (translation Jac≡1) by a FREE 2×2 box → close by
`core_schur2_lt_top`.

## QUESTIONS
1. **Is corank-3 (j=1) really just: one N2b split + translation-dominate the 2×2 Sc-core + invoke
   core_schur2_lt_top?** I.e. does the corank-3 recursion BOTTOM OUT in my closed corank-2 lemma (depth 2,
   no further recursion), so I do NOT need a general-r induction yet — just this one concrete step?
2. **The JOINT-core subtlety at corank-3.** The controller says keep BOTH blocks and recurse on the JOINT
   core. But if I invoke `core_schur2_lt_top` for the residual `‖Sc·S_bot‖²` ALONE (the 2×2 core), and
   SEPARATELY the top Morse block ‖(R·S)_row0‖² (a clean Fin p Morse leaf, threshold p/2), are these two
   pieces DISJOINT in S (top reads S_row0, residual reads S_bot=rows 1,2) so they Tonelli-factor — and is
   the threshold then min(p/2-ish from the radial, ...) correct? Or does the JOINT-keep requirement mean I
   CANNOT split them and must integrate (‖W‖²+‖Sc·V‖²)^{-c'} jointly (the radial_morse_dominates pattern:
   Morse block + nonneg core)? Which is it for corank-3, and does core_schur2_lt_top supply the right form?
3. **Threshold arithmetic at corank-3.** radial a-axis: c' < r²/2 = 9/2. The inner ‖R·S‖² (R angular,
   bounded): does it need c' < 9/2 too, or does the inner split give a LOWER inner threshold that binds?
   For (3,3,p) the controller's λ recursion gives λ_{3,p}; is the inner finiteness threshold ≥ 9/2 (so the
   a-axis 9/2 binds) or < 9/2 (so the inner binds and I need the full joint-core not just core_schur2)?
4. **Does the translation-domination (Jac≡1) genuinely make ∫_{M22∈box}‖Sc·S_bot‖^{-2c'} ≤
   ∫_{Sc∈bigbox}‖Sc·S_bot‖^{-2c'}?** The translate is `M22 ↦ M22 − (shear, fixed at fixed spectators)`;
   the shear depends on M11,M21,M12 (spectators), constant w.r.t. M22. So per-fixed-spectator it's a
   translation of M22 → Sc; box-enlarges to the shifted box. Confirm this is exactly
   lintegral_translate_le_local applied to the M22-block, and the bigbox radius (2T? (1+j)T?).

Be concrete + skeptical. Flag if corank-3 needs the FULL joint-core induction (not just core_schur2) — if
so, that's the real first milestone, not the "bottom out in corank-2" shortcut.
