# pivotDom_finiteness — (3,3,3) reconciliation-gate accounting (formaliser)

Anchor (3,3,3), L=0, u=2, a=b=1. uρ=6, ab=1, minAdm(redChain 2 M)=6, minAdm(M)=7.
LHS<∞ ⟺ c'<3.5=(uρ+ab)/2; pure-pivot (corank dropped) ⟺ c'<3=uρ/2. Gap = c'∈(3,3.5).

## Verdicts (mine, Codex-decorrelated: pivotfin-accounting-{prompt,answer}.md)
1. Pull-pivot-at-exponent-c' (my original step 3): **UNSOUND** in gap. Pivot normal-space dim uρ=6,
   ∫_0 r^{5-2c'}dr<∞ ⟺ c'<3 ⟹ C_ang=∞ for c'∈(3,3.5). Controller's correction confirmed. [Codex SOUND]
2. Threshold 3.5 needs the OUTER (z,A_cor) degeneracy: fixed-(z,A_cor) linear-image rank = M0·rank Q = 9
   (threshold 4.5), NOT uρ+ab=7. No fixed-outer linear codim delivers 7 ⟹ controller's (a) joint-D-B at
   codim uρ+ab is NOT realizable by a fixed-outer ‖linear‖² map; A_cor-free ⟹ bilinear (B₁₂·A_cor·Zf).
   [Codex SOUND]
3. EXPONENT EXTRACTION `RHS<∞ ⟹ c'<3.5`: **SOUND**. Restrict (A_cor,Γ) to {‖Γ·Q_b‖²≤decLoss};
   integrand ≥ (2decLoss)^{-c'}; corner sublevel-VOLUME lower bound μ{‖Γ·Q_b‖²≤D} ≳ D^{ab/2} via
   |Γ|≤√D/‖Q_b‖ (‖Q_b‖≤M compact; vanishing σ_max only ENLARGES the set — no lower σ needed);
   ⟹ RHS ≳ ∫_v v^{6-2c'} = ⊤ for c'≥3.5. [Codex SOUND; the ONE clean new sublemma]
4. Forward finiteness `c'<3.5 ⟹ LHS<∞` (the crux, bilinear RLCT): the "DROP" (pointwise + uniform C_abs)
   is **CONDITIONAL** — (i) absorbing C as au-codim gives threshold (uρ+au)/2; for b>u (au<ab) there is a
   FAILURE WINDOW (uρ+au)/2 < c' < (uρ+ab)/2 (Codex). FIX: handle C by S3's Ccross-UNIFORMITY (box-vol, NOT
   codim) ⟹ corank threshold = ab, window closes — BUT S3 needs the additive pivot term A_cor-free, which
   needs the pivot cross-term drop first (circular). (ii) uniform C_abs near degenerating Q_p,Q_b needs a
   SEPARATE angular/Jacobian ratio lemma (NOT from a.e. rank) [Codex].

## Bottom line
- Extraction half (3): sound, one moderate new sublemma (corner sublevel-vol lower bound). Covers the gap.
- Forward half (4): the genuine crux = the bilinear RLCT / pivot cross-term drop; D-B cannot shortcut it
  (verdict 2); the clean-const realization is only conditionally pinned. This is where a wall can hide.
