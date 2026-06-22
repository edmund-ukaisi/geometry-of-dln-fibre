<task>
Lean/Mathlib RLCT proof for deep linear networks. A SHARP cert-fidelity question I must settle before
transcribing a Lean structure — is the "gauge-normalized core" PER-LAYER or the FULL product Schur
complement? They DISAGREE on a known counterexample. I need the truth-value + the right object.

SETUP. L layers, each gauge-sliced C_s = [[I_r+X_s, Y_s],[Z_s, T_s]] (deviation blocks, T_s the reduced
(H_s−r)×(H_{s+1}−r) block). The square-Frobenius loss near the deepest point = ‖∏C_s − blockdiag[I_r,0]‖²
= ∑E² + ‖P11‖², where E = the product's (0,0)-I,(0,1),(1,0) blocks (regular residuals) and P11 = the
product's (1,1) block.

TWO candidate "gauge-normalized cores":
 (A) PER-LAYER: T̃_s = T_s·(I − V_s Y_s)⁻¹ per layer, core = ‖∏_s T̃_s‖². (V_s,Y_s the per-layer gauge blocks.)
 (B) FULL PRODUCT SCHUR: R = P11 − P10·(P00)⁻¹·P01 (P00,P01,P10,P11 the product's blocks), core = ‖R‖².

THE COUNTEREXAMPLE (exact, verified). L=3, r=1, H=(2,2,2,2): C1=[[1,0],[−ε²,ε]], C2=[[1,ε],[ε,0]],
C3=[[1,−ε²],[0,ε]]. Then C1C2C3 = blockdiag[1, −ε⁴], so ∑E²=0, P11=−ε⁴, loss=ε⁸.
 - (A) per-layer: raw T_s = (ε, 0, ε) [the (1,1) entries], so ∏T̃_s = ε·0·ε·(units) = 0. core_A = 0.
 - (B) full Schur: P10=P01=0 here (∑E²=0), so R = P11 = −ε⁴, core_B = ε⁸ = loss. ✓
So (A) gives Φ = ∑E²+core_A = 0 ≠ loss=ε⁸ (squeeze FALSE); (B) gives Φ = ε⁸ = loss (squeeze holds at this pt).

THE TENSION with the FINAL RLCT split. The downstream step is rlct_additive_smooth_block:
rlctAtOn(∑reg² + G(core)²) = nReg/2 + rlctAtOn(G²) — it REQUIRES the core G to depend on the CORE
coords ALONE (a clean product (Fin nReg → ℝ) × CoreSpace). But the full Schur R = P11 − P10·P00⁻¹·P01
DEPENDS on the regular residuals P10,P01 — so ‖R‖² is NOT a function of the core slot alone (off the
{reg=0} locus). At the counterexample reg=0 so R=P11, but generically R mixes reg coords.
</task>

<output_contract>
Terse, decisive:
1. Which core is CORRECT for the squeeze-then-additive-split to be sound: (A) per-layer T̃, (B) full
   product Schur R, or (C) something else? One sentence why. (The counterexample kills (A) at one point;
   does (A) fail generically or just measure-zero?)
2. If (B): how is the rlct_additive_smooth_block "core depends on core-coords alone" requirement met,
   given R depends on the regular residuals P10,P01? Options: (b1) the dependence is a UNIT/bounded
   perturbation peeled like the leak (so the RLCT-relevant core is the {reg=0} restriction R|_{reg=0} =
   the per-layer-ish chain); (b2) a coordinate change makes R core-only; (b3) the squeeze is against
   ∑E² + ‖R‖² and the additive split is applied to a FURTHER-reduced object. Which, and is it sound?
3. THE RECONCILIATION: at reg=0, does R|_{reg=0} = the per-layer ∏T̃_s, or do they STILL differ? (If they
   agree on {reg=0}, then (A) is "right on the reduced locus" and the disagreement is only off-locus,
   charged to ∑E² — salvaging a per-layer-ish core. If they differ even on {reg=0}, (A) is just wrong.)
   Compute R|_{reg=0} vs ∏T̃_s for the counterexample and a generic small case.
4. The cleanest CORRECT object for the Lean "deepestCoreF (core coords)" that (i) matches the loss near
   the deepest point via a squeeze, AND (ii) is core-coords-only for the additive split. State it.
5. The most likely way I'm wrong about (A) being insufficient.
</output_contract>

<grounding_rules>
The block algebra + the counterexample are TRUSTED (verified exact). Reason about which core object is
correct and whether it's compatible with the additive split. Distinguish "fails at a measure-zero set"
(might be OK for RLCT, which is a germ/integral) from "fails on an open set" (genuinely wrong). If the
per-layer (A) fails only on a measure-zero set AND the RLCT is insensitive to it, say so — that changes
the verdict. Compute R|_{reg=0} explicitly.
</grounding_rules>
