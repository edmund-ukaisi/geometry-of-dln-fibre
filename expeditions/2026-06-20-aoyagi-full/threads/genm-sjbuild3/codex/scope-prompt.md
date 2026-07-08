<task>
Lean 4 / Mathlib formalisation of Aoyagi's RLCT computation for deep linear networks (the
Lehalleur–Rimanyi 2024 paper). I need a decorrelated scope verdict on ONE target and its stated
one-tide plan, because my controller's task framing ("no wall — size + one real inequality proof")
is at odds with the repo's own accumulated evidence.

THE TARGET. Close a named `sorry`, `sjJointResolution`:
  gammaPeelIntegral M t ρ κ c' < ⊤
where, for a chain of widths M : Fin (L+3) → ℕ, pivot cut (t,ρ,κ), and c' < ½·minAdm M,
  gammaPeelIntegral M t ρ κ c'
    = ∫_{A' ∈ box(tailChain M)} ∫_{A0 ∈ matBox(M0)(M1) ∩ pivotChart ρ κ}
        (frobSq(A0 · prod(tailChain M) A'))^{-c'}.
The hypothesis available is the strong IH: RouteMBoxThresholdFinite M' for EVERY one-shorter chain
M' : Fin (L+2) → ℕ, where RouteMBoxThresholdFinite M := ∀ c'<½·minAdm M, ∫_{box} frobSq(prod M A)^{-c'} < ⊤.

WHAT I HAVE ESTABLISHED (Lean-verified, banked this tide, clean-three axioms):
(1) A monotonicity reduction: gammaPeelIntegral M t ρ κ c' ≤ routeMLayerBoxIntegral M c' 1
    (= ∫_{box} frobSq(prod M A)^{-c'}), a pure subset-integral bound. HENCE sjJointResolution
    follows IMMEDIATELY from standalone RouteMBoxThresholdFinite M (the SAME chain M, not shorter).
    Note this makes the peel spine (sjBoundaryPeel: box ≤ ∑ gammaPeel) circular for proving
    box-finiteness — box ≤ ∑ gammaPeel ≤ (#charts)·box is vacuous.
(2) A banked freed-Γ EQUALITY (gammaPeelIntegral_schurShearFree_eq): via block-reindex + Schur weld +
    measure-preserving shear, gammaPeelIntegral rewrites to ∫_{A'} ∫_{x} ∫_{Γ freed}
    (freedSchurLoss x Γ Q̃)^{-c'}, Γ the corank block (dim (M0-t)(M1-t)) an independent variable,
    Q̃ = tail product submatrix.
(3) Banked regime lemmas for the freed inner Γ-integral over matBox:
    - regime A (matBox_corank_residual_absZ_le): ∫_z ∫_Δ (frobSq Δ + W z)^{-c'} ≤ Cresid·∫_z W^{-(c'-pq/2)},
      requires W z > 0 STRICTLY and c' > pq/2;
    - regime B (matBox_corank_dominates_absZ_lt_top): ∫_z ∫_Δ (frobSq Δ + W z)^{-c'} < ⊤,
      requires c' < pq/2, W ≥ 0, μ(Z) < ∞.
(4) Conditional inner finiteness (freedSchurLoss_inner_peel_lt_top): the inner Γ-integral is finite
    GIVEN three interface hypotheses that FAIL pointwise: pivot energy frobSq(P·Q̃ₚ) > 0 (can vanish),
    Q_b Q_bᵀ positive-definite (rank-deficient on ≈15% of charts when M1−t > min deeper widths),
    c' > pq/2 (not forced by c' < ½·minAdm M on ≈20% of charts).
(5) A decorated-recursion scaffold: a predicate DecoratedBoxThresholdFinite over a generator-carrier
    decoration; DecoratedBoxThresholdFinite(trivial M) ↔ RouteMBoxThresholdFinite M (banked);
    carrierThreshold M = ½·minAdm M; a banked soundness shift carrierThreshold M − ½·peelCharge ≤
    carrierThreshold(redChain). The peel step and terminal dispatch are UNBUILT.

REPO EVIDENCE saying "multi-tide monument": a prior decorrelated Codex scope-answer (65–75% genuinely
new construction — finite chart tree, explicit iterated blow-up maps, null-set control, Jacobian product,
leaf assembly); a design cert saying "at the binding cut minAdm M = pq + minAdm(redChain t* M) the
residual exponent EXACTLY saturates the reduced-chain IH threshold — Hölder-infeasible — so the strong
IH is insufficient as a black box"; and my own point that regime A needs W>0 strictly, which fails on the
vanishing/rank-deficient locus, requiring further blow-up (= resolution of singularities).

MY WORKING CONCLUSION: closing sjJointResolution reduces (via my monotonicity bound) to proving
RouteMBoxThresholdFinite M for ALL M via the decorated recursion, which IS the explicit
resolution-of-singularities chart-tree construction — a multi-module monument, not a one-tide close.
The controller should re-scope.
</task>

<output_contract>
Four sections, terse:
1. VERDICT: Is closing sjJointResolution a one-tide task or a multi-tide monument? One paragraph.
2. Is my monotonicity reduction (item 1) CORRECT and NON-CIRCULAR as stated, and is it a fair
   characterization that it makes the peel spine vacuous for proving box-finiteness? Flag any error.
3. Is there ANY one-tide path I am missing — e.g. a way to prove RouteMBoxThresholdFinite M or
   gammaPeelIntegral < ⊤ that dodges the W>0 / rank-deficient-Q_b wall using the banked pieces + the
   strong IH? If yes, the single cheapest concrete route. If no, state so plainly.
4. If multi-tide: what is the SINGLE highest-value genuinely-completable (sorry-free) sub-brick to bank
   next toward the decorated recursion, given the banked pieces above?
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the definitions I gave vs. what is INFERENCE about the mathematics.
Do not assume Mathlib lemmas exist without flagging as "would need to check". If you believe my
monotonicity reduction is wrong, say exactly why. Do not soften a "multi-tide" verdict to please the
framing — I want the honest call.
</grounding_rules>
