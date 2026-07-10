<task>
Lean 4 + Mathlib formalisation. I must prove one open leaf `sjJointResolution`:

  gammaPeelIntegral M t ρ κ c' < ⊤,  where
  gammaPeelIntegral M t ρ κ c' :=
    ∫⁻ A' in paramsBoxM (tailChain M) 1,
      ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
        ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))
  hypotheses: 1 ≤ t ≤ min(M0,M1), c' < minAdm M / 2, and an arity IH
  (box-finiteness for every one-shorter chain). M : Fin (L+3) → ℕ (opaque width).

BANKED (proven, reusable) endpoint I just landed (module RouteMSJCornerGate):
  corner_block_cube_lintegral_lt_top_of_injective:
    for INJECTIVE linear L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) and c' < n/2,
    ∫⁻ z in [-1,1]^n, ofReal ((∑ⱼ (L z)ⱼ²)^(-c')) < ⊤.
  (i.e. a positive-definite squared-linear loss on the flat cube is endpoint-integrable.)
Also banked: front-split (box integral = tail-outer front-factor fibre integral), pivot-chart
cover (sjBoundaryPeel, CLOSED), the EXACT Schur block split
  frobSq(A0·Q) = frobSq(A·Q̃p) + frobSq(C·Q̃p + Γ·Qb), Γ = D − C A⁻¹ B  (A = pivot block, invertible on chart),
measure-preserving shear D↦Γ (Jacobian 1), block-reindex Fin(M0)≃Fin t⊕Fin(M0−t) (MP), radial
polar blow-up, monomial endpoint.

PINNED design route (pen-and-paper cert, decorrelated-Codex-concurred): refine the pivot chart into
GOOD {|det pivot| ≥ δ·scale} ∪ DEEPER (small-pivot + deep-factor-rank-drop) branches; on the GOOD
chart the cross-coupled Schur loss g_cc(joint block E_T) is a positive-definite quadratic form
(dim E_T = Mval(T) = the charge, min over branches = minAdm), fed ONCE to the corner endpoint
(threshold Mval/2, min = minAdm/2). Deeper branches non-binding by banked charge-budget
(minAdm ≤ (M0−t)(M1−t) + minAdm(redChain t M)); finite-flag termination.

The gap between gammaPeelIntegral and the banked endpoint is the change-of-variables / resolution
map + the L-recursion over the rank flag + the refined cover + deeper-branch closure. Prior recon
estimates this at ~65-75% genuinely-new Lean; it is a multi-tide mountain, NOT closeable in one tide.

I have ~a few hours of one Lean tide left. I want the SINGLE most valuable, genuinely tide-reachable
(green, sorry-free) sub-lemma to bank next — one that is (a) network-free or nearly so, (b) reusable
by the eventual assembly, (c) NOT itself the whole CoV. Candidates I am weighing:
  C1. injectivity criterion: A0 ↦ rmatMul A0 Q is injective (as flat linear map) ⟺ rank Q = M1
      (full row rank) — connects brick 3's "L injective" to a concrete rank condition.
  C2. the g_cc loss (a²·frobSq(v·A₂) + frobSq((C·v+Γ·W)·A₂)) as an explicit squared-linear form
      L(Γ,v) on the joint block, + its injectivity ⟺ [pivot≠0 ∧ W,A₂ full row rank].
  C3. the good-chart-ONLY reduction of the inner A0-integral to a corner integral (defer deeper
      branches + outer A'-recursion as explicit hypotheses/sorries), wiring brick 3.
  C4. the refined-cover chart split {good ∪ deeper} as a pure set-cover inequality (measure theory,
      no CoV), analogous to the banked pivotChartCover.
  C5. something else I'm missing.
</task>

<output_contract>
1. RANK the candidates C1-C4 (+ any C5 you propose) by (value to the eventual assembly) × (Lean
   tide-reachability at opaque width), best first. One line each on WHY.
2. For the TOP pick: the precise Lean statement (signature) you'd write, the 3-6 proof steps, and
   the main Mathlib/friction risk. Keep it to what fits one tide.
3. FLAG explicitly: is any candidate secretly the whole CoV mountain in disguise (i.e. not
   tide-sized)? Which, and why.
4. One line: is banking endpoint-admissibility bricks (done) + one more brick, then reporting the
   CoV as the remaining mountain, the right call for a leaf executor here — or is there a
   higher-leverage move?
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the algebra given vs INFERENCE about Lean tractability (label
the latter). Do not assume Mathlib lemma names exist — describe the mathematical content, flag where
a name would need checking. If a candidate's difficulty is uncertain, say so rather than guessing.
</grounding_rules>
