<task>
Lean 4 + Mathlib (v4.29) formalisation design review. I am closing a finiteness theorem
`sjJointResolution`: `gammaPeelIntegral M t ρ κ c' < ⊤` for `c' < minAdm M / 2`, where

  gammaPeelIntegral M t ρ κ c' = ∫⁻ A' in paramsBoxM (tailChain M) 1,
                                   ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
                                     ofReal (frobSq (rmatMul A0 (prod (tailChain M) A')) ^ (-c')).

`M : Fin (L+1+1+1) → ℕ` (widths of an (L+3)-vertex chain). `Params (tailChain M) = ∀ s : Fin (L+1),
Matrix (Fin (tailChain M s.castSucc)) (Fin (tailChain M s.succ)) ℝ` (the L+1 tail layer matrices;
`A' 0` is the leading tail layer, size M1×M2). `prod` is the left-associated layer product.

I have BANKED (all sorry-free) both ENDS of the intended change-of-variables:

(1) MEASURE-SIDE, unconditional EQUALITY:
    gammaPeelIntegral M t ρ κ c' = ∫⁻ A' in paramsBoxM (tailChain M) 1,
                                     ∫⁻ x in outerDom t (M0-t) (M1-t) 1,
                                       ∫⁻ Γ in {Γ | Γ + schurShift x ∈ genBox _ _ 1},
                                         ofReal (sjGoodChartLoss x Γ (Ã₁ A') (A₂ A') ^ (-c'))
  where Ã₁ A' = (A' 0).submatrix (blockSplitEquiv κ) id  (row-reindex of the leading layer),
        A₂ A' = the deep factor = reindex(prod (Mtail (tailChain M)) (Atail (tailChain M) A')),
        `sjGoodChartLoss x Γ A1 A2 = frobSq(P·v·A2) + frobSq((C·v+Γ·W)·A2)` with
        P = of x.1.1, C = of x.2, W = A1.submatrix Sum.inr id (corank rows of Ã₁),
        v = A1.submatrix Sum.inl id + P⁻¹·(of x.1.2)·W (κ-pivot rows of Ã₁, shifted).
  IMPORTANT: in the banked statement A₂ A' is written as `Classical.choose (sjTail_factor …)` — opaque;
  but its explicit value (a function of ONLY Atail(tailChain M) A', i.e. the DEEPER layers A' 1..L,
  NOT A' 0) is known.

(2) ENDPOINT end, with v EXPOSED as a free box variable:
    `sjGoodChartLoss_endpoint_lt_top`: given good-chart data (pivot P left-invertible LP·P=1; corank map
    W right-invertible W·RW=1; deep factor A2 right-invertible A2·RA=1) and c' < (a·b + t·h)/2,
      ∫⁻ y in matBox a b 1 ×ˢ matBox t h 1, ofReal (sjGoodChartLoss x y.1 (assembleFront x y.2 W) A2 ^ (-c')) < ⊤,
    where `assembleFront x v W` rebuilds the front factor with corank rows = W and pivot rows = v − P⁻¹·B₁₂·W,
    so that its depth-reduction boundary rows collapse back to `v`. (Proved via a banked corner endpoint.)
  Also banked: a BALL endpoint with an EXPLICIT bound `∫_{closedBall 0 R} g^{-c'} ≤ a^{-c'}·const(N,R,c')`
  and a `<⊤`-from-pointwise-sphere-positivity version (extreme-value theorem).

THE GAP: the MEASURE TRANSPORT connecting (1) to (2). In (1), `v` is a DETERMINED function of (A'0, x);
in (2), `v` is a FREE integration variable. I must transport
  ∫_{A' ∈ paramsBoxM} ∫_x ∫_Γ  g_cc(v(A'0,x))     →     ∫_{env} ∫_{(Γ,v)-box} g_cc(v)
where env = (deeper layers A'1..L determining A2, corank rows W of A'0, x=(P,B12,C)), by:
  (a) isolate A'0 from the deeper layers (Pi-split of paramsBoxM over Fin(L+1)); template available:
      `eFront`/`MeasurableEquiv.piFinSuccAbove` + volume_preserving_piFinSuccAbove + a box-preimage lemma;
  (b) split A'0's rows into κ-pivot-rows × complement-rows(=W); template: `blockSplitD`/`splitCols`
      (measure-preserving row/col splits via sumPiEquivProdPi);
  (c) translate the pivot rows (Ã₁)_p ↦ v = (Ã₁)_p + P⁻¹·B12·W (fixed x,W): `measurePreserving_add_right`.
  Then restrict to the GOOD cover (|det pivot| ≥ δ ⟹ left-inv; W, A2 generic ⟹ right-inv) to feed (2),
  integrate the finite inner over the bounded env (uniform bound from the ball endpoint), and handle the
  deeper (non-good) branch by a banked charge inequality + an L-recursion over the rank flag.

Constraints/known frictions (Mathlib v4.29): dependent-width matrix products (Fin (tailChain M …)) break
`rw`-matching through HMul — must use fully-applied terms / `.trans`. `Classical.choose` in a statement
blocks `rw`/motive because its type mentions the abstracted term. `Matrix.submatrix_mul` needs a bijective
middle reindex.
</task>

<output_contract>
Be concrete and Lean-4-idiomatic. Sections, in this order:

1. ROUTE RANKING. Rank two candidate structures for the transport, cheapest-to-formalise first:
   (A) Pi-split A'0 then Fubini then per-fiber row-split + pivot-translation;
   (B) a single fiberwise SHEAR on the A'0 matrix (add P⁻¹B12·(complement rows) to the κ-rows), Jacobian 1,
       treating deeper layers + x as environment — analogous to the banked schur shear.
   For each: the sequence of Mathlib lemmas / measure-preserving maps, and the ONE step most likely to
   thrash. State which you'd commit to and why.

2. THE Classical.choose FIX. The cleanest way to make A₂'s deeper-layers-only dependency usable: restate
   the measure-side equality with the EXPLICIT deep factor (a def `sjDeepFactor M A' := reindex(prod
   (Mtail (tailChain M)) (Atail (tailChain M) A'))`), so the Pi-split can see A₂ is constant in A'0. Give
   the lemma shape.

3. GOOD/ENV STRUCTURE. How to organise the good-cover restriction + environment integration so the inner
   (Γ,v)-integral (finite, uniformly bounded on good env) integrates against the finite-measure env box —
   the exact Tonelli/monotonicity skeleton, and whether the shifted (Γ,v) shear-image box needs the BALL
   endpoint (⊆ fixed ball domination) vs the CUBE endpoint.

4. SMALLEST NEXT LEMMA. The single smallest self-contained lemma to formalise next that is (i) within one
   tide's reach, (ii) a genuine step of the transport (not scaffolding). Give its exact Lean statement.

5. WALL CHECK. Is any sub-step a genuine mathematical wall (not just labour)? If so, name it precisely.
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the given API names vs. what you INFER about Mathlib lemma
availability. Flag any lemma name you are NOT confident exists at v4.29 as "verify exists". Do not invent
lemma signatures with false confidence. The measure-transport is believed to be labour (not a wall) per a
prior certificate; if you disagree, say so and why.
</grounding_rules>
