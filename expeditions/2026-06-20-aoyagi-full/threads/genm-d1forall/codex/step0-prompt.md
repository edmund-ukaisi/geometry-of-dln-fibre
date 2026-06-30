<task>
Lean 4 + Mathlib formalisation, DLN-fibre RLCT project. I must discharge ONE leaf of an
L=2 headline scaffold, the D1 (≥)-leg ∀-v slot. I need an independent verdict on whether
it is REACHABLE from the banked pieces, or whether there is a genuine SCOPE obstruction.

THE EXACT TARGET (`hD1ge_L2`), at general L=2 widths H : Fin 3 → ℕ, r : ℕ, with
hpos : ∀ s, r < H s, and B' a front-pivoted matrix with rank r:

    ∀ v ∈ optimalSet H B',
      rlctAt H (dlnLoss H B') (deepestPoint H r B' …) ≤ rlctAt H (dlnLoss H B') v

`optimalSet H B' = {A | prod H A = B'}` (the fibre). The deepest reduced widths are
`H − r` (componentwise), which for GENERAL H need NOT be square.

THE BANKED ENGINE (`rlctAt_deepest_le_of_optimal_L2`, sorry-free modulo its hyps),
per a fixed v, concludes the per-v ≤, but it is SCOPED and requires, among others:
  (1) `hcoreDeepest : coreDeepest = ofReal(lambdaCore (squareWidths m))` — i.e. the
      DEEPEST reduced widths must be SQUARE (m,m,m). The middle-stratum arithmetic
      (extra/2 + lambdaCore(M') ≥ lambdaCore(square m), M'=(m−a,m−a−b,m−b)) is proven
      ONLY for square deepest widths (a 164-strata sweep 1≤m≤8). Non-square reduced
      widths H−r are explicitly flagged "beyond the banked adjudication."
  (2) `hDeepest : rlctAt deepest = nRegL2/2 + coreDeepest` — the #44 equality. Available
      sorry-free via `deepest_regular_core_normal_form_L2_front` BUT it produces
      `ofReal(lambdaCore (fun s => H s − r))` (the ACTUAL, possibly-rectangular reduced
      widths), conditional on htop/hcolfront (WLOG-supplied) + hRValue (R1, supplied by
      the scaffold's separate R1 leaf hR1_L2).
  (3) first-peel chart data (q, hq, t0, hchart, hRne, hslice, hslice0) — producible
      sorry-free at ANY optimal v via `dln_hchart_residual` + `exists_jacFlatL2_minor`.
  (4) `(m,a,b)` with `a+b ≤ m` and `hrank₂ : extraCount m a b ≤ (jacResid (q(0,·)) t0).rank`
      — the second-peel rank bound. De-risked "BOUNDED" but NOT yet a proven theorem; it
      needs a middle-stratum first-order range bound + a Schur quotient-rank step +
      determinantal-engine minor extraction.
  (5) `hInterface` (R1 resolution at the degraded M') — supplied via the scaffold's R1 leaf.

TWO CANDIDATE GAPS I see for the GENERAL-H, ∀-v leaf:
  GAP A (square-widths scope): the engine's hcoreDeepest forces deepest widths square,
  but my leaf is at GENERAL H (H−r possibly rectangular). The #44 value the scaffold's
  STEP-C value side uses is lambdaCore(H−r), NOT lambdaCore(square m). So for non-square
  H−r the engine's `coreDeepest = ofReal(lambdaCore(square m))` cannot match the #44 value
  `ofReal(lambdaCore(H−r))` — the deepest-side equality the engine needs is for the
  WRONG core unless H−r is square.
  GAP B (∀-v coverage + (m,a,b)/hrank₂): even at square H, producing (m,a,b)/hrank₂ at a
  GENERAL optimal v (every stratum, not just the middle stratum) is unbuilt.

WHAT I NEED ADJUDICATED:
- Is GAP A a genuine obstruction to discharging `hD1ge_L2` at GENERAL H with ONLY the
  banked pieces + the two scaffold leaves (R1 + this D1 leaf)? I.e. is the D1 ≥-leg
  engine fundamentally square-deepest-width-scoped, so the general-H leaf CANNOT be
  closed without either (i) new non-square middle-stratum arithmetic, or (ii) a
  different ∀-v route that does not go through the square-only engine?
- If GAP A is real: is there a DIFFERENT bounded route to the per-v ≥ that does NOT
  require square deepest widths? Candidates: a direct first-peel-only monotonicity
  argument (Aoyagi Lemma 1 radial-scaling: rlctAt is monotone in the residual, so the
  all-zero deepest core dominates), bypassing the second peel entirely. Note the FIRST
  peel `dln_hchart_residual` works at general v AND general H. The question is whether the
  deepest-side core value lambdaCore(H−r) can be shown ≤ the slice residual's RLCT WITHOUT
  the square-widths second-peel arithmetic.
- Rank GAP A vs GAP B by which is the true blocker for the GENERAL-H leaf.

Treat this as a SCOPE adjudication: I would rather STOP and flag a precise obstruction
than force a vacuous proof. An expedition note (Item 99) claims "the D1 side has NO
research wall (bounded)" — but that may have been judged at SQUARE H only. Tell me if
the general-H ∀-v leaf is bounded or hits GAP A.
</task>

<output_contract>
1. VERDICT on GAP A: GENUINE OBSTRUCTION at general H, or NOT (one line + why).
2. VERDICT on GAP B: bounded or wall (one line).
3. If GAP A is real: the single cheapest bounded route to the general-H per-v ≥ that
   avoids the square-only engine (name the mathematical mechanism + which banked pieces
   it reuses), OR "no bounded route — flag and stop."
4. The precise lemma chain for whichever route you recommend (≤ 8 steps).
5. RANK: GAP A vs GAP B — which is the true blocker.
Keep it under ~500 words. Flag inference vs. asserted-fact explicitly.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason from the structural description above; do NOT invent
Mathlib lemma names as if confirmed. Mark every claim as (inference) unless it follows
directly from the stated structure. If you cannot adjudicate GAP A without seeing a
specific definition, say which definition and why.
</grounding_rules>
