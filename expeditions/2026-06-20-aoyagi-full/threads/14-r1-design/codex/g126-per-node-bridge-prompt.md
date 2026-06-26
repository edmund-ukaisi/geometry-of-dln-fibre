<task>
Adjudicate ONE structural question for a Lean build routing, with exact reasoning. Do NOT run code.

SETTING. RLCT of the matrix-chain core. There are TWO related splits:
- OUTER L2 split (verified, "WITNESS #125"): F = ||prod(C) - B||^2, B RANK r > 0. At the deepest point
  (every layer an identity-corner block-normal form) the regular block (dim nReg) splits off by an
  explicit triangular UNIT-PIVOT elimination — the regular generators have a perturbed-UNIT pivot (1+w0)
  (the identity corner perturbed), so the chart is UNIT-JACOBIAN (det = a unit, not ±1), no blow-up.
  Residual = the Schur-complement core ||prod(C')||^2 with B'=0.
- PER-NODE R1 chart (fm-2's schur_chart_exists, the crux): each reduced chain dlnLoss M' 0 =
  ||prod(C')||^2 with B' = 0 (ZERO-product core), straightened (Schur) at ITS deepest point = the ORIGIN,
  recursing M -> M' -> ...

QUESTION: does the OUTER L2 unit-pivot construction apply PER-NODE directly (giving schur_chart_exists),
or is the per-node R1 chart structurally different?

FACTS I established by exact computation:
- At the per-node ZERO-CORE origin (dlnLoss (2,2,2) 0 = ||A1 A2||^2, all C=0): ALL generators are
  BILINEAR (homogeneous degree 2), Jacobian rank 0 — NO regular block, NO unit pivot. So the unit-pivot
  regular peel (the OUTER #125 technique) does NOT apply at the zero-core origin.
- The per-node chart must therefore BLOW UP FIRST (the rank-stratum center, e.g. {A1=0}: A1 = x*Ahat,
  Ahat[0,0]=1 becomes a HARD constant 1, Jacobian x^{Mval-1}), THEN straighten with the HARD pivot. With
  a hard pivot 1, the Schur straighten is a pure TRANSVECTION (det=±1, MEASURE-PRESERVING) — exactly the
  (2,2,2) anchor's lemma2Fwd (det=−1, measurePreserving_lemma2, already green) — THEN recurse on the
  smaller zero-core.
- So per-node = [coordinate-subspace blow-up u^{Mval-1}] ∘ [hard-pivot transvection Schur straighten,
  det±1, MP]. The OUTER L2 split = [unit-Jacobian unit-pivot peel, NO blow-up] (B rank r>0, perturbed
  pivot). Different: per-node blows up first (B'=0, no regular block at origin); outer peels directly
  (B rank r>0, regular block present).
</task>

<sub_question>
1. Is the per-node R1 chart (schur_chart_exists) the SAME as the outer L2 unit-pivot split, or
   structurally different (blow-up-first + hard-pivot transvection, vs unit-pivot peel no-blow-up)?
2. Does the #125 unit-pivot TECHNIQUE (Schur straighten via a pivot) still recur per-node — but with a
   HARD pivot (post-blow-up) giving an MP/transvection straighten (lemma2Fwd-style) rather than the
   perturbed-unit pivot (unit-Jacobian) of the outer split?
3. Is the per-node chart still ELEMENTARY (no new Mathlib obstruction) — reusing the green coordinate-
   subspace blow-up (pivotBlowupOn) + the green transvection straighten (lemma2Fwd-style) — or does it
   hit a fresh obstruction once inside the core recursion?
4. Verdict for fm-2's routing: is schur_chart_exists "apply #125 per-node directly" (crux closes on the
   #125 banked structure) OR "a related but distinct C2 node (blow-up + hard-pivot transvection)
   reusing green pieces" OR "a fresh construction with a new obstruction"? Be precise.
</sub_question>

<output_contract>
- Verdict on per-node: same as outer, or structurally distinct (with the precise difference).
- Whether the #125 technique recurs (hard-pivot MP transvection per-node vs perturbed-unit outer).
- Whether the per-node chart is elementary (green pieces) or hits a new obstruction.
- The precise routing for fm-2 (apply-#125-directly / distinct-C2-node-reusing-green / fresh-construction).
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard resolution / RLCT theory. Reason on paper ONLY; do NOT read files
  or run code.
- "zero-core" = ||prod(C')||^2 with B'=0, deepest point = origin, all generators bilinear/homogeneous.
- "unit-Jacobian" = det a unit (not ±1); "MP/transvection" = det ±1, measure-preserving.
- Preserve FACT vs INFERENCE. Be precise about the per-node-vs-outer structural difference.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
