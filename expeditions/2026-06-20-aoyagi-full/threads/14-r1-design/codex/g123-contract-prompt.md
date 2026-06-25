<task>
Adjudicate the COMPLETENESS + SOUNDNESS of a Lean INTERFACE contract, with exact reasoning. Do NOT run code.

SETTING. General-M resolution of the zero-product matrix-chain core F = ||prod(C)||^2 (the RLCT
critical path). The recursion NODE (validated as C2: det-1 GL-straighten THEN coordinate-subspace
blow-up) is being formalised. A formaliser proposes a 5-field INTERFACE contract `resolvedForm` that
each recursion node must satisfy, before committing the node body. We validate it against the (2,2,2)
Lean anchor and flag missing guarantees for general M.

THE 5-FIELD CONTRACT (what the node's resolvedForm must guarantee):
1. TYPE: resolvedForm : (chart domain) -> (Fin N' -> R), the straightened coords.
2. MEASURE-PRESERVING / det-1: unit Jacobian, no exponent shift.
3. COORDINATE-CENTER ID: maps the bilinear rank-defect locus {r-pq=0} to a coordinate subspace {w=0},
   exposing the EXPLICIT pivot/active index set the blow-up consumes.
4. REDUCED-CHAIN MAP: exposes the reduced widths M' + the residual core'.
5. STRICT-TRANSFORM EQ: core x = core'(resolvedForm x) on the chart.

FACTS I established from the (2,2,2) Lean anchor (lemma2Fwd / measurePreserving_lemma2 / step1Residual
/ resolvedForm) by exact algebra:
- Field 1: lemma2Fwd : (Fin 7→R)→(Fin 7→R), the straightening. EXHIBITED.
- Field 2: measurePreserving_lemma2, det=−1, unit Jacobian. EXHIBITED.
- Field 3: the straightened coord δ = t3 − t1·t2 (the bilinear {r−pq=0} → {δ=0}); center {E=F0=δ=0} =
  slots {1,2,3}; pivotBlowupOn {1,2,3} consumes EXACTLY that index set. EXHIBITED with explicit pivot set.
- Field 5: step1Residual v = resolvedForm(lemma2Fwd v), ring-proven. EXHIBITED.
- Field 4 (REDUCED-CHAIN MAP): the (2,2,2) resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)² is a single
  explicit QUADRATIC; it goes STRAIGHT to the step-2 blow-up. The δ-branch residual block
  E'²+F0'²+(qE'+G)²+(qF0'+H)² IS exactly ||Â'·B'||² for a SMALLER chain (Â'=[[1,0],[q,1]],
  B'=[[E',F0'],[G,H]]) — a reduced-chain core — BUT the (2,2,2) anchor handles it as a literal small
  4-square SMOOTH BLOCK (monomialized directly by step-3), NEVER exposing a reduced-chain MAP.
  So field 4 is NOT exhibited by (2,2,2); it is degenerate-trivial there (the residual is small enough
  to monomialize without recursing).
</task>

<sub_question>
(a) Does the (2,2,2) anchor exhibit exactly these 5 fields? (My finding: fields 1,2,3,5 YES; field 4 NO
    — it's hidden/degenerate at (2,2,2) because the residual block is monomialized directly, not recursed.)
(b) Is any guarantee MISSING at general M that (2,2,2) hid? Specifically:
    - Is field 4 (the reduced-chain map exposing M' + core') GENUINELY NEEDED at general M (where the
      residual core is a LARGER ||prod(C')||² that must be re-straightened + re-blown-up recursively,
      not monomialized directly), even though (2,2,2) avoids it? If so, the (2,2,2) anchor under-tests
      field 4 and the formaliser must not infer field 4's correctness from (2,2,2).
    - Is there a 6th missing guarantee — e.g. WELL-FOUNDEDNESS of the recursion (the reduced M' has
      strictly smaller ΣM so the node-recursion terminates)? The 5 fields as stated don't include a
      termination/measure-decrease guarantee. Is that needed for the general-M cover to close?
    - The L≥3 NON-EMPTY-CORE case (an earlier confound): at an intermediate fibre point the residual core
      is non-empty (gen-Jac-rank < #generators). Does the contract handle a non-trivial residual core'
      (field 4 non-empty), or does it implicitly assume the (2,2,2)-style small/empty residual?
(c) Is field 3's coordinate-center ID stated tightly enough — does "exposes the explicit pivot/active
    index set" give the blow-up machinery (a g5_pivotNode that blows up a NAMED coordinate subspace
    {y_1=…=y_c=0}) exactly what it consumes (the explicit finset of active indices + the codim c)? Or is
    it under-specified (e.g. just "a coordinate subspace exists" without the explicit index set / codim)?
(d) Verdict: is the 5-field set COMPLETE + SOUND for the general-M cover, anchored in (2,2,2)? Flag any
    missing field or under-specification.
</sub_question>

<output_contract>
- (a) per-field: which of the 5 the (2,2,2) anchor exhibits vs hides.
- (b) the missing-field flag: is field 4 genuinely needed at general M (under-tested by (2,2,2))? Is a
  6th (well-foundedness / measure-decrease) field missing? Does the contract handle the L≥3 non-empty core?
- (c) is field 3 tight enough (explicit pivot finset + codim) for the coordinate-subspace blow-up?
- (d) COMPLETE+SOUND verdict + the precise list of additions the formaliser needs before committing the body.
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard resolution / RLCT theory. Reason on paper ONLY; do NOT read files
  or run code.
- A "coordinate-subspace blow-up" consumes a named finset of active indices {y_1..y_c} and the codim c
  (Jacobian u^{c-1}). The recursion closes only if each residual core' is again resolvable (field 4) and
  ΣM strictly drops (termination).
- Preserve FACT vs INFERENCE. Be blunt about under-tested fields.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
