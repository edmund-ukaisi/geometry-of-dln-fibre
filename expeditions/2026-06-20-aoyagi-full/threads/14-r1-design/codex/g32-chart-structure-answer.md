# Codex (gpt-5, high effort, web-search) — G3.2 chart structure (A)/(B)/(C)

Decorrelation consult by fm-2, 2026-06-21, on whether the general-M Schur resolution chart is
det-1/measure-preserving (A), a Jacobian-carrying blow-up (B), or both-in-sequence (C). Codex read
Aoyagi's neuralnet.pdf + the Lehalleur–Rimányi paper.

## Verdict: (C) — det-1 GL straightening THEN blow-ups with monomial Jacobian weights.

**Chart structure.** Aoyagi first straightens the regular blocks by GL-actions (det-1) but THEN
executes explicit blow-ups along rank-defect strata to achieve normal crossings. Each blow-up
replaces a block of vanishing minors by `d = u·d'`, the exceptional parameter `u` capturing the pivot
size; the coordinate Jacobian acquires factors `u^{h_j}` (never all zero once a rank drop occurs), so
the chart is NOT measure-preserving.

**Recursion statement (THE FIX).** After resolving, `K∘π = ∏ u_j^{2k_j} · (‖x‖² + ‖reduced‖²)` and
the Jacobian contributes `∏ u_j^{h_j}`; RLCT = `min_j (h_j+1)/(2k_j)` — NOT a pure
`nReg/2 + RLCT_reduced`. A clean additive recursion holds ONLY when every exceptional exponent `h_j`
vanishes. Once blow-ups appear, the correct step is
   RLCT = min{ nReg/2, monomial thresholds from the new exceptional coords, RLCT(reduced) }
matching Watanabe's general resolution formula — i.e. the `⨅ monomialThreshold` form.

**Implications.** The monomial Jacobian factors are what produce Aoyagi's arithmetic minimum over
distributions of the rank deficit; L–R re-express the same minimum as `codim(mult⁻¹(0))/2`. A
det-1-only Schur chart CANNOT recover the observed RLCT — the blow-up's nontrivial weights enforce
the piecewise-linear minimum. (2,2,2) already needed a pivot blow-up; the general proof iterates the
same pattern.

## Consequence for the Lean SPECIFY (fm-2)

- `schur_rlct_recursion_step` as `rlctAtOn(dlnLoss M 0) 0 = nReg/2 + rlctAtOn(dlnLoss Mred 0) 0` is
  UNSOUND as a standalone identity (omits the monomial weight). RETRACTED.
- `IsSchurChart` with a bare scalar unit `u` and no exceptional monomial Jacobian is INCOMPLETE.
- The recursion-step output must be the `⨅ monomialThreshold` form (already the shape of
  `resolution_charts` Skeleton:1021) — the chart is a blow-up carrying monomial weights, NOT a clean
  measure-preserving reduction. This matches the (2,2,2) ladder's actual architecture (pivotBlowup +
  ⨅ monomialThreshold), so the general-M route is the (2,2,2) route iterated, not a new clean chain.
