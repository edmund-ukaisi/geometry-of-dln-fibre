# Codex consult (gpt-5-codex, xhigh) — P2.j reroute

Prompt: `codex-prompt.txt`. Session `019f1e2e-a26b-75d3-ae9a-9f1b49bec4a8`.

## Verdict
- **Q1 (delegation preserves downstream defeqs):** Yes. Delegating each DLN def to its abstract
  counterpart preserves all prior definitional equalities; the only remaining consumer is the DLN
  file itself, now seeing the abstract term rather than a re-spelled surrogate, so unification /
  instance resolution behave at least as well. No opaque wrappers added. → HELD (build green).
- **Q2 (bump eliminable?):** Codex agreed the timeout is aligning the goal's reducible-typed
  `AlgEquiv.refl` target with the abstract lemma's, forcing the massive `whnf`, and proposed a
  `change` to pin the RHS `refl` at the abstract `targetChartLoc` type before `exact`. → This idiom
  did NOT work empirically: `show`/`change` into the abstract type, `simp only [def]; exact`, and
  `AlgEquiv.ext` pointwise all still time out at default 200000. Root cause (established here, past
  Codex's model): the cost is in elaborating the theorem STATEMENT's instance synthesis
  (`Semiring`/`Algebra` of the reducible `targetChartLoc`), which those tactics do not avoid — the
  expensive whnf happens before/around the tactic block, on the statement type itself. So the bump
  is intrinsic; reduced 800000 → 400000 by the reroute, not removable.
- **Q3 (`overlapElt` ascription):** With the ascription `Localization.Away (chartDsigAt I.s I.t)`
  (vs abstract `Away (pivotElt I)`, defeq via unfolding `pivotElt`), Codex suggested switching to
  `Away (pivotElt I)` to make it syntactic. → Empirically the `overlapElt` def elaborated fine with
  the current ascription (no timeout there); left as-is (harmless, and `overlapElt` is now consumed
  only in docstrings after the reroute).
