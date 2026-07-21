# Thread 36 — leaf-statement fidelity review (rev-leaves)

> Controller-banked 2026-07-21 from the reviewer's verdict message; probes copied from /tmp
> (VM-volatile) and controller re-run EXIT 0 against the PRE-FIX statements at tip c63f3cf1e.
> Full verdict in the journal ("REV-LEAVES VERDICT" entry) and the reviewer's message.

VERDICT: 2 BLOCKING statement defects + 1 contract weakness; L1/L3/L5/L6/L7/L8 statements PASS;
root non-vacuity PASS; C1 import boundary PASS; D1/D4 PASS.

- `smell_probes.lean` — the KILL-SET WITNESSES: (i) a Lean PROOF of `¬ TerminalBezout` (witness
  V = {u | 0 < u 0}: all hypotheses hold, no open V' ∋ 0 fits in V — the statement as reified is
  FALSE); (ii) the StepInvChild collapse (`fun _ => h` discharges `∀ _branch : Bool, StepInvChild …`
  from ONE child — the branch quantifier is cosmetic). arch-C's fix gate: BOTH constructions must
  FAIL against the fixed statements.
- `root_probe.lean` — the NON-VACUITY witness: the root instance
  `StepInv F id (fun _ ↦ 1) F (Kronecker) V` elaborates; terminal PrincipalInv inhabitable. Must
  STILL elaborate after the fixes.
- `codex/` — the decorrelated consult (corroborated both blocking findings; supplied the
  complementary V = {0} witness and the monomial-⇏-scalar-divisibility fact against
  StructuralChainResidual).

Fixes commissioned to arch-C (same tick): terminal_bezout +IsOpen V +0∈V +ContinuousOn unit V;
StructuralChainResidual falsity-test then re-state-as-vector-chain-or-drop; StepInvChild real branch
parameter; minors (L4 docstring nR'<nR; PivotOrderingK0 inline discharge; unused hne). Elder second
delta (D2'/D3 amendments) running in parallel.

## POST-FIX FLIP (controller re-run, 2026-07-21, post-merge ddbecb57e)
- `smell_probes.lean` now FAILS (EXIT 1: the ¬TerminalBezout construction is type-rejected — `IsOpen V`
  required). The fix is real. NOTE (arch-C): the literal s2 probe is a tautology ABOUT StepInvChild
  (unchanged, still compiles standalone); the actual collapse fix lives in `Case1Preservation`'s
  branch-δ-law conclusion — re-point future kill-witnesses there.
- `root_probe.lean` still elaborates (EXIT 0) — non-vacuity preserved.

## ROUND-2 (diff-scoped re-verification, 2026-07-21)
The four fixes PASS (block-reasons verified: the old ¬TerminalBezout witness dies at exactly `0 ∈ V`;
the Case1Preservation branch collapse is jointly-unsatisfiable-dead). NEW BLOCKING: **L7 and L8 are
FALSE as stated** — both quantify over a FREE `atlas : GeoAtlasData` with no field tying it to the
fold/tree. `l7probe.lean` = the degenerate-atlas refutation (n=1, steps=[], gmap=id, dom={0}: no ball
fits in {0}); `l8probe.lean` = the adversarial-jac refutation (jac := sum+1 beats single_le_sum).
Controller re-ran both: EXIT 0. Root cause: the fold's guarantees (witness law, per-chart
PrincipalInv) never reach L7/L8 through a bare GeoAtlasData — and FIX 2's (correct) deletion removed
L8's only (false) tree-link. arch-C's case-2-b'-law open note was a SYMPTOM of this. FIX direction:
anchor the atlas to the fold (provenance predicate or GeoAtlasData enrichment) — dispatched to arch-C.
`reverify.lean` = the round-2 fix-verification probes. Wave impact: L3/L4 statements SOUND (L4 seat
commissioned); L5's atlas-producing half sound (statement may gain the provenance clause); L7/L8 seats
HELD on the anchoring.

## AMENDMENT-ROUND FLIP (controller re-run, post-merge 248c34615)
- `l4probe_refute.lean` now FAILS (EXIT 1) — the S3 vanishing clause makes its constant-family
  StepInv premise unsatisfiable. ✓ flip.
- `root_probe.lean` (S3-updated to a vanishing family) still elaborates. ✓ non-vacuity.
- `l7probe.lean` / `l8probe.lean` still compile — EXPECTED: they are SELF-CONTAINED (they refute the
  OLD ∀-atlas Prop taken as a hypothesis, not the named theorems). Kept as historical kill-witnesses.
  The REAL verification (controller, direct reading): the amended L7/L8 each take
  `hfold : FoldProduced d e atlas`, and FoldProduced's `hdom_ball` clause excludes the dom = {0}
  degeneracy — the anchored statements cannot be fed the degenerate atlas.
- Cone re-verified = exactly the 8 leaves; O9 atoms off-cone; batch-341 + cordon green.

## KERNEL-CHECK ROUND (rev-leaves, post-elder-ruling; controller re-ran both, EXIT 0)
- `elder_refute.lean` — **¬ Case2Preservation, machine-proven** (the elder's |S|=1 witness: F =
  coordinates, spec center {0}, δ=1; blockBlowupMap {0} 0 = id ⟹ σ = sh; child StepInv forces sh ≡ 0
  on the u₀=0 slice; the slice-derivative kills e₁ ⟹ det Dsh(0) = 0 ≠ 1 — closed WITHOUT the inverse
  function theorem). The free-standing Case-2 ∀-(state,spec) form is FALSE, proven.
- `case1_rescue.lean` — **the round-3 (A) Case-1 half is RETRACTED**: the misaligned-spec witness is
  RESCUED by a jacDet-1 rotation ((x₀,x₁,x₂) ↦ (x₀,x₂,−x₁) makes 2u₀u₂ ↦ −2u₀²u₁ ∈ ⟨u₀²⟩, `by
  ring`). The |S|=1 killer requires card = 1, excluded by Case-1's 2 ≤ card guard. **Case-1's
  free-standing form is UNRESOLVED** — shears rescue every witness tried. Edge-indexing of BOTH
  remains ratified on constructibility + provenance grounds (hbranch_len unsatisfiability; the
  closing principle), NOT on a Case-1 falsity claim — docstrings must not overclaim.
- Calibration note: the shear slot does REAL algebraic work beyond the paper's row/column clears
  (relayed to seat-L4 as a construction asset).
