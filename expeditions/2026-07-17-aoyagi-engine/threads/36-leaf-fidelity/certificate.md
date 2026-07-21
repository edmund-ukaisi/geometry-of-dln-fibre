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
