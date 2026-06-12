# Review

Review is an independent adversarial audit, run by a **reviewer** teammate the
controller spawns (a thread never reviews itself). A reviewer can call
`local-codex-consult` for a decorrelated Codex opinion. Review is a general
capability, not only the formalisation AUDIT gate.

## Functions

A reviewer is aimed at one target with one function:

- **Fidelity** (the formalisation AUDIT gate) — do the Lean statement and its
  hypotheses match the informal claim? **Report-only**: fidelity findings escalate
  to the operator; the reviewer never silently rewrites the mathematics.
- **Simplification** — meaning-preserving Lean improvements (shorter proofs,
  Mathlib lemmas subsuming hand-rolled code, redundant hypotheses, dead code).
  Implementable behind a **signature-invariance check**: re-extract the public
  theorem/def signatures before and after; a changed signature is a fidelity edit
  (escalate), not a simplification.
- **Claim-soundness** — a harder adversarial stress-test of a claim than its
  explore thread ran: counterexample hunt against the kill-condition. For a **universal / negative /
  exhaustiveness** claim ("holds for all", "no counterexample", "the case-split is complete") this
  **decorrelated hunt is the gate**: it must have attacked the claim and failed before the claim is treated as
  established; an empty hunt is *scoped evidence* (state what was searched), never a proof — review confirms
  the cases shown, the hunt surfaces the case missed ([`bedrock.md`](bedrock.md) § the refutation dialectic).
- **Mathematical precision** — does the name and statement denote *exactly* what is
  proved? Are **Proved / Assumed / Cited / Deferred** separated ([`precision.md`](precision.md))?
  Is the **load-bearing** step proved, or merely assumed and named as the open target — not
  dressed as done? Catches the impressive-name / premature-"done" pull. **Report-only**, like fidelity.
- **Synthesis-coherence** — does `synthesis.md` overclaim relative to what threads
  established? Are caveats co-located with claims? Is terminology consistent?
- **Exposition fidelity** — does a human-facing exposition (`expeditions/<id>/expositions/`)
  faithfully represent what the threads actually did and found — correct before elegant before
  efficient? Report-only, like Lean fidelity.
- **Wording / object-level scrub** — remove meta-hedging and selling phrasing from
  any authored doc; check coherence. See the list below.

## Wording: object-level focus

Authored docs state what to do and why, at the object level. Remove authorial
self-reassurance; keep only object-level directives to the reader. Resist meta-commentary.

Banned-wording list (flag each, judge, remove the hedging use; an object-level
directive such as "report the result honestly" stays):

```
honestly · importantly · fundamentally · the whole point is · definitely · 
of course · simply · just · needless to say · clearly · obviously · this is loadbearing
```

`grep -rniE` the list across authored docs during a wording pass.

## Review to equilibrium

A **critical** finding is a fidelity mismatch, a refuting counterexample, or a
soundness break. On one, the controller drives fix → re-review / ripple-check until
stable (cap 4 rounds). One pass is not enough when the fix can introduce a new issue.
If still unstable after 4 rounds, escalate to the operator and park the item `unclear`
in `priorities.md`.

## Audit techniques (formalisation gates)

Reusable methods for auditing a "derived" formalisation gate (distilled from auditing
"derived-on-a-stratum" identities):

- **Disprove circularity by going OFF the stratum.** For a gate of the form "derived
  `X = Y` on a stratum" — where the claim is that one side is a *genuinely fixed* object, not a
  definitional alias of the other — evaluate both sides **off** the stratum: a genuine fixed object
  must **disagree** there. If they agree everywhere, the on-stratum `EqOn` is a vacuous `rfl` and the
  gate is hollow. (E.g. a quantity defined relative to a *fixed* combinatorial datum — an orbit label,
  a rank pattern — must mis-predict for an input whose true datum differs; build such an input and show
  the values differ.) This is the single most important check for a "derived not assumed" claim.
- **Non-vacuity is a *separate* check from soundness.** An `EqOn` / branch identity over a
  possibly-**empty** stratum is still a sound identity but carries no content. A "genuine
  stratum" claim needs an in-file witness `x ∈ S` for the **exact** stratum the theorem uses
  (a strict-interior witness, not a boundary/degenerate point). Check the *named* witness actually
  lands in that stratum — it may belong to a different one.
- **Watch `rfl`-after-rewrite "theorems."** A fold that is `rfl` once a definition is unfolded is
  useful API, not independent content. Name the **load-bearing** theorem (the one with the real
  induction / the real algebra); don't bill its packaging as a separate result.
- **Precision cuts both ways.** `grep` docstrings against what theorems *actually exist* in
  the file — for **overclaim** ("instantiated" when deferred, "affine" when multilinear) and
  for **stale underclaim** ("deferred/remaining" after the result has landed). The recurring
  real finding across these audits was prose precision, not broken math.
- **Operational.** Read the **Lean** exit code, not a trailing `echo $?` (the echo's exit
  masks lean's — a failing `example` can read as a pass under a truncated tail). To audit a
  committed target while the shared tree is build-red, copy the committed defs into a
  self-contained scratch `.lean` under `$CLAUDE_JOB_DIR/tmp` (no import of the broken
  module), probe there, then `#print axioms` on the real theorem once green. **Decorrelate
  every gate with a Codex consult** (`local-codex-consult`, xhigh, read-only) — independent
  reasoning repeatedly caught false positives and prose imprecision.
- **Re-run cited scripts; never trust a relayed headline.** A script or numerical certificate cited in
  support of a claim must **reproduce its stated verdict on a clean re-run** — re-run it yourself. Watch for
  the self-contradicting reproducer: a script that **grid-reconstructs / re-samples a *different* object** than
  the one claimed (e.g. picks a maximal-rank instance instead of *pinning the exact* config) and then prints a
  verdict its own recomputation refutes. Pin the exact inputs; a script whose re-run contradicts its printed
  headline is the runtime analogue of a vacuous theorem ([`bedrock.md`](bedrock.md) §Non-vacuity).

Domain-specific crux checks (e.g. for the quiver-orbit core: orbit ↔ Kostant-partition is a genuine
bijection, not a re-encoding; the rank-pattern ↔ multiplicity inclusion-exclusion inverts; the
`Ext(M,M)` count matches the orbit's normal-slice codimension) live with the domain conventions in
[`../../lean/CLAUDE.md`](../../lean/CLAUDE.md).
