# priorities.md — Aoyagi-Full taste ledger

Controller proposes (VOI × directed-suspicion); operator edits directly (highest-authority signal).
Nothing unranked; "unclear-but-keep-going" is first-class.

## Now (ranked)

1. **[pursue] Rung 0 — pin the goal skeleton + foundational definitions.** Highest VOI: every later
   rung stands on `rlctAt`/`rlctOrderAt`/`dlnLoss`/`aoyagiλ`. Get the *math* of the definitions exactly
   right (controller architects in `synthesis.md`/brief), delegate Lean encoding, then **independent
   fidelity review against numerical ground truth** before building upward. Conceptual slop here poisons
   everything (green build proving the wrong thing).
2. **[pursue] Def-3 well-definedness.** Decide & prove: `aoyagiλ` via the minimisation (total); printed
   Theorem-2 form equal where Def 3 applies. Pin whether Def 3 selects a unique set always, or only on a
   characterised regime. (Known trap — see `lessons.md`.)
3. **[pursue] Choose the smallest end-to-end validation case.** Candidate: single matrix (L=1) for the
   pure RLCT-from-resolution machinery, then L=2 reduced-rank r=0 (2,1,2)/(2,2,2). The whole ladder must
   close top-to-bottom on it before generalising.
4. **[park-unclear] D1 / Theorem 4 scope.** Read Aoyagi 2013 (`entropy-15-03714.pdf`); scope exactly what
   the deepest-singular-point reduction needs. Don't over-formalise the 2013 paper — only the lemma D1 uses.
5. **[park-unclear] R1 cost.** The resolution is the mountain; the small-case validation (item 3) is the
   probe that tells us its true cost. Hold detailed R1 planning until one case's charts are built by hand.

## Watching (suspicion / risks)

- Treadmill recurrence (the prior expedition's mode) — guardrail: sorry-count must trend down; every file
  on the critical path to a named sorry.
- Definitional infidelity — guardrail: review defs against ground truth before building up.
- Build-time blow-up — guardrail: small modules, background builds, tactic hygiene.

## Operator notes

(empty — operator injects here)
