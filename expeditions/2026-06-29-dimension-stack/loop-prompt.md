# Controller loop — `dimension-stack`

> One tick per firing. The hourly cron fires: *"Controller tick — dimension-stack expedition. Run ONE tick
> per loop-prompt.md."* Operate from the `expedition/dimension-stack` worktree
> (`.claude/worktrees/dimension-stack`). Stay **blind** to `expedition/aoyagi-full`.

## Disposition (hold this)

**Build the buildable** ([`../../CLAUDE.md`](../../CLAUDE.md) § Disposition;
[`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)): the dimension facts
are well-established, detail-at-scale, Mathlib-absent — build them to Mathlib grade; cite only the monuments.
**Foundation-first**: finalise the general core in `Core.Dimension.*`, then retrofit DLN consumers to tag to
it. Bedrock + name = content. Decorrelated-review the crux. Be more ambitious than the teammates.

## Per-tick

1. **Read** [`priorities.md`](priorities.md) (the rung ladder) + [`threads.md`](threads.md); check any active
   teammate's output (`TaskOutput` / its result).
2. **Integrate** finished, green-gated, reviewed rungs: merge the teammate worktree → `expedition/dimension-stack`;
   **green-gate** (`scripts/lb DLNFibre` foreground; sorry-free; `#print axioms` clean on new headlines).
3. **Dispatch** the next ready rung to a `lean-formaliser` — foundation-first (general core in
   `Core/Dimension/`, upstream-grade: Mathlib naming + docstrings + minimal hyps; generalise-and-re-home, not
   re-prove). One editor per shared worktree (serial); isolated worktrees only if genuinely parallel.
4. **Review the crux**: R2 monic-positioning, R4 the field-general/`[IsAlgClosed]` split, E2 the
   `[IsAlgClosed]→[PerfectField]` weakening — fidelity + hardener (+ decorrelated Codex) before trusting; the
   scout flagged R4/E2 as asserted-from-docstring, not trial-built.
5. **Update** `priorities.md` / `threads.md` / `synthesis.md`; **push** to origin to bank (pre-authorized for
   the expedition branch).
6. If **blocked on an operator decision**, surface it in **plain prose, non-blockingly** (never a blocking
   `AskUserQuestion` while teammates are active — it freezes the inbox) and continue other rungs.

## Gates

green build · sorry-free · axiom-clean `[propext, Classical.choice, Quot.sound]` · name = content ·
decorrelated review on the crux · **foundation-first** (no bespoke dimension proof left un-retrofitted at
close).

## Close

When R1–R4 + E1–E2 + retrofit (RF) land green/reviewed and the disposition docs are integrated: exposition +
synthesis; PR against `dev` (signal-and-wait — operator-gated).

## Roadmap residuals (NOT this expedition)

orbit-geometry capstone de-`Tuple` (recon entry 3); type-A Gabriel/`Ext` (4); q-series (5); the mathlib4
upstream PR process; package extraction (knowing decision).
