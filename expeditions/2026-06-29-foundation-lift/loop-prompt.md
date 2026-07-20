# Controller loop — `foundation-lift`

> One tick per firing. The hourly cron fires: *"Controller tick — foundation-lift expedition. Run ONE tick
> per loop-prompt.md."* Operate from the `expedition/foundation-lift-*` worktree
> (`.claude/worktrees/foundation-lift`). Stay **blind** to `expedition/aoyagi-full`.

## Disposition (hold this)
**Build the buildable** ([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)):
all P1/P2/P3 content is already-green, well-established, Mathlib-absent — lift to Mathlib-grade. Foundation-first,
generalise-and-re-home, name=content, bedrock. Decorrelated-review the three crux rungs.

## Autonomous cadence (operator decision)
**Drive P1 → P2 → P3 to completion — do NOT pause for operator merges.** One PR per phase, opened as the phase
lands, for async review. **Stacked branches:** `-p1` off `origin/dev`; `-p2` off `-p1`; `-p3` off `-p2`
(conflict-free). Retarget a PR's base to `dev` once its predecessor merges.

## Per-tick
1. Read [`priorities.md`](priorities.md) (the phased ladder) + [`threads.md`](threads.md); check the active rung's teammate output.
2. **Integrate** a finished, reviewed rung: merge teammate worktree → the current phase branch; **re-gate** (`scripts/lb DLNFibre` foreground; sorry-free; `#print axioms` clean on new headlines + DLN payoffs unchanged).
3. **Dispatch the next ready rung** to a `lean-formaliser` (generalise-and-re-home; mirror the Mathlib target namespace; pre-flight the sibling-name-clash `rg`). One editor per shared worktree (serial); **L3** — only dispatch once the prior formaliser's completion notification has arrived.
4. **The crux rungs** (P1-R5 per-prime no-drop · P2-R2 minor-rank `←` · P3-R1 cokernel-finrank): route a decorrelated review (fidelity + Codex) before signing off.
5. **Phase boundary:** when a phase's rungs are all green+reviewed → open its PR (stacked base); update synthesis; **proceed to the next phase without waiting** (create `-pN+1` off the just-finished branch).
6. Update `priorities`/`threads`/`synthesis`; push to origin to bank. Apply **L2** (transitive sweep + full-build) and **L4** (codepoint longLine) every rung.

## Gates (every rung)
green build · sorry-free · axiom-clean `[propext, Classical.choice, Quot.sound]` · DLN payoff axioms unchanged · name=content · decorrelated review on the crux · sibling-clash gate cleared.

## Close
When P1+P2+P3 are landed (3 PRs open/merged) + exposition + synthesis: signal the operator the set is complete. PRs + merges are operator-gated (async).
