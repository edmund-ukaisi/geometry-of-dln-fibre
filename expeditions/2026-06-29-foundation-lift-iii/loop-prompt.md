# Controller loop — `foundation-lift-iii`

> One tick per firing. The hourly cron fires: *"Controller tick — foundation-lift-iii expedition. Run ONE tick
> per loop-prompt.md."* Operate from the `expedition/fl3-*` worktree (`.claude/worktrees/fl3`). Stay **blind**
> to `expedition/aoyagi-full`.

## Disposition (hold this)
**Build the buildable** ([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)):
the differential-algebra interface (Phase 1) is ~70% already-green + DLN-free — re-home / consolidate /
extract-V3 / name-hygiene, Mathlib-grade. Phase 2 (the orbit-dimension **squeeze** — recalibrated, NOT
`dim G − dim Stab`) is a genuine de-`Tuple` refactor, **probe-gated**. Foundation-first, generalise-and-re-home,
name=content, bedrock. Decorrelated-review the crux rungs.

## Autonomous cadence (operator decision)
**Drive Phase 1 → Phase 2 to completion — do NOT pause for operator merges.** One PR per phase, opened as the
phase lands, for async review. **Stacked branches:** `fl3-p1` off `origin/dev`; `fl3-p2` off `fl3-p1`
(conflict-free). Retarget a PR's base to `dev` once its predecessor merges.
**Phase-2 gate:** P2.0 is a de-`Tuple` probe — **default proceed** on a positive probe; **halt + surface to the
operator** only if it shows the argument is irreducibly `Tuple`-shaped (then Phase 1 ships alone).

## Per-tick
1. Read [`priorities.md`](priorities.md) (the phased ladder) + [`threads.md`](threads.md); check the active rung's teammate output.
2. **Integrate** a finished, reviewed rung: merge teammate worktree → the current phase branch; **re-gate** (`scripts/lb DLNFibre` foreground; sorry-free; `#print axioms` clean on new headlines + DLN payoffs unchanged).
3. **Dispatch the next ready rung** to a `lean-formaliser` (generalise-and-re-home; mirror the Mathlib target namespace; pre-flight the sibling-name-clash `rg`). One editor per shared worktree (serial); **L3** — only dispatch once the prior formaliser's completion notification has arrived.
4. **The crux rungs** (P1.2 char-hyp · P2.4 + P2.5 the de-`Tuple` refactor): route a decorrelated review (fidelity + Codex) before signing off. P2.0 probe de-risks P2.4/P2.5 first.
5. **Phase boundary:** when a phase's rungs are all green+reviewed → open its PR (stacked base); update synthesis; **proceed to the next phase without waiting** (create `fl3-p2` off `fl3-p1`). At the Phase-1→2 boundary, run/inspect the P2.0 probe before committing to the P2 refactor.
6. Update `priorities`/`threads`/`synthesis`; push to origin to bank. Apply **L2** (transitive sweep + full-build), **L4** (codepoint longLine), **L5** (re-gate at boundaries + crux, not every low-risk re-home) every rung.

## Gates (every rung)
green build · sorry-free · axiom-clean `[propext, Classical.choice, Quot.sound]` · DLN payoff axioms unchanged · name=content (object-eq vs `finrank`-eq; 3 base-change-rank variants distinct; char hyps explicit) · decorrelated review on the crux · sibling-clash gate cleared.

## Close
When Phase 1 (+ Phase 2, or Phase 2 honestly recorded as `Tuple`-blocked) are landed + synthesis: signal the operator the set is complete. PRs + merges are operator-gated (async).
