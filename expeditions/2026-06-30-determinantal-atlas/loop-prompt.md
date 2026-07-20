# Controller loop — `determinantal-atlas`

> One tick per firing. The hourly cron fires: *"Controller tick — determinantal-atlas expedition. Run ONE tick
> per loop-prompt.md."* Operate from the `expedition/det-atlas-*` worktree (`.claude/worktrees/det-atlas`).
> Stay **blind** to `expedition/aoyagi-full`.

## Disposition (hold this)
**Build the buildable** ([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)):
standard determinantal algebraic geometry (rank loci, Schur, localization cocycles) as a clean, **constructive**,
Mathlib-grade `Core` library; DLN rank-loci become instances. Foundation-first, generalise-and-re-home,
name=content, bedrock. **Constructive-first** (explicit pivot atlas over abstract existence). Decorrelated-review
the crux rungs (P2.c cocycle, P2.d bridge).

## Autonomous cadence (operator decision)
**Drive P0 recon → Phase 1 → Phase 2 to completion — do NOT pause for operator merges.** One PR per phase, opened
as the phase lands, for async review. **Stacked branches:** `det-atlas-p1` off `origin/dev`; `det-atlas-p2` off
`-p1`. Retarget a PR's base to `dev` once its predecessor merges (GitHub auto-retargets only if the base branch
is deleted on merge — else `update_pull_request base=dev` manually).
**Capstone gate:** P2.d (bare `FiberBundle`) is recon-gated — **build if the residue-field-rank bridge is
detail-at-scale; if it is a monument, ship atlas+cocycle as the honest ceiling + roadmap the bare-bundle leap.**

## Per-tick
1. Read [`priorities.md`](priorities.md) + [`threads.md`](threads.md); check the active rung's teammate output.
2. **Integrate** a finished, reviewed rung: merge teammate work → the current phase branch; **re-gate** (`scripts/lb DLNFibre` from `lean/`, foreground; sorry-free; `#print axioms` clean on new headlines + DLN payoffs unchanged).
3. **Dispatch the next ready rung** to a `lean-formaliser` (generalise/re-home; mirror the Mathlib target namespace — **bare namespace per L7**; pre-flight the sibling-clash `rg`). One **builder/committer** per shared worktree (serial); **L3** — only dispatch once the prior formaliser's completion notification has arrived. Read-only auditors may run alongside one builder.
4. **The crux rungs** (P2.c cocycle compatibility · P2.d residue-field-rank bridge): route a decorrelated review (fidelity + non-vacuity witness + Codex) before signing off. The P0 recon de-risks both first (the build-vs-cite verdict).
5. **Phase boundary:** when a phase's rungs are all green+reviewed → controller authoritative re-gate (full build + sorries + axioms) → open its PR (stacked base) → proceed to the next phase without waiting.
6. Update `priorities`/`threads`/`synthesis`; push to origin to bank. Apply **L2** (transitive sweep + full-build), **L4** (codepoint longLine), **L5** (re-gate at boundaries + crux), **L6** (instance-import after splits), **L7** (bare namespace), **L8** (GUARD-first when abstracting) every rung.

## Gates (every rung)
green build · sorry-free · axiom-clean `[propext, Classical.choice, Quot.sound]` · DLN payoff axioms unchanged · name=content (rank-`=r` vs `≤r`; constructive vs existence; object-eq vs dim-eq) · decorrelated review on the crux · sibling-clash gate cleared · namespace bare-Mathlib-mirror.

## Close
When Phase 1 + Phase 2 are landed (PRs) + the RLCT programme is in `ROADMAP.md` + synthesis: signal the operator
the set is complete. PRs + merges are operator-gated (async).
