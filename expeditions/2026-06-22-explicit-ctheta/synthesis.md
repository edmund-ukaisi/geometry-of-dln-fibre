# synthesis — explicit `(C, θ)` for arbitrary `d`  (controller's internal ground)

*Internal integrative read + drift-guard; assumes repo context. Not the deliverable.*

## Current read (2026-06-22, setup)

Opened off `dev` (`7854591`) immediately after PR #6 (perm-invariance) merged. Central question:
lift the `Monotone d`-gated explicit closed-form `(C, θ)` (`cValue`/`cTheta`, Thm 7.10) to an
**arbitrary** dimension vector, by composing the just-merged sort bridge with it.

**Bricks (all landed on `dev`, signatures verified):**

- `cCodim_eq_qipMin` (`CThetaQIPConverse:833`), `qipMin_eq_cValue` (`CThetaValue:582`) — `Monotone d`, `r=0`.
- `numTop_zero_eq_cTheta` (`CThetaThetaBridge:146`) — `Monotone d`, `r=0` (the θ bridge; already exists).
- `cCodim_comp_sort` / `numTop_comp_sort` (`CThetaPermInvariance:122/129`) — any `d` → monotone rearrangement.
- `cCodim_rankShift` / `numTop_rankShift` (`CTheta:377/397`) — general `r` → `r=0`.
- `kostantPartitions_nonempty_of_le` (`CCodimCornerMono`, added last expedition) — `1≤N` + `r≤min d` ⟹ nonempty.
- `kostant_nonempty_iff_qipFeasible_nonempty` (`CThetaThetaBridge:63`) — QIP-feasibility ↔ kostant nonempty (`Monotone d`).

**Route** is fully pre-scoped (see `brief.md`). **Open uncertainties:** the Mathlib lemma name for
`Monotone (d ∘ Tuple.sort d)`; discharging `(qipFeasible (sorted)).Nonempty` for the composition.

## Process

Controller is **in a worktree** (`explicit-ctheta`) ⟹ teammate `isolation: worktree` collapses onto
this shared worktree (serial, one editor at a time — per `expedition.md` §Isolation). For a single
formaliser tide that is fine. Baseline build warming (fresh worktree had no `.lake`). One tide
(thread 01) → review → ROADMAP refresh → close (PR to `dev`, signal-and-wait).

## Drift guard

Bundle-1 / `Core`-only. No `DLNFibre.DLN` import; nothing named `rlct_`. **No collision with the live
aoyagi expedition** (Bundle 4 / RLCT analytic, running in the main checkout).

## Close (2026-06-23)

**Central question answered.** `Core.CThetaArbitrary` (new, aggregated at `DLNFibre.lean:82`) gives the
explicit closed-form `(C, θ)` for an **arbitrary** dimension vector, dropping the `Monotone d` gate:

- `cCodim_zero_eq_cValue_comp_sort` / `numTop_zero_eq_cTheta_comp_sort` (`r = 0`);
- `cCodim_eq_cValue_comp_sort` / `numTop_eq_cTheta_comp_sort` (general `r`): `cCodim d r = cValue ((d−r)∘sort)`, `numTop d r = cTheta ((d−r)∘sort)` — `hr` derived from `h` (weakest hypotheses);
- non-monotone witness `(2,3,2)`: `cCodim = cValue∘sort = 4`, `numTop = cTheta∘sort = 2`.

**AUDIT cleared** (proportionate for a thin composition of merged+reviewed bricks): controller
independent green-gate (whole-library `lake build` green 3696 jobs; `scripts/sorries` 0; `#print axioms`
→ `[propext, Classical.choice, Quot.sound]` on all new theorems) + controller precision/bedrock read
(no hidden `Monotone`; name = content; non-vacuous witness shown in-file) + the tide's decorrelated
reviewer + Codex fidelity pass (which also hardened the `hr` drop). No third redundant pass commissioned.

**ROADMAP refresh done** (Bundle 1 / Bundle 3 status corrected to Proved post-PR #6; the
arbitrary-`d` result added; the Process/harness uplift section added).

**Process note:** the formaliser self-spawned its reviewer (off the leaf-executor rule) — logged in
`lessons.md`; harmless here.

**Remaining:** exposition section (perm-invariance chapter); commit; signal-and-wait before PR.
