# lessons — explicit `(C, θ)` for arbitrary `d`  (append-only)

Methodological learnings; directed-suspicion seed for the controller tick.

- **(setup) Fresh worktree build.** A `git worktree add` checkout has no `.lake`, so it needs
  `lake exe cache get` + `lake build` — and these must run from the `lean/` subdirectory (the lakefile
  is `lean/lakefile.toml`), not the worktree root. First baseline-build attempt failed by invoking
  `lake` from the worktree root (`no configuration file with a supported extension`).
- **(setup) Controller-in-worktree.** This expedition's controller runs from a worktree, so teammate
  `isolation: worktree` collapses onto the shared worktree (serial, one editor) — acceptable for a
  single formaliser tide. True per-teammate isolation needs the controller in the main checkout, which
  is unavailable (occupied by the live aoyagi expedition). [→ ROADMAP "Process / harness uplift".]
- **(tide) `Tuple.sort` is not kernel-reducible** (routes through `Multiset.sort`), so `decide +kernel`
  on `cValue (d ∘ Tuple.sort d)` is impossible. The witness instead proves `d ∘ Tuple.sort d` equals a
  concrete monotone vector (here `![2,3,2] ∘ sort = ![2,2,3]`) via `Tuple.comp_sort_eq_comp_iff_monotone`
  applied to the explicit sorting permutation, then `decide +kernel` on the concrete vector. The
  `Monotone (d ∘ Tuple.sort d)` fact is `Tuple.monotone_sort`.
- **(process) The formaliser self-spawned its own reviewer** instead of `REQUEST_SPAWN` to the
  controller (leaf executors should not spawn — `expedition.md` §Architecture). Harmless here (the
  decorrelated reviewer + Codex added real value — caught the redundant `hr` hypothesis), and the
  controller still ran an independent green-gate + precision/bedrock read. Going forward: instruct the
  seat to `REQUEST_SPAWN` so the controller commissions the audit (keeps the gate controller-owned).
