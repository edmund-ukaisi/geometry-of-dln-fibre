# Lessons — `dimension-stack`

*L-numbered lessons accumulate here as they surface (transferable craft, not per-rung status).*

- **L0 — generalising surfaces holes.** Stripping a bespoke narrowing (`Tuple`/`Type 0`/`[IsAlgClosed]`) is
  not cosmetic: the exact minimal hypotheses are a finding, and the gaps the narrowing hid are the layer to
  fill. Confirm the boundary by a throwaway build (rung 0), not from docstrings alone.
- **L1 — over-assumed `[IsAlgClosed]` is common, and cheap to shed — but check each.** R0 found the DLN
  codim consumers carry `[IsAlgClosed]` the field-general core never needs (the bridge routes through
  `height_vanishingIdeal_*`, not the Nullstellensatz; `vanishingIdeal_isRadical` is a no-nilpotents proof,
  not strong-Nullstellensatz — its docstring was stale). Generalising = dropping a spurious hypothesis + a
  name=content docstring fix. But the *genuine* `[IsAlgClosed]` (zeroLocus↔radical) does **not** weaken to
  `[PerfectField]` — confirm per-lemma which closure use is real, don't assume uniformly.
- **L2 — re-homing a decl: sweep for *transitive* (unqualified) consumers, not just direct importers.** R1
  moved decls `DLNFibre.Core → DLNFibre.Core.Dimension`; one consumer (`FibreSmoothBlockExists`) used a moved
  decl *unqualified* without importing the old file — relying on the `DLNFibre.Core` namespace — and broke
  only in the **full-aggregator** build, not the direct-importer set. After a namespace move, grep every moved
  identifier across the whole library and full-build to catch these; fix with `open Dimension` (or qualify).
- **L3 — gate next-rung dispatch on the prior formaliser's COMPLETION notification, not a clean-tree
  snapshot.** R4 was dispatched into the shared worktree on a clean-`git status` read while the R3 formaliser
  was still alive; R3 then returned for a review-driven follow-up commit + a `git reset --mixed`, racing R4's
  git/working-tree state. **No damage resulted** — the committed history stayed clean (every rung is pushed
  immediately) and R4's strict build-gate caught the race as benign (green 3820; Lean won't compile a tangled
  file) — but the safe rule is to wait for the prior agent's completion notification before dispatching the
  next into the same shared worktree. The safety net that made it recoverable: **per-rung push + a strict
  build-gate + a clean committed base to fall back to.** (Root cause: the Uplift-B worktree-collapse — a
  worktree-based controller's teammates share one tree and must be strictly serialised.)
- **L4 — the `longLine` linter counts codepoints, not bytes.** RF found `awk length` (UTF-8 bytes) disagrees
  with the Lean `longLine` linter and Python `len(str)` (codepoints) on comment lines dense with wide chars
  (`≤`, `≃`, `★`, `⟹`, …). A line that passes a byte-count check can still trip the linter and vice versa —
  reflow against **codepoint** width (the linter's `:N:100` column is the binding target, not a byte count).
