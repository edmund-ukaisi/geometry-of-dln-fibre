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
