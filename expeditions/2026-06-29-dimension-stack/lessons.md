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
