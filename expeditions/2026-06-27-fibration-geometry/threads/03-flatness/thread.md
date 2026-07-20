# Thread 03 — S3 flatness payoff

**Target.** Register the flatness of the DLN fibre family over the rank-`= r` open, + corollaries.
Settle the cheap-flatness kill-condition (is flatness cheap without the charts?).

**Outcome.** Landed `DLNFibre.Core.FibreFlatness` (`lean/DLNFibre/Core/FibreFlatness.lean`):
6 headlines, sorry-free, axiom-clean. See `statement-card.md`.

## Cheap-flatness verdict (the kill-condition)

Settled inside the build, Codex-consulted (`codex/cheap-flatness-{prompt,answer}.md`, decorrelated):

- The literal "structure map of the bundle's coordinate ring over the base" splits into TWO
  genuinely-different maps:
  1. **chart inclusion** `Base → Total` — a localization, flat for free (`Localization.flat`),
     independent of the Schur charts / rank bridge. CHEAP, but the open-chart-inclusion fact, NOT the
     bundle payoff.
  2. **fibre-family projection** `SchurLoc → SchurLoc ⊗_k sweepFibreRing` — the genuine bundle
     flatness; the standard model is FREE over `SchurLoc` (`Module.Free.tensor`), hence flat. Needs
     the atlas (it is about the trivialized fibre), then cheap.
- **Miracle/generic flatness is the WRONG route** (Codex). No CM/regular/equidim input used; no
  generic-flatness dense-open used. Both flatness facts are cheap once the right map is identified.

So: flatness IS cheap, but the cheap-and-easy reading (localization) is not the load-bearing one. The
load-bearing bundle flatness is the standard-model freeness, routed through the atlas trivialization.

## Route

1. SPECIFY skeleton (4 theorems, 2 sorry) — signatures validated.
2. Pinned API in a scratch file (deleted): `Localization.flat`, `Module.Free.tensor`,
   `Module.Flat.of_free` — all fire.
3. Proved scheme-level `Flat` via `HasRingHomProperty.Spec_iff (P := @Flat)` +
   `RingHom.flat_algebraMap_iff`.
4. Proved `UniversallyOpen` via `UniversallyOpen.of_flat` (`LocallyOfFinitePresentation` from
   `Algebra.FinitePresentation.baseChange` of the fp `k`-algebra `sweepFibreRing`).
5. Added the atlas-connection witness tying the payoff to the actual per-pivot chart ring.

## Honest gaps (named in-file + card)

- Global flatness over all of `rankROpen` (one morphism) needs R1 target-overlap gluing. Stated
  chartwise.
- `rankAtStalk` locally constant does NOT apply: the fibre has positive dimension, so the family is
  not a finite module / vector bundle. `UniversallyOpen` is the corollary that does apply.

## Consults

- `codex/cheap-flatness-{prompt,answer}.md` — the cheap-flatness verdict + statement-shape ranking.
  Reshaped the target: the bundle payoff is the fibre-family projection (standard-model flatness),
  not the localization, and not a different/harder object.

## Review outcome (fidelity) — de-escalation actioned

Reviewer (+ decorrelated Codex) returned PASS-WITH-NOTES with one MAJOR finding: the original
"THE BUNDLE FLATNESS PAYOFF" framing of `standardFibreModel_flat` OVERCLAIMED.

- `SchurLoc ⊗_k sweepFibreRing` free over `SchurLoc` is **generic base change** (any `k`-algebra; no
  DLN geometry); `SchurLoc` is the in-chart auxiliary ring, NOT the bundle base.
- The atlas trivialization is only `≃ₐ[k]`, so the model flatness does NOT transport to the chart
  ring — exactly the gap the target-setting Codex consult named. The brief's S3 target
  (`Flat π : mult⁻¹(rankROpen) → rankROpen`) is therefore **NOT delivered**; the missing rung is the
  `SchurLoc`-linear trivialization.

Actioned (Lean math unchanged, framing corrected): module header rewritten with an explicit
"S3 TARGET NOT MET — blocker" section; `standardFibreModel_{free,flat}` docstrings de-escalated to
"over the auxiliary `SchurLoc` / generic base change"; scheme theorems renamed
`flat_specMap_standardFibreModelOverSchur` / `universallyOpen_…OverSchur`; atlas-connection witness
reworded as "two separate facts, `k`-linear link only"; gaps reordered with the missing
`SchurLoc`-linear trivialization as the PRIMARY blocker. Card updated to match.

**Honest status:** the cheap-flatness verdict is settled and the two true side-facts + `UniversallyOpen`
corollary are landed (green, sorry-free, axiom-clean). The S3 fibre-family flatness over the base is
OPEN, blocker named. This is a verdict-and-side-facts deliverable, not the S3 payoff.

## Controller wiring

`lean/DLNFibre.lean` needs `import DLNFibre.Core.FibreFlatness` appended (single-writer; not edited
here).
