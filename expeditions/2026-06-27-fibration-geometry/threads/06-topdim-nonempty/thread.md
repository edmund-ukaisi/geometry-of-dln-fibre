# Thread 03 — S2c: close the smooth block's top-component residual (formalisation / tide)

**Target:** discharge the `I ∈ TopDimMinPrimes (sweepFibreRing …)` + `hI` hypotheses of
`FibreSmoothBlock.exists_smoothBlock_certificate`. Two deliverables: (1) `TopDimMinPrimes (sweepFibreRing
…)` nonempty under the kostant gate; (2) a CLOSED existence theorem (NO `I, hI`) composing (1) with the
per-component certificate.

**Status:** DELIVERED. Green, sorry-free, axiom-clean; fidelity-reviewed (PASS A–E).

## Route (as built)
- Found a far shorter route than the coheight-iSup sketch I consulted Codex on: the generic engine
  `topDimMinPrimes_nonempty` (nontrivial Noetherian ⟹ nonempty, NO finite-dim hypothesis) is
  ~25 lines, reusing banked `ringKrullDim_quotient_eq_coheight` (IntegralDimension.lean),
  `minimalPrimes.finite_of_isNoetherianRing`, `Set.exists_max_image`, `Order.coheight_anti`,
  `Order.krullDim_eq_iSup_coheight`, `ringKrullDim_quotient_le`.
- Spec-gate: `topDimMinPrimes_sweepFibreRing_nonempty` gets `Nontrivial (sweepFibreRing)` from banked
  `vanishingIdeal_sweepFibre_ne_top`; `IsNoetherianRing` auto-inferred.
- Closed: `exists_topComponent_smoothBlock_certificate` derives `hN` in-proof, `Infinite k` from
  `IsAlgClosed k`, then `exists_smoothBlock_certificate`.

## Consults
- `codex/route-{prompt,answer}.md` — design red-team (confirmed Noetherian+nontrivial suffices, no
  finite-dim hypothesis; the LTSeries route silently needs FiniteRingKrullDim). Superseded in part by
  finding the banked `ringKrullDim_quotient_eq_coheight`.
- `codex/topdim-soundness-{prompt,answer}.md` — reviewer's decorrelated soundness consult (PASS).

## Statement card
`statement-card.md` (status: sorry-free, fidelity-reviewed PASS).

## Controller wiring
`lean/DLNFibre.lean` must add `import DLNFibre.Core.FibreSmoothBlockExists` at the end (after
`import DLNFibre.Core.FibreSmoothBlock`). Aggregator NOT edited by this tide.
