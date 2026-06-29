# Synthesis — `dimension-stack`

*Accumulates as rungs land. Opening shape: [`brief.md`](brief.md) + [`priorities.md`](priorities.md).*

The programme's first **Mathlib-foundation build**: grow the affine dimension stack (catenary +
integral-extension invariance + height↔dim codimension bridge) and the smooth ⟹ regular-local stack — built
bespoke inside `DLNFibre.Core`, Mathlib-absent — into clean, general, Mathlib-grade reusable libraries under
`DLNFibre.Core.Dimension.*`, then retrofit the DLN consumers to tag to them.

## Tick log

- **2026-06-29 — kickoff.** Worktree `expedition/dimension-stack` off `dev` `65b6e729`; shared lake store
  reused. Disposition docs folded in (`docs/policies/library-building.md`; CLAUDE.md "Build the buildable"
  bullet; controller.md "Makes the build-vs-cite call"; README/bedrock kin). Rung-0 de-risk launched +
  Mathlib in-flight check. Hourly controller-loop cron set.
- **2026-06-29 — R0 (gate) PASSED.** De-risk probe confirmed `NullstellensatzCodim`'s catenary/codimension
  core is field-general (exact minimal hyps `[Field k] [Finite σ]`; `[CharZero]` absent; axiom-clean). Clean
  **3-band split** pins R4 (field-general core → `Core.Dimension.Codimension`; a thin `[IsAlgClosed]`
  geometric/non-vacuity layer that feeds no core theorem; DLN consumers retrofit). Two findings: the DLN
  consumers' `[IsAlgClosed]` is **provably dead weight** (RF generalisation win), and the
  `[IsAlgClosed]→[PerfectField]` win is an **E2-only** concern (the codim bridge never carries it). Mathlib
  in-flight check: `IsCatenary` absent + community-planned (build-worthy/upstream-worthy); regular local
  rings recently landed (entry-2 foundation). Ladder commits → **R1 dispatched** (integral-extension
  dimension invariance → `Core.Dimension.Integral`).
- **2026-06-29 — R1 LANDED** (`f447c0ce`). Integral-extension dimension invariance re-homed to the new
  `DLNFibre.Core.Dimension` namespace: `Dimension/Integral.lean` (headline
  `ringKrullDim_eq_of_integral_injective`, `@[stacks 00OK]`; supports incl. the `@[stacks 00OJ]` injectivity-
  free `≤` half and the `@[stacks 00GU]` going-up chain-lift) + `Dimension/Basic.lean` (polynomial-over-field
  + quotient/coheight). All 9 decls byte-identical statements (diff = namespace + docstrings + stacks tags);
  8 consumers re-pointed; old file deleted. Green 3819 / sorry-0 / axiom-clean; reviewer + decorrelated Codex
  PASS. **The first rung of the Mathlib-grade dimension stack stands.** Next: R2 (polynomial-ring catenary +
  monic positioning).
- **2026-06-29 — R2 LANDED** (`574a9056`). Polynomial-ring catenary re-homed to `Core/Dimension/Catenary.lean`
  (482 lines): headline `height_add_ringKrullDim_quotient_eq` (`height p + dim(R/p) = n` for `R = k[Fin n]`,
  any field; `@[stacks 00OS]`) + `primeHeight`/coheight forms + the monic-positioning crux
  `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit` (`@[stacks 00OX]`). **Crux handled:** Mathlib's `private`
  Noether-normalization substitution re-derived in-repo (visibility-only verbatim copy, Provenance-documented;
  no public v4.29 route — Codex xhigh confirmed the call + the any-field generality, char/cardinality-free,
  no `IsAlgClosed`). `NoetherMonicPositioning` deleted, `PolynomialDimension` trimmed to its non-catenary
  fact, 7 consumers + aggregator re-pointed (4 were **transitive/unqualified** — L2 trap, caught by the
  full-build sweep). Green 3819 / sorry-0 / axiom-clean. **Controller re-gate + an independent decorrelated
  crux-review (verbatim-copy fidelity + any-field soundness) in flight before R3.
- **2026-06-29 — R2 SIGNED OFF.** Controller re-gate PASS (3819 green); independent crux-review
  **PASS-with-notes** — verbatim private-substitution copy is byte-faithful (only `T` de-privatised, helpers
  stay private), the any-field generality is sound (zero closure/char/cardinality hypotheses anywhere). Two
  non-blocking cosmetics (statement-card tag-claim overstates `@[stacks]` attributes that are prose in code;
  two dangling `§` cross-refs in `Catenary.lean`) folded into R3. **Catenary rung stands.** → R3 dispatched
  (finite-type-domain catenary L4d + closed-point corollaries).**
