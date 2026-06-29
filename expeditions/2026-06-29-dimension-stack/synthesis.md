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
  (finite-type-domain catenary L4d + closed-point corollaries).
- **2026-06-29 — R3 LANDED + PASS** (`f3670561`). New `Core/Dimension/AffineDomain.lean` (a deliberate split
  from `Catenary` — distinct Mathlib home for f.g.-algebra dimension theory): headline
  `affine_domain_height_add_ringKrullDim_quotient_eq` (`height p + dim(A/p) = dim A`, any finite-type domain,
  **any field** — no closure/char/cardinality; `@[stacks 00OS]`) + closed-point corollaries + the new general
  brick `height_under_eq_of_isIntegral` (integral height transport). Reuses R2 catenary as a black box (no
  re-induction). Peer crux-audit (separate session) **PASS-with-notes** (6/6, no hole; minor: 00OS headline is
  a restatement, 5 longLines → folded into R4). **Three catenary rungs stand.** Resource-aware: R3's
  full-aggregator re-gate is **bundled into R4's green-gate** (R4 edits `AffineDomain` for the cosmetics +
  imports the whole library). → R4 dispatched (the R0-pinned field-general codim bridge).
- **2026-06-29 — R4 LANDED + ENTRY-1 COMPLETE** (`2a610f8f`). Field-general codimension bridge extracted to
  `Core/Dimension/Codimension.lean` at `[Field k][Finite σ]` (no closure — R0's split realised): `varietyDim`,
  `height(vanishingIdeal Z) + varietyDim Z = card`, the Zariski-irreducible↔prime characterisation,
  `vanishingIdeal_isRadical` (docstring fixed: no-nilpotents, not strong-Nullstellensatz). The `[IsAlgClosed]`
  non-vacuity layer + DLN `codimRep_*` consumers stay in `NullstellensatzCodim` (re-`export`); `vanishingIdeal_univ_eq_bot`
  weakened `[IsAlgClosed]→[Infinite k]`. Reviewer PASS 6/6 + Codex CLEAN; controller re-gate green **3820**,
  axiom-clean. **★ The affine dimension stack is COMPLETE** — `DLNFibre.Core.Dimension.{Integral,Basic,Catenary,AffineDomain,Codimension}`,
  the any-field Mathlib-grade headline (integral-dim invariance + catenary equality + f.t.-domain dimension
  formula + height↔dim codim bridge), all Mathlib-absent at v4.29. **A coordination hazard surfaced + was
  caught benign** (see L3): the R3 formaliser returned post-push for a follow-up + `git reset` while R4 ran in
  the same worktree; committed history stayed clean (per-rung push) and R4's build-gate caught the race (green
  3820 — Lean won't compile a tangled file). → **Entry-2** next: E1 (étale local-dim bridge) → E2 (smooth ⟹
  regular, the `[IsAlgClosed]→[PerfectField]` win), then RF (consumer retrofit).
- **2026-06-29 — E1 LANDED** (`614b8838`). Entry-2 foundation: `Core/Dimension/Smooth.lean` (Mathlib mirror
  `RingTheory.Smooth.Regular`) — `Ideal.height_eq_under_of_etale` (étale preserves height) +
  `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` (smooth-point local Krull dim via the
  étale-over-affine-space route, **non-circularity preserved** — no cotangent identity). Verbatim re-home,
  **no closure hypothesis at E1** (the `[IsAlgClosed]→[PerfectField]` framing belongs to E2's
  `SmoothPointRegular`). L2 sweep caught the `FibreSmoothBlock` transitive bite. Re-gate green 3819,
  axiom-clean; E1 was **L3-clean** (committed, pushed, stopped). → E2 dispatched (the entry-2 capstone +
  `[IsAlgClosed]→[PerfectField]` generalisation — flagged crux, will get a decorrelated review).
- **2026-06-29 — E2 LANDED → ENTRY-2 CONTENT-COMPLETE** (`b9affa4a`). The capstone
  `smooth_point_isRegularLocalRing [PerfectField k]` (`@[stacks 00TV]`) + cotangent-finrank companion →
  new `Core/Dimension/Regular.lean`; local Krull dim from E1's non-circular bridge (no cotangent identity).
  **Honest surprise on the "crux":** the `[IsAlgClosed]→[PerfectField]` weakening was **already banked** in a
  prior rlct-bridge commit (`0084b645`) — the source already carried `[PerfectField]`. So E2 = independent
  verification (per-lemma trace: the lone field-theoretic input is `FormallySmooth.of_perfectField`,
  `[PerfectField]`-only) + clean re-home + dropping the vestigial `IsAlgClosed.Basic` import (green build
  confirms). A Bayesian update: the anticipated work was already done; the value was confirming + cleaning it.
  Re-gate green 3819, axiom-clean; E2 L3-clean. **The dimension stack (entry-1 + entry-2) now stands: 7
  Mathlib-grade modules `Core.Dimension.{Integral,Basic,Catenary,AffineDomain,Codimension,Smooth,Regular}`.**
  Capstone audit (08r) in flight; on PASS → RF (consumer retrofit + all cosmetics) → close.**
