# Statement card — R5 bundle completion: projection compatibility + target-side transition object

> **Claim (1, projection compatibility — the S5/S4b open item (i), CLOSED).** The in-chart base map
> `schurToDsigAt : SchurLoc →ₐ[k] Away (chartDsigAt s t)` (the named structure map over which the S4b
> over-base trivialization + flatness live) **is `mult`'s comorphism**, gauge-transported. Precisely, as
> an equality of `k`-algebra homs `MvPolynomial SchurVar k → Away (chartDsigAt s t)`:
>
>     schurToDsigAt ∘ localizeSchur
>       = awayCongr(gauge) ∘ phiSourceHom ∘ multComap ∘ targetSchurEmbed
>
> where `targetSchurEmbed` embeds a target Schur-block coordinate as the matching target matrix entry
> variable, `multComap` is `mult`'s comorphism (`Core.MultComorphism`), `phiSourceHom` descends-and-
> localizes to the chart, and `awayCongr(gauge)` is the pivot gauge transport. So the over-base direction
> is the geometric multiplication map on the Schur block, not an artificial chart base map.
>
> **Claim (2, target-side transition OBJECT — R1 partial).** The genuine target-side overlap transition
> exists, pairwise: a double-localized `k`-algebra iso `targetProductOverlapTransition I J :
> targetChartLoc I J ≃ₐ[k] targetChartLoc J I` on the standard fibre model `M = SchurLoc ⊗_k
> sweepFibreRing`, transported from the base-side overlap through the per-pivot trivializations. Its
> **round-trip cocycle** is a precisely-named residual (math-immediate, Lean-infra-blocked — see below).
>
> - **Lean (1, projection compatibility).**
>   - `DLNFibre.Core.chartPhiSchurAeval_eq_comp_multComap`
>   - `DLNFibre.Core.schurToDsig_comp_localizeSchur` (top-left chart)
>   - `DLNFibre.Core.schurToDsigAt_comp_localizeSchur` (every pivot)
>   - `DLNFibre.Core.ProjCompatOverBaseChart` + `DLNFibre.Core.projCompatOverBaseChart` (bundles
>     projection-compat + the S4b over-base `≃ₐ[SchurLoc]` triv + flatness)
>   - file: `lean/DLNFibre/Core/FibreProjectionCompat.lean`
> - **Lean (2, target-side transition object).**
>   - `DLNFibre.Core.awayCongr'` (generalized localization transport of an `AlgEquiv` between different
>     algebras — reusable brick; the banked `awayCongr` needs `A ≃ₐ A`)
>   - `DLNFibre.Core.overlapElt` / `targetChartLoc` / `overlapTriv` (the base→target transport)
>   - `DLNFibre.Core.chartOverlapTransitionK` + `chartOverlapTransitionK_trans_symm` (k-restricted base
>     transition + its round-trip)
>   - `DLNFibre.Core.targetProductOverlapTransition` (the target-side transition object)
>   - file: `lean/DLNFibre/Core/FibreTargetOverlap.lean`
>
> - **Gloss.**
>   - `localizeSchur` is the canonical `MvPolynomial SchurVar k →ₐ[k] SchurLoc` localization hom.
>   - `chartPhiSchurAeval_eq_comp_multComap` is the crux: the Φ Schur comorphism (`aeval chartPhiVarSub`)
>     equals `phiSourceHom ∘ multComap ∘ targetSchurEmbed` — because `chartPhiVarSub` is DEFINED to read
>     off `multPoly` (the generic product = the coordinate-ring image of `mult`), so on a generator
>     `X s` the RHS is `phiSourceHom (multComap (X (schurVarToEntry s))) = phiSourceHom (multPoly …) =
>     chartPhiVarSub s` (`multComap_X` + `phiSourceHom_multPoly`). This is what makes the result genuine
>     geometry of `mult` rather than a vacuous restatement over the named base map.
>   - `targetProductOverlapTransition I J = (overlapTriv I J).symm ≪≫ chartOverlapTransitionK I J ≪≫
>     overlapTriv J I` — conjugating the base-side overlap cocycle through the two per-pivot
>     trivializations onto the product model.
>
> - **Proved (unconditionally), axiom-clean.** All of claim (1), and the transition OBJECT + base
>   round-trip of claim (2), over any `[Field k] [Infinite k]`, `d : Fin (N+2) → ℕ`, `r`, `hp, hq`.
>   `#print axioms` (force-elaborated, scratch file importing the full `DLNFibre` aggregator + both new
>   modules) reports `[propext, Classical.choice, Quot.sound]` for
>   `chartPhiSchurAeval_eq_comp_multComap`, `schurToDsig_comp_localizeSchur`,
>   `schurToDsigAt_comp_localizeSchur`, `projCompatOverBaseChart`, `targetProductOverlapTransition`,
>   `chartOverlapTransitionK_trans_symm` — no `sorryAx`, no custom axiom. `scripts/sorries` = 0 across
>   the library. Full `scripts/lb DLNFibre` green (no name clash with the aggregator's siblings, verified
>   by the scratch dual-import).
>
> - **Assumed.** `[Infinite k]` (the deep chart `e_β` inside the trivialization needs it); the structural
>   `hp, hq` rank bounds. No analytic / cited interface.
>
> - **Cited.** None. (Banked-internal inputs only: S4b `FibreOverBaseTriv`, the thread-23 atlas
>   `FibreBundleLocallyTrivialFull`, `MultComorphism`; all green/sorry-free in-repo.)
>
> - **Deferred (named, NOT done — the honest residuals/ceiling).**
>   - **Target-side cocycle round-trip** `(I,J) ∘ (J,I) = id` on `targetProductOverlapTransition`. The
>     transition OBJECT is built; the round-trip is mathematically immediate from the LANDED base-side
>     `chartOverlapTransitionK_trans_symm`, but formalising it stalls on Lean infrastructure (NOT math):
>     (a) the pointwise (`ext`) route unfolds the `@[reducible]` double-localized `targetChartLoc` into a
>     term the **kernel** cannot typecheck in budget (deterministic kernel timeout, heartbeat-invisible);
>     (b) the structural route needs `AlgEquiv.trans_assoc` / `trans_refl` / `refl_trans`, which Mathlib
>     v4.29 does NOT provide for `AlgEquiv` (only `self_trans_symm` / `symm_trans_self`), and proving
>     them by `ext` re-incurs the kernel cost. Fix: either the missing `AlgEquiv` associativity API (a
>     Mathlib-gap spin-out, network-free) or a non-`reducible` `targetChartLoc` with hand-bundled
>     instances. In-file roadmap at `end Target` of `FibreTargetOverlap.lean`.
>   - **Global `Flat π` / `FiberBundle` over `rankROpen`** — NOT claimed. Beyond the cocycle round-trip
>     it additionally needs the triple-overlap coherence packaged + a local-to-global flatness assembly.
>     This is the honest ceiling; it is infra beyond the banked per-pivot atlas + the S1 rank-tie.
>
> - **Route.** (1) Found that `schurToDsig` (`ChartPhiSubstitution`) is `liftAlgHom chartPhiSchurAeval`
>   with `chartPhiVarSub` reading `multPoly`, so projection compatibility is a genuine factorization
>   through `multComap` (not a restatement). Factored as AlgHom equalities via `MvPolynomial.algHom_ext`
>   on the Schur generators + `schurToDsig_algebraMap` + the gauge `awayCongr`. (2) Built the generalized
>   `awayCongr'`, conjugated the base-side overlap through the per-pivot trivializations. The cocycle
>   round-trip hit the kernel/Mathlib-API wall and was deferred (NOT forced) per the bedrock/precision
>   discipline. Codex (xhigh) scoped the two items + flagged the vacuous-restatement trap before any Lean
>   (`codex/scoping-{prompt,answer}.md`).
>
> - **Status.** sorry-free, axiom-clean (awaiting reviewer fidelity pass + controller integration/wiring
>   of the single-writer aggregator).
