# Statement card — S4 honest local-product over the rank-`= r` open

> **Claim.** The reduced fibre family is an **honest local product over the rank-`= r` open**: over
> `rankROpen ⊆ Spec(sweepSigmaRing k d r)` — now certified (via the S1 keystone) to be exactly the
> locus where the universal product matrix has rank `= r` over each residue field — the per-pivot
> charts `basicOpen(chartDsigAt s t)` form an open cover, and over each chart the localized total ring
> is, as a `k`-algebra, the product `SchurLoc ⊗_k sweepFibreRing` of the local matrix direction with
> the (fixed) standard fibre ring. Equivalently (reader-facing): every prime at which the universal
> matrix has rank `= r` sits in a pivot chart carrying such a product trivialization. **Per-chart /
> uncocycled** — the charts' products are NOT glued on overlaps (roadmap R1).
>
> - **Lean (structure):** `DLNFibre.Core.RankROpenPerPivotLocalProduct`
>   + assembled instance `DLNFibre.Core.reducedFibre_rankROpenPerPivotLocalProduct`
>   (`lean/DLNFibre/Core/FibreLocallyTrivial.lean` @ `9e057101967b8cc7a81bc5fdfdb509801e14d7f3`)
> - **Lean (headline):** `DLNFibre.Core.reducedFibre_existsProductChartAt_rankEq`
>   (same file / SHA)
>
> - **Gloss.**
>   - `RankROpenPerPivotLocalProduct d r hp hq` bundles four fields:
>     - `isRankLocus : ∀ P, P ∈ rankROpen d r ↔ (universalMatrixResidue d r P).rank = r`
>       — the S1 keystone, folded in: `rankROpen` IS the residue-field rank-`= r` locus.
>     - `cover : (⋃ st, basicOpen (chartDsigAt d r st.1 st.2)) = rankROpen d r`
>       — the per-pivot charts cover the rank-`= r` open.
>     - `triv : ∀ I : PivotDatum, LocalTrivializationDatum k (sweepSigmaRing) (Away (chartDsigAt I.s
>       I.t)) (SchurLoc …) (sweepFibreRing)` — a per-chart product trivialization (`k`-algebra iso of
>       the localized chart total ring with `SchurLoc ⊗_k sweepFibreRing`).
>     - `triv_chartElt : ∀ I, (triv I).chartElt = chartDsigAt d r I.s I.t` — the chart localizes at its
>       pivot minor (connects a cover chart to its trivialization).
>   - `reducedFibre_existsProductChartAt_rankEq d r hp hq P hP` : for a prime `P` with
>     `(universalMatrixResidue d r P).rank = r`, `∃ s t, P ∈ basicOpen (chartDsigAt d r s t) ∧
>     Nonempty (Away (chartDsigAt d r s t) ≃ₐ[k] SchurLoc … ⊗[k] sweepFibreRing …)`.
>
> - **Proved (unconditionally).** All four structure fields and the pointwise headline, over any
>   `[Field k] [Infinite k]`, `d : Fin (N+2) → ℕ`, `r`, `hp : r ≤ d (last)`, `hq : r ≤ d 0`. The
>   `isRankLocus` field is the S1 bridge `mem_rankROpen_iff_rank_universalMatrixResidue_eq`; the
>   `cover` is `iSup_pivot_basicOpen_eq_rankROpen`; the `triv` is the banked atlas's per-pivot
>   `LocalTrivializationDatum` (thread 22); the headline composes them. `#print axioms` (force-
>   elaborated) reports `[propext, Classical.choice, Quot.sound]` for both
>   `reducedFibre_rankROpenPerPivotLocalProduct` and `reducedFibre_existsProductChartAt_rankEq` — no `sorryAx`,
>   no custom axiom.
>
> - **Assumed.** `[Infinite k]` (the deep chart `e_β` inside the trivialization needs it); the
>   structural `hp, hq` rank bounds. No analytic / cited interface.
>
> - **Cited.** None. (Banked-internal inputs only: S1 `FibreRankBridge`, the thread-22 atlas
>   `FibreBundleLocallyTrivialFull`; all green/sorry-free in-repo.)
>
> - **Deferred (named, NOT done — the honest residual).**
>   - **R1 — the target-side overlap-trivialization cocycle** (`targetOverlapTransition`): the
>     per-chart products are NOT identified on overlaps. This is precisely why the result is **not**
>     named `locallyTrivial` / `FiberBundle`. (The banked atlas carries the *base-side* overlap cocycle
>     `chartOverlapTransition` + an overlap-local restriction + a gauge-factoring lemma; those are
>     base-side, not the fixed-target gluing a fibre bundle requires.)
>   - **Projection-compatibility** is deliberately **omitted, not asserted.** The product iso is a bare
>     `k`-algebra equivalence `Total ≃ₐ[k] SchurLoc ⊗_k Fibre`; a genuine "respects the base
>     projection" condition would compare it against a named base map `SchurLoc →ₐ[k] Total` (giving an
>     `AlgEquiv` over `SchurLoc`), which is not packaged. Stating it without that map would be vacuous
>     (decorrelated Codex design consult, Q2). S5 (`IsLocallyTrivialProduct` reusable predicate) is a
>     separate rung — not attempted here.
>
> - **Route.** Fold the S1 rank-locus identity into a per-chart-only record (`RankROpenPerPivotLocalProduct`),
>   assemble it from the banked atlas + S1, and expose the harder-to-misread pointwise theorem as the
>   reader-facing headline. The honesty levers (drop the vacuous projection field; name R1 as the
>   residual; avoid `locallyTrivial`) were set by a decorrelated Codex design consult
>   (`codex/design-{prompt,answer}.md`) before any Lean was written.
>
> - **Status.** sorry-free (awaiting reviewer fidelity pass).
