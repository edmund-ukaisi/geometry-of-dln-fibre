# Thread 23 — the per-pivot local-product atlas + overlap cocycle (B3-6) — statement card

**Status: sorry-free (pending reviewer fidelity → reviewed PASS-WITH-CONCERNS, actioned).** Module
`lean/DLNFibre/Core/FibreBundleLocallyTrivialFull.lean`. Whole library green (3803 jobs); all
headlines axiom-clean `[propext, Classical.choice, Quot.sound]` (gated via `#print axioms`). Two
decorrelated Codex consults (cocycle framing + naming honesty).

**Scope verdict (honest): the per-pivot local-product atlas with coherent transitions over the
rank-exactly-`r` locus.** NOT named `locallyTrivial` (reviewer + Codex: the cover is point-set, not
scheme-theoretic `span = ⊤`; and bare `locallyTrivial` over the closure `Σ̄^r` is FALSE). The headline
is `reducedFibre_pivotLocalProductAtlasOnRankLocus`.

---

## The framing correction (Codex xhigh, decorrelated)

The team lead's literal target — identify the chart transitions with the **ambient**
`awayOverlapTransition` over `MvPolynomial (Fin p × Fin q) k` — was a **red herring**. The genuine
transition cocycle for this atlas lives over the **base** `sweepSigmaRing`, instantiating the banked
thread-19 engine at `R = sweepSigmaRing`, `f, g = chartDsigAt`. (Consult:
`codex/cocycle-{prompt,answer}.md`.)

## Card 1 — the chart-side overlap cocycle

> **Claim.** On the double overlap of two pivot charts, the canonical transition `AlgEquiv` between
> the two iterated localizations of the base `sweepSigmaRing`, with the cocycle laws.
>
> - **Lean:** `chartOverlapTransition` (+ `_commutes`, `_symm`, `_trans_symm`); `PivotDatum`,
>   `pivotElt`.
> - **Gloss.** `chartOverlapTransition I J := awayOverlapTransition (pivotElt I) (pivotElt J)` over
>   `sweepSigmaRing`, `pivotElt I := chartDsigAt d r I.s I.t`. The laws are the banked thread-19
>   lemmas applied (inherited from localization initiality, not re-asserted).
> - **Proved.** over `[Field k]` (the cocycle lemmas `omit [Infinite k]`); `Fin (N + 2) → ℕ`.
> - **Status.** sorry-free, axiom-clean.

## Card 2 — the trivialization-transition factors through the base gauges (the intertwining)

> **Claim.** The transition between two per-pivot trivializations `e_I.trans e_J.symm` factors
> purely through the base-ring gauge transports — the deep chart `e_β` cancels.
>
> - **Lean:** `chartLocalizedAlgEquivAt_transition_eq_gauge`.
> - **Gloss.** `(e_I).trans (e_J).symm = (awayCongr (gaugeEquivSigma P_I)).symm.trans (awayCongr
>   (gaugeEquivSigma P_J))`, where `e_• = chartLocalizedAlgEquivAt` (thread 22). Since every `e_•` is
>   `(awayCongr P_•).symm ≪≫ e_β` with the SAME `e_β`, the `e_β` cancels; the residual is the relative
>   gauge `P_J · P_I⁻¹` (carried as the gauge-transport composite). So the transitions are
>   base-algebraic — the structure-group content of local triviality.
> - **Proved.** `[Field k] [Infinite k]`, `Fin (N + 2) → ℕ`.
> - **Status.** sorry-free, axiom-clean.

## Card 3 — the geometric cover of the rank-`r` locus

> **Claim.** Every point of `Σ^r` lies in some per-pivot chart `D(ΔPdeepAt s t)`.
>
> - **Lean:** `sweepSigma_subset_chartOpen`.
> - **Gloss.** `∀ x ∈ sweepSigma k d r, ∃ (s, t) injective, IsUnit (eval x (ΔPdeepAt d r s t))`.
>   From `exists_invertible_minor_of_rank` (a rank-`r` matrix has an invertible `r × r` minor) applied
>   to `mult A` (rank `= r` on `Σ^r`) + `eval_det_submatrix_multPoly`. This is the **point-set** cover
>   of the OPEN rank-`= r` locus.
> - **Proved.** `[Field k]` (`omit [Infinite k]`), `Fin (N + 2) → ℕ`.
> - **Status.** sorry-free, axiom-clean.

## Card 4 — the assembled atlas (the headline)

> **Claim.** The full per-pivot local-product atlas over `Σ^r`: cover + per-pivot trivializations +
> coherent transition cocycle + the gauge-factoring coherence, all bundled.
>
> - **Lean:** `PivotLocalProductAtlas` (structure) + `pivotLocalProductAtlas` (instance) +
>   `reducedFibre_pivotLocalProductAtlasOnRankLocus` (headline); supporting `chartDsigAt_tensorEquiv_eq`.
> - **Gloss.** The structure bundles `cover` (Card 3), `triv` (per-pivot `LocalTrivializationDatum`,
>   thread 22), `overlapTransition` (Card 1), `transitionRoundTrip` (the identity normalization), and
>   `transitionFactors` (the trivialization transition = the schur-side `e_{s,t}` transition, the
>   tensor tail cancelling — hence base-algebraic via Card 2). All five fields instantiated.
> - **Proved.** `[Field k] [Infinite k]`, `Fin (N + 2) → ℕ`. Non-vacuity witnesses fire.
> - **Status.** sorry-free, axiom-clean.

---

## What this earns and does NOT earn — and why NOT `locallyTrivial`

- **EARNED:** a genuine per-pivot **local-product atlas with coherent (base-algebraic) transitions**
  over the rank-exactly-`r` locus `Σ^r`: the geometric (point-set) cover + per-pivot trivializations
  into the standard fibre + the overlap transition cocycle with its laws + the intertwining. This is
  the structure-group content of local triviality, assembled and machine-checked.

- **NOT named `locallyTrivial`** (reviewer PASS-WITH-CONCERNS → actioned; Codex naming consult
  `codex/naming-{prompt,answer}.md` + `honesty-name-*`): TWO honesty reasons.
  1. **Closure vs open.** `sweepSigmaRing = O(Σ̄^r)` is the coordinate ring of the CLOSURE. A bare
     scheme-theoretic `locallyTrivial` over `Spec(sweepSigmaRing) = Σ̄^r` is **false** — the rank-`< r`
     boundary points of the closure lie in NO chart (all `r × r` minors vanish there). The charts
     cover exactly the OPEN rank-`= r` locus `Σ^r`.
  2. **Point-set vs scheme cover.** Even over `Σ^r`, the cover supplied (Card 3) is the **point-set**
     cover `∀ x ∈ Σ^r, ∃ pivot, …`, NOT a scheme-theoretic open-cover / unit-ideal `span = ⊤`.

- **The precise residual to a bare scheme-theoretic `locallyTrivial`:** localize `sweepSigmaRing` to
  the rank-`= r` open and prove `span = ⊤` there (where it holds — the `r × r` minors cut out the
  rank-`< r` complement). A clean further rung (Nullstellensatz-style bridge over the open), no new
  mathematics, not built here.

## Net B3 state (controller synthesis)

single-chart triviality (#11) + per-minor open cover + chart family (#18) + ambient cocycle (#19) +
top-left datum (#21) + per-pivot conjugation skeleton / per-pivot trivializations (#22) + **the
per-pivot local-product atlas with coherent transitions over the rank-`r` locus (#23, here)**. The
one remaining rung to a bare scheme-theoretic `locallyTrivial` is the scheme-level cover (`span = ⊤`
over the rank-`= r` open).
