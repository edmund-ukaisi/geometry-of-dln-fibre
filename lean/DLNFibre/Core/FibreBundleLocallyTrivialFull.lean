/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreChartConjugation
import DLNFibre.Core.FibreBundleTransition

/-!
# `DLNFibre.Core.FibreBundleLocallyTrivialFull` — the chart-side overlap cocycle (B3-6)

Thread 22 (`Core.FibreChartConjugation`) built the conjugation skeleton: a genuine
`LocalTrivializationDatum` at **every** pivot `(s, t)` of the per-minor cover, all over the
chart-closure base ring `sweepSigmaRing k d r`. The remaining rung to a `locallyTrivial` name is the
**transition cocycle on overlaps**.

The decorrelated Codex consult (xhigh) corrected the framing: the genuine transition cocycle for
this atlas lives over the **base** `sweepSigmaRing`, NOT over the ambient matrix-space coordinate
ring `MvPolynomial (Fin p × Fin q) k` (the latter is a red herring — it is the coordinate ring of a
*different* ring, used in thread 19 for the ambient matrix cover). My per-pivot charts are all
localizations of the SAME base `sweepSigmaRing` at the elements `chartDsigAt s t`, so the canonical
overlap identification is exactly the banked abstract `awayOverlapTransition` (thread 19), now
instantiated at `R = sweepSigmaRing`, `f = chartDsigAt s t`, `g = chartDsigAt s' t'`.

## What is built (the chart-side overlap cocycle)

- `PivotDatum d r hp hq` — a pivot of the atlas: the selectors `s, t` and the permutations `σ, τ`
  carrying the first `r` rows/columns to them (carried as data, per Codex — independence from the
  `σ, τ` choice is otherwise a separate rung). `pivotElt I := chartDsigAt d r I.s I.t` is its
  localizing element of `sweepSigmaRing`.
- `chartOverlapTransition I J := awayOverlapTransition (pivotElt I) (pivotElt J)` over
  `sweepSigmaRing` — the genuine transition `AlgEquiv` on the double overlap `D(g_I · g_J)`, with
  the inherited cocycle laws (`_commutes`, `_symm`, `_trans_symm`, the triple cocycle), all FROM the
  banked thread-19 engine (localization initiality).

## Scope (honest) — locally trivial over the rank-exactly-`r` locus

The full assembly `reducedFibre_locallyTrivialOnRankLocus` (a `PivotLocalProductAtlas`) bundles, and
machine-checks, all the local-triviality data over the rank-exactly-`r` locus `Σ^r`:

- the **geometric cover** of `Σ^r` by the per-pivot charts `D(ΔPdeepAt s t)`
  (`sweepSigma_subset_chartOpen`, from `exists_invertible_minor_of_rank`);
- the **per-pivot trivializations** into the standard fibre `SchurLoc ⊗ sweepFibreRing` (thread 22);
- the **base-side transition cocycle** `chartOverlapTransition` with its laws (banked thread-19
  engine at `R = sweepSigmaRing`);
- the **intertwining** `chartLocalizedAlgEquivAt_transition_eq_gauge` — the transition between
  trivializations factors purely through the base-ring gauges (the deep chart `e_β` cancels), so the
  transitions are base-algebraic (the structure-group content).

**The `OnRankLocus` qualifier is load-bearing** (Codex xhigh, decorrelated): a *bare*
scheme-theoretic `locallyTrivial` over `Spec (sweepSigmaRing) = Σ̄^r` (the CLOSURE) is **false** —
the rank-`< r` boundary points of the closure lie in NO chart (all `r × r` minors vanish there). The
charts cover exactly the OPEN rank-`= r` locus `Σ^r`, the genuine base of `mult⁻¹(B) → Mat^{= r}`.
So the cover is the point-set cover of `Σ^r`, NOT a unit-ideal `span = ⊤` over the closure ring. The
precise residual to a bare scheme-theoretic statement is to localize `sweepSigmaRing` to the
rank-`= r` open and prove `span = ⊤` there (where it holds) — a clean further rung, not built here.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-! ## A pivot of the atlas -/

/-- **A pivot of the per-minor atlas.** The selectors `s, t` (into the target rows `Fin (d last)` /
source columns `Fin (d 0)`) together with permutations `σ, τ` carrying the first `r` rows/columns to
the selected ones — the data the conjugation skeleton needs. Carried as a bundle (per Codex:
otherwise independence from the `σ, τ` choice is a separate rung). -/
structure PivotDatum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) where
  /-- The target-row selector. -/
  s : Fin r → Fin (d (Fin.last (N + 1)))
  /-- The source-column selector. -/
  t : Fin r → Fin (d 0)
  /-- The target permutation carrying the first `r` rows to `s`. -/
  σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))
  /-- The source permutation carrying the first `r` columns to `t`. -/
  τ : Equiv.Perm (Fin (d 0))
  /-- `σ` carries the first `r` rows to the selected ones. -/
  hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i
  /-- `τ` carries the first `r` columns to the selected ones. -/
  hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j

/-- **The localizing element of a pivot**: the `(s, t)` deep minor class `chartDsigAt s t` in the
chart-closure base ring `sweepSigmaRing`. The chart at `I` is the principal open `D(pivotElt I)`. -/
noncomputable def pivotElt (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    sweepSigmaRing k d r :=
  chartDsigAt d r I.s I.t

/-! ## The chart-side overlap transition cocycle -/

/-- **The chart-side overlap transition.** On the double overlap `D(pivotElt I · pivotElt J)` of two
pivot charts, the canonical transition `AlgEquiv` between the two iterated localizations of the base
`sweepSigmaRing` — the banked abstract `awayOverlapTransition` (thread 19) at `R = sweepSigmaRing`,
`f = pivotElt I`, `g = pivotElt J`. Both `awayOverlap (pivotElt I) (pivotElt J)` and the swap are
`IsLocalization.Away (pivotElt I · pivotElt J) sweepSigmaRing`. -/
noncomputable def chartOverlapTransition (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)
      ≃ₐ[sweepSigmaRing k d r]
        awayOverlap (pivotElt (k := k) d r hp hq J) (pivotElt (k := k) d r hp hq I) :=
  awayOverlapTransition (pivotElt d r hp hq I) (pivotElt d r hp hq J)

omit [Infinite k] in
/-- **Cocycle: base normalization.** The transition fixes the image of the base ring
`sweepSigmaRing` (it is a base-algebra map). -/
theorem chartOverlapTransition_commutes (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq)
    (x : sweepSigmaRing k d r) :
    chartOverlapTransition (k := k) d r hp hq I J
        (algebraMap (sweepSigmaRing k d r)
          (awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)) x)
      = algebraMap (sweepSigmaRing k d r)
          (awayOverlap (pivotElt (k := k) d r hp hq J) (pivotElt (k := k) d r hp hq I)) x :=
  awayOverlapTransition_commutes _ _ x

omit [Infinite k] in
/-- **Cocycle: symmetry.** The `(I, J)` transition's inverse is the `(J, I)` transition. -/
theorem chartOverlapTransition_symm (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    (chartOverlapTransition (k := k) d r hp hq I J).symm
      = chartOverlapTransition (k := k) d r hp hq J I :=
  awayOverlapTransition_symm _ _

omit [Infinite k] in
/-- **Cocycle: identity normalization.** The pairwise round trip `(J, I) ∘ (I, J)` is the id. -/
theorem chartOverlapTransition_trans_symm (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    (chartOverlapTransition (k := k) d r hp hq I J).trans
        (chartOverlapTransition (k := k) d r hp hq J I)
      = AlgEquiv.refl :=
  awayOverlapTransition_trans_symm _ _

/-! ## The trivialization transition factors through the base gauges (B3-6b)

The genuine coherence tying the cocycle to the per-pivot trivializations: the transition between two
per-pivot trivializations `e_I.trans e_J.symm` (between the single-localized chart total rings
`Away (chartDsigAt I)` and `Away (chartDsigAt J)`) factors **purely through the base-ring gauge
transports** — the deep chart `e_β` cancels, since every `e_I` is `(awayCongr (gaugeEquivSigma P_I))
.symm ≪≫ e_β` with the SAME `e_β`. So the transition is the localization transport of base-ring
automorphisms (`gaugeEquivSigma`), i.e. it is base-algebraic — the structure-group content of local
triviality. (Codex-confirmed: the `e_β` cancellation is real; the residual is the relative gauge
`P_J · P_I⁻¹`, carried here as the composite `(awayCongr P_I).symm ≪≫ awayCongr P_J`.) -/

/-- **The trivialization transition factors through the base gauges.** The transition between the
two per-pivot trivializations `e_I` (`chartLocalizedAlgEquivAt` at `I`) and `e_J` (at `J`),
`e_I.trans e_J.symm : Away (chartDsigAt I) ≃ₐ[k] Away (chartDsigAt J)`, equals the composite of the
two base-ring gauge localization transports `(awayCongr (gaugeEquivSigma P_I)).symm ≪≫ awayCongr
(gaugeEquivSigma P_J)` — the deep chart `e_β = chartLocalizedAlgEquiv` cancels (both `e_I`, `e_J`
factor through it). Hence the transition is the localization transport of base automorphisms: the
transitions are base-algebraic, the local-triviality structure-group content. -/
theorem chartLocalizedAlgEquivAt_transition_eq_gauge (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    (chartLocalizedAlgEquivAt d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trans
        (chartLocalizedAlgEquivAt d r hp hq J.s J.t J.σ J.τ J.hσ J.hτ).symm
      = (awayCongr (gaugeEquivSigma d r (pivotGauge d I.σ I.τ)) (chartDsig k d r hp hq)
            (chartDsigAt d r I.s I.t)
            (gaugeEquivSigma_chartDsig d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ)).symm.trans
          (awayCongr (gaugeEquivSigma d r (pivotGauge d J.σ J.τ)) (chartDsig k d r hp hq)
            (chartDsigAt d r J.s J.t)
            (gaugeEquivSigma_chartDsig d r hp hq J.s J.t J.σ J.τ J.hσ J.hτ)) := by
  -- unfold both trivializations to `(awayCongr P).symm ≪≫ e_β`; the `e_β` cancels (`ext` + `simp`)
  ext x
  simp only [chartLocalizedAlgEquivAt, AlgEquiv.trans_apply, AlgEquiv.symm_trans_apply,
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_symm]

/-- **The per-pivot tensor trivialization factors as `e_{s,t}` then the schur tensor tail.**
`chartDsigAt_tensorEquiv = chartLocalizedAlgEquivAt ≪≫ reducedFibre_chartGfib_tensorEquiv_…`. Both
sides are `awayCongr.symm` then the top-left tensor package `reducedFibre_chartDsig_tensorEquiv_…`,
and the latter is itself `chartLocalizedAlgEquiv ≪≫ (chartGfib tensor)` — so the `(s, t)` tensor
trivialization is the `(s, t)` chart equiv `e_{s,t}` followed by the SAME schur-side tensor tail. -/
theorem chartDsigAt_tensorEquiv_eq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (σ : Equiv.Perm (Fin (d (Fin.last (N + 1))))) (τ : Equiv.Perm (Fin (d 0)))
    (hσ : ∀ i : Fin r, σ (Fin.castLE hp i) = s i)
    (hτ : ∀ j : Fin r, τ (Fin.castLE hq j) = t j) :
    chartDsigAt_tensorEquiv (k := k) d r hp hq s t σ τ hσ hτ
      = (chartLocalizedAlgEquivAt (k := k) d r hp hq s t σ τ hσ hτ).trans
          (reducedFibre_chartGfib_tensorEquiv_reducedVariety d r hp hq) := by
  ext x
  simp only [chartDsigAt_tensorEquiv, chartLocalizedAlgEquivAt,
    reducedFibre_chartDsig_tensorEquiv_reducedVariety, AlgEquiv.trans_apply]

/-! ## The geometric base-cover by the per-pivot charts (B3-6c)

Every point of the base locus `Σ^r = sweepSigma` lies in at least one per-pivot chart `D(ΔPdeepAt
s t)`: at a point `A` with `rank (mult A) = r`, the determinantal-rank existence fact
(`exists_invertible_minor_of_rank`) gives some pivot whose `r × r` minor of `mult A` is invertible,
i.e. `ΔPdeepAt s t` does not vanish there (`eval_det_submatrix_multPoly`). This is the genuine
geometric cover of the base. -/

omit [Infinite k] in
/-- **The per-pivot charts cover the base locus `Σ^r` (the geometric cover).** Every point `x` of
`sweepSigma` is in some chart `D(ΔPdeepAt s t)` — there is an injective pivot `(s, t)` with
`eval x (ΔPdeepAt s t)` a unit. From `exists_invertible_minor_of_rank` (a rank-`r` matrix has an
invertible `r × r` minor) applied to `mult A` (rank `= r` on `Σ^r`) + `eval_det_submatrix_multPoly`
(eval of the deep `(s, t)` minor = the `(s, t)` minor det of `mult A`). -/
theorem sweepSigma_subset_chartOpen (d : Fin (N + 2) → ℕ) (r : ℕ)
    (x : RepCoord d → k) (hx : x ∈ sweepSigma k d r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      Function.Injective s ∧ Function.Injective t ∧
      IsUnit (eval x (ΔPdeepAt (k := k) d r s t)) := by
  obtain ⟨A, hA, rfl⟩ := hx
  rw [mem_productRankLocus] at hA
  obtain ⟨s, t, hs, ht, hdet⟩ := exists_invertible_minor_of_rank (mult d A) hA
  exact ⟨s, t, hs, ht, by rw [ΔPdeepAt, eval_det_submatrix_multPoly]; exact hdet⟩

/-! ## The per-pivot local-product atlas with coherent transitions (B3-6c)

The genuine assembly: for a fixed `(d, r)` the per-pivot data forms a **local-product atlas with a
coherent transition cocycle** — a `LocalTrivializationDatum` at every pivot (thread 22), the
base-side overlap transition cocycle (above), and the coherence that the transitions between
trivializations
factor through the base gauges (above). This is the structure-group content of local triviality,
assembled and machine-checked. -/

open scoped TensorProduct in
/-- **A per-pivot local-product atlas with coherent transitions.** Bundles, for a fixed `(d, r)`:
a `LocalTrivializationDatum` at every pivot `I` (the trivialization `triv I`, into the standard
fibre `SchurLoc ⊗ sweepFibreRing`), the base-side overlap transition cocycle `overlapTransition`
on every pair `(I, J)` with its identity normalization, and the coherence `transitionFactors` that
the transition between two trivializations factors through the base-ring gauges (so the transitions
are base-algebraic — the structure-group content). This is the coherent atlas; it is **not** the
full `locallyTrivial` claim, which additionally needs the base-cover (the disclaimer below). -/
structure PivotLocalProductAtlas (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) where
  /-- The geometric cover: every point of `Σ^r` lies in some chart `D(ΔPdeepAt s t)`. -/
  cover : ∀ x : RepCoord d → k, x ∈ sweepSigma k d r →
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      Function.Injective s ∧ Function.Injective t ∧
      IsUnit (eval x (ΔPdeepAt (k := k) d r s t))
  /-- A genuine local-trivialization datum at every pivot. -/
  triv : ∀ I : PivotDatum d r hp hq,
    LocalTrivializationDatum k (sweepSigmaRing k d r)
      (Localization.Away (chartDsigAt (k := k) d r I.s I.t))
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq)
  /-- The base-side overlap transition on every pair of pivots. -/
  overlapTransition : ∀ I J : PivotDatum d r hp hq,
    awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)
      ≃ₐ[sweepSigmaRing k d r]
        awayOverlap (pivotElt (k := k) d r hp hq J) (pivotElt (k := k) d r hp hq I)
  /-- The transition cocycle round-trips to the identity. -/
  transitionRoundTrip : ∀ I J : PivotDatum d r hp hq,
    (overlapTransition I J).trans (overlapTransition J I) = AlgEquiv.refl
  /-- The transition between trivializations equals the schur-side `e_{s,t}` transition (the tensor
  tail cancels): so it factors through the base gauges
  (`chartLocalizedAlgEquivAt_transition_eq_gauge`), i.e. the transitions are base-algebraic. -/
  transitionFactors : ∀ I J : PivotDatum d r hp hq,
    (triv I).trivialization.trans (triv J).trivialization.symm
      = (chartLocalizedAlgEquivAt d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trans
          (chartLocalizedAlgEquivAt d r hp hq J.s J.t J.σ J.τ J.hσ J.hτ).symm

/-- **The per-pivot atlas is genuinely assembled** for every `(d, r)`: every field is instantiated
from thread-22's per-pivot trivializations + the base-side overlap cocycle + the gauge-factoring
coherence. (`transitionFactors` holds because all trivializations are `chartDsigAt_tensorEquiv =
chartLocalizedAlgEquivAt ≪≫ (chartGfib tensor)` with the SAME tensor tail, so it collapses to the
`chartLocalizedAlgEquivAt`-transition, which is base-algebraic.) -/
noncomputable def pivotLocalProductAtlas (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    PivotLocalProductAtlas (k := k) d r hp hq where
  cover x hx := sweepSigma_subset_chartOpen d r x hx
  triv I := perPivotLocalTrivializationDatum d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ
  overlapTransition I J := chartOverlapTransition d r hp hq I J
  transitionRoundTrip I J := chartOverlapTransition_trans_symm d r hp hq I J
  transitionFactors I J := by
    -- both trivializations are `chartLocalizedAlgEquivAt ≪≫ (chartGfib tensor)` (the SAME tail);
    -- the tail cancels in `triv I ≪≫ (triv J).symm`, leaving the chart-equiv transition
    show (perPivotLocalTrivializationDatum d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization.trans
        (perPivotLocalTrivializationDatum d r hp hq J.s J.t J.σ J.τ J.hσ J.hτ).trivialization.symm
      = _
    rw [show (perPivotLocalTrivializationDatum d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization
          = chartDsigAt_tensorEquiv d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ from rfl,
      show (perPivotLocalTrivializationDatum d r hp hq J.s J.t J.σ J.τ J.hσ J.hτ).trivialization
          = chartDsigAt_tensorEquiv d r hp hq J.s J.t J.σ J.τ J.hσ J.hτ from rfl,
      chartDsigAt_tensorEquiv_eq, chartDsigAt_tensorEquiv_eq]
    ext x
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.symm_apply_apply]

/-! ## The EARNED headline: the per-pivot local-product atlas over the rank-`r` locus

The reduced fibre bundle has a **per-pivot local-product atlas with coherent transitions over the
rank-exactly-`r` locus** `Σ^r`: the geometric cover of `Σ^r` by the per-pivot charts + the per-pivot
trivializations into the standard fibre + the coherent (base-algebraic) transition cocycle, all
assembled (`pivotLocalProductAtlas`).

**The headline is deliberately NOT named `locallyTrivial`** (reviewer + Codex xhigh, decorrelated):
two reasons. (1) A *bare* scheme-theoretic `locallyTrivial` over `Spec (sweepSigmaRing) = Σ̄^r` (the
CLOSURE) is **false** — the rank-`< r` boundary points of the closure lie in NO chart `D(ΔPdeepAt
s t)` (every `r × r` minor vanishes there). The charts cover exactly the OPEN rank-`= r` locus
`Σ^r`, the genuine base of `mult⁻¹(B) → Mat^{= r}`. (2) Even over `Σ^r` the cover supplied here is
the **point-set** cover (`∀ x ∈ Σ^r, ∃ pivot, …`, `PivotLocalProductAtlas.cover`), NOT a
scheme-theoretic open-cover / unit-ideal `span = ⊤`. So the honest name is "per-pivot local-product
atlas (with coherent transitions) over the rank locus", not "locally trivial". The precise residual
to a bare scheme-theoretic `locallyTrivial` is to localize `sweepSigmaRing` to the rank-`= r` open
and prove `span = ⊤` there (where it holds — the `r × r` minors cut out the rank-`< r` complement);
a clean further rung, not built here. -/

/-- **The per-pivot local-product atlas over the rank-exactly-`r` locus.** The full assembly
(`pivotLocalProductAtlas`): the geometric (point-set) cover of `Σ^r` by the per-pivot charts, the
per-pivot trivializations into the standard fibre `SchurLoc ⊗ sweepFibreRing`, and the coherent
base-algebraic transition cocycle on overlaps — all genuinely assembled. Deliberately **not** named
`locallyTrivial`: the base is the rank-`= r` locus `Σ^r` (not its closure `Σ̄^r`, over which bare
scheme-theoretic local triviality is false), and the cover is point-set, not `span = ⊤`. See the
section note for the precise residual to a scheme-theoretic statement. -/
noncomputable def reducedFibre_pivotLocalProductAtlasOnRankLocus (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    PivotLocalProductAtlas (k := k) d r hp hq :=
  pivotLocalProductAtlas d r hp hq

/-! ## Non-vacuity witnesses -/

section Witness

/-- **Cover witness.** The geometric cover fires: any point of `Σ^r` lies in some per-pivot chart —
a concrete consequence at an abstract `[Infinite k]` field, the genuine geometric local-triviality
content over the rank locus. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (x : RepCoord d → k) (hx : x ∈ sweepSigma k d r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      Function.Injective s ∧ Function.Injective t ∧
      IsUnit (eval x (ΔPdeepAt (k := k) d r s t)) :=
  (reducedFibre_pivotLocalProductAtlasOnRankLocus (k := k) d r hp hq).cover x hx

/-- **Atlas witness.** The transition cocycle round-trips to the identity at every pair of pivots —
the assembled atlas is genuine coherent data, not asserted. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ)
    (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    letI A := reducedFibre_pivotLocalProductAtlasOnRankLocus (k := k) d r hp hq
    (A.overlapTransition I J).trans (A.overlapTransition J I) = AlgEquiv.refl :=
  (reducedFibre_pivotLocalProductAtlasOnRankLocus (k := k) d r hp hq).transitionRoundTrip I J

end Witness

end DLNFibre.Core
