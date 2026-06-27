<task>
Lean 4 / Mathlib v4.29 algebraic-geometry formalisation. I am building the S4 deliverable of an
expedition: an HONESTLY-NAMED "local triviality over the rank-= r open" statement for a fibre family,
promoting an already-assembled per-pivot local-product atlas. The name=content discipline is the
load-bearing thing here. I need you to red-team the EXACT honest statement shape before I build it.

## The banked objects (all green, sorry-free, axiom-clean; I will reuse, not re-derive)

Setting: a field `k` (Infinite), `d : Fin (N+2) → ℕ`, `r : ℕ`, `hp : r ≤ d (last)`, `hq : r ≤ d 0`.
`sweepSigmaRing k d r` is the coordinate ring of the chart-CLOSURE Σ̄^r (rank ≤ r baked in).

1. `rankROpen d r : Set (PrimeSpectrum (sweepSigmaRing k d r))` — DEFINED as the complement of the
   common-vanishing locus V({chartDsigAt s t}) of all r×r pivot minors `chartDsigAt s t`.

2. `iSup_pivot_basicOpen_eq_rankROpen` :
     (⋃ st, (PrimeSpectrum.basicOpen (chartDsigAt d r st.1 st.2) : Set (PrimeSpectrum …))) = rankROpen d r
   — the per-pivot charts cover rankROpen (near-definitional, since rankROpen is the cover-complement).

3. **S1 KEYSTONE (just landed)** `mem_rankROpen_iff_rank_universalMatrixResidue_eq` :
     P ∈ rankROpen d r ↔ (universalMatrixResidue d r P).rank = r
   where `universalMatrixResidue d r P` is the generic product matrix pushed into the residue field
   κ(P) = P.asIdeal.ResidueField. THIS is the new content: it certifies rankROpen genuinely IS the
   locus where the universal matrix has rank exactly r over each residue field — a GEOMETRIC identity,
   not the definitional cover-complement. Previously the objection to naming the result "locallyTrivial"
   was precisely that rankROpen = {rank = r} was unformalized; S1 closes that.

4. Per pivot `I : PivotDatum d r hp hq` (carrying selectors s,t and permutations σ,τ), a
   `LocalTrivializationDatum k Base Total BaseLoc Fibre` with:
     - `chartElt = chartDsigAt I.s I.t` (∈ sweepSigmaRing; this is `pivotElt I`)
     - `trivialization : Localization.Away (chartDsigAt I.s I.t) ≃ₐ[k] (SchurLoc) ⊗[k] (sweepFibreRing)`
   So the localized total ring of chart I is iso, as a k-algebra, to a tensor product
   SchurLoc ⊗ sweepFibreRing. `SchurLoc` is the localized matrix-direction ("base-open side" of the
   product), `sweepFibreRing` is the standard fibre coordinate ring (SAME for every pivot).

5. Cocycle data over overlaps: `chartOverlapTransition I J` (base-side AlgEquiv on D(g_I·g_J)) with
   cocycle laws, an overlap-LOCAL restriction lemma, and a "transition factors through base gauges"
   lemma. **BUT** the genuine fixed-TARGET overlap-trivialization cocycle (`targetOverlapTransition`,
   roadmap R1) is NOT assembled — the per-pivot trivialization targets are not glued on overlaps.

6. The whole thing is bundled as `PivotLocalProductAtlas` and instantiated as
   `reducedFibre_pivotLocalProductAtlasOnRankOpen d r hp hq`.

## The decision I need adjudicated

I want to state a clean, honestly-named theorem/structure
`reducedFibre_isLocallyProductOverRankOpen` capturing "∃ open cover of rankROpen + per-chart product
iso over the base", USING S1 to upgrade the open's status from "definitional cover-complement" to
"genuine rank-= r locus". I will NOT name it `locallyTrivial`/`FiberBundle` (that implies the R1
target-side coherent transitions I have not proved).

Concretely I am considering a structure with fields:
  (a) `isRankLocus : ∀ P, P ∈ rankROpen d r ↔ (universalMatrixResidue d r P).rank = r`  [= S1]
  (b) `cover : (⋃ st, basicOpen (chartDsigAt …)) = rankROpen d r`  [= the open cover]
  (c) `triv : ∀ st injective, Localization.Away (chartDsigAt st) ≃ₐ[k] SchurLoc ⊗ sweepFibreRing`
      [per-chart product iso] with `chartElt = chartDsigAt st` recorded
  (d) a "projection-compatible" field: the trivialization, composed with the projection
      `SchurLoc ⊗ sweepFibreRing → SchurLoc` (tensor-first projection), recovers the structural
      localization map Away(chartDsigAt) ⟵ base direction — i.e. the iso respects the base projection.

## Questions (rank by importance)

Q1. Is field (a) [the S1 rank-locus identity] the RIGHT thing to fold in to make this an HONEST
    "local triviality over the rank-= r open" rather than over a formally-defined open? Or is it
    overclaiming / orthogonal / better left as a separate cited input? Be precise about what (a) buys.

Q2. For (d) "compatible with the projection": in standard fibre-bundle local triviality, the chart iso
    φ : π⁻¹(U) ≅ U × F must satisfy pr₁ ∘ φ = π. Here Total = Away(chartDsigAt), the product is
    SchurLoc ⊗ sweepFibreRing, and the "base" of the product is the SchurLoc (matrix-direction)
    factor. Algebraically the projection-to-base is the tensor inclusion of the FIRST factor
    `SchurLoc → SchurLoc ⊗ sweepFibreRing` (= `algebraMap`/`includeLeft`), and π is the structural
    `algebraMap`. What is the cleanest HONEST algebraic statement that the trivialization "respects the
    projection", given I have a k-algebra iso `Total ≃ₐ[k] SchurLoc ⊗ Fibre`? Is "respects projection"
    even meaningful/checkable here, or is it automatic / vacuous / requires data I do not have? If it
    requires identifying which subring of Total is the base direction, do I have that (the
    trivialization is `(awayCongr gauge).symm ≪≫ e_β ≪≫ tensor-package`)? Should I DROP (d) rather than
    state something vacuous?

Q3. Given R1 (target-side overlap cocycle) is genuinely missing, is "local product over an open cover"
    (cover + per-chart product iso, NO claim of glued transitions) a COHERENT and HONEST mathematical
    notion to name on its own, distinct from a fibre bundle? Or does omitting the glue make the named
    object misleading (a reader expects bundle-like coherence from "locally a product")? Name the
    single sharpest objection a skeptical reviewer would raise to the name
    `reducedFibre_isLocallyProductOverRankOpen`, and whether it is fatal.

Q4. Is there a strictly BETTER honest headline I'm missing — e.g. should the deliverable instead be a
    single theorem of the form "∀ P ∈ rankROpen, ∃ chart with a product trivialization at P" (a
    pointwise local-triviality-at-each-prime statement, which composes S1 + cover + triv directly and
    reads as genuine local triviality without needing a bespoke structure)? Compare that pointwise
    theorem against the structure-bundling approach for honesty + reusability.
</task>

<output_contract>
Answer Q1–Q4 in order, each ≤ 8 sentences. Then a final section "RECOMMENDED SHAPE" giving the exact
fields/signature you'd commit to (Lean-ish pseudo-signature is fine), and a one-line "DO NOT" naming
the single thing that would make it dishonest. Be decisive — I need a buildable target, not options.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the objects as described; if a claim depends on a detail I have
not given (e.g. whether `e_β` makes the base-direction subring identifiable), say so explicitly and
mark it as an assumption, do not assert it as fact. Flag any place where my proposed shape would be
VACUOUS or CIRCULAR (e.g. if (b) is near-definitional, does folding it in add nothing?).
</grounding_rules>
