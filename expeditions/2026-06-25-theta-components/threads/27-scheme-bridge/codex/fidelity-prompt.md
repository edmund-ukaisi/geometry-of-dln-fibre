<task>
You are an adversarial honesty red-team on a Lean 4 + Mathlib formalisation. A
PR claims to close the "scheme-level half" of a cover→PivotDatum bridge, so that
injectivity of selectors is DERIVED from chart membership rather than ASSUMED.
I want you to attack the claims for vacuity / overclaim. Do NOT trust my framing.

CONTEXT (definitions, exact Lean):

- `multPoly d : Fin (d (Fin.last N)) → Fin (d 0) → MvPolynomial (RepCoord d) k`
  is the (r,c) entry of a generic matrix product (a polynomial). `Matrix.of (multPoly d)`
  is the generic product matrix, indexed rows = Fin (d (Fin.last N)), cols = Fin (d 0).

- `ΔPdeepAt d r s t := ((Matrix.of (multPoly d)).submatrix s t).det`, where
  `s : Fin r → Fin (d (Fin.last N))` (row selector), `t : Fin r → Fin (d 0)` (col selector).
  So `submatrix s t` is the r×r matrix with (i,j) entry `multPoly (s i) (t j)`.

- `sweepSigma := canonicalCoord '' productRankLocus d r` where productRankLocus is the
  set of tuples A with rank(mult A) = r (rank EXACTLY r). `sweepSigmaRing := MvPolynomial(RepCoord d) ⧸ vanishingIdeal(sweepSigma)`.

- `chartDsigAt d r s t := Ideal.Quotient.mk (vanishingIdeal(sweepSigma)) (ΔPdeepAt d r s t)`
  — the class of the minor polynomial in sweepSigmaRing.

- `pivotElt d r hp hq I := chartDsigAt d r I.s I.t` for a PivotDatum I (a structure carrying
  selectors s,t and permutations σ,τ with σ∘castLE = s, τ∘castLE = t).

- `pivotDatumOfSelectors ... s t (hs: Injective s)(ht: Injective t) : PivotDatum` sets .s:=s,.t:=t,
  σ,τ := extendToPerm of the injective selectors. `pivotElt_pivotDatumOfSelectors : pivotElt (pivotDatumOfSelectors..s t hs ht) = chartDsigAt d r s t := rfl`.

THE NEW LEMMAS UNDER AUDIT:

1. `ΔPdeepAt_eq_zero_of_not_injective_left (hs : ¬ Injective s) : ΔPdeepAt d r s t = 0`
   proof: obtain i≠j with s i = s j from not_injective_iff; `det_zero_of_row_eq hij (funext col, submatrix_apply rewrite with s i = s j)`.
2. `_right` symmetric with `det_zero_of_column_eq` and t i = t j.
3. `chartDsigAt_eq_zero_of_not_injective (h: ¬Inj s ∨ ¬Inj t) : chartDsigAt d r s t = 0`
   proof: ΔPdeepAt = 0 (above), then mk 0 = 0 (map_zero).
4. `injective_of_mem_basicOpen_chartDsigAt {p} (hp : p ∈ basicOpen (chartDsigAt d r s t)) : Injective s ∧ Injective t`
   proof: rw mem_basicOpen (gives chartDsigAt ∉ p.asIdeal); by_contra each side, get chartDsigAt = 0, then 0 ∈ p.asIdeal contradicts.
5. `pivotDatumOfMemBasicOpen {p} (hmem : p ∈ basicOpen (chartDsigAt d r s t)) :
     {I : PivotDatum // pivotElt I = chartDsigAt d r s t}`
   := ⟨pivotDatumOfSelectors ... s t (inj from #4).1 (inj from #4).2, pivotElt_pivotDatumOfSelectors ...⟩.
   The atlas FIELD pivotOfBasicOpen is wired to this.

CLAIMS I want you to attack:
(A) "pivotDatumOfMemBasicOpen / pivotOfBasicOpen are genuinely free of any injectivity
    hypothesis on the selectors — only p ∈ basicOpen is assumed." Is that what the signatures
    actually say, or is injectivity smuggled in (e.g. via an instance, a hidden hyp, or because
    the type forces it)?
(B) The localizing-element equality `pivotElt I = chartDsigAt d r s t` is `rfl`. Is that a
    GENUINE equality of two sweepSigmaRing elements, or a vacuous/definitional alias that says
    nothing (i.e. is it a "rfl-after-unfold packaging" with no content, or does it correctly assert
    that the produced PivotDatum localizes at exactly the chart's element)?
(C) NON-VACUITY: is `injective_of_mem_basicOpen_chartDsigAt` vacuous? Specifically: could it be
    that `chartDsigAt d r s t = 0` for ALL (s,t), making basicOpen always empty, so the lemma
    holds with no content? Argue whether the chart basicOpen(chartDsigAt s t) is inhabitable for
    SOME injective (s,t), given that sweepSigma is the rank-EXACTLY-r locus and r ≤ d(last), r ≤ d 0.
    (Consider: a k-point x in sweepSigma gives a maximal ideal; an r×r minor that is a unit at x
    gives chartDsigAt s t ∉ that maximal ideal. Does that argument hold? Are there edge cases —
    r = 0, sweepSigma empty — where it fails, and would those be honest gaps in the claim?)
(D) Does the det-zero step use det_zero_of_row_eq / _column_eq CORRECTLY? In Mathlib,
    `submatrix s t` reindexes rows by s and columns by t. det_zero_of_row_eq needs two equal ROWS.
    Row i of (submatrix s t) is `fun col => multPoly (s i) (t col)`. If s i = s j then row i = row j.
    Confirm the rows↔s, columns↔t correspondence is right and the lemma is applied to the correct one.
</task>

<output_contract>
Five short sections (A)–(E):
(A) verdict: injectivity-free YES/NO + the precise reason.
(B) verdict: genuine equality vs vacuous alias + reason.
(C) verdict: non-vacuous YES/NO; if there are edge cases (r=0, empty Σ^r) state them and say
    whether they make the HEADLINE claim dishonest or are acceptable scope.
(D) verdict: correct row/col usage YES/NO.
(E) Single overall: is the PR's honesty claim ("injectivity derived, not assumed; equality genuine;
    mechanism non-vacuous") DEFENSIBLE? One paragraph. Flag any overclaim you'd force a rewrite for.
</output_contract>

<grounding_rules>
You are reasoning from the Lean/Mathlib semantics I described; you cannot run the build. Mark each
judgement as either (i) forced by the Lean/Mathlib semantics as stated, or (ii) an inference that
depends on a fact you cannot verify from my description (name that fact). Do not invent Mathlib lemma
behaviour — if det_zero_of_row_eq or submatrix semantics differ from what I stated, say so as a
caveat. Be concrete; a specific vacuity case beats vague doubt.
</grounding_rules>
