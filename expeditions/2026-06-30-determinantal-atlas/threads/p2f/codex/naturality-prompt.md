<task>
FOLLOW-UP (decorrelated) on a Lean 4 + Mathlib (v4.29) formalisation of a constructive
pivot-chart atlas. I have PROVED, sorry-free, the target-side TRIPLE COCYCLE
`((tripleTransition C D E).trans (tripleTransition D E C)).trans (tripleTransition E C D) = AlgEquiv.refl`
where `tripleTransition C D E : targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D E C` is built by
CONJUGATING the canonical base-side triple transition `chartTripleTransitionK C D E`
(`IsLocalization.algEquiv` between cyclic `awayTriple` presentations of `Base`, k-restricted)
through the two canonical transports `tripleTriv` (= `awayCongr'` of the 2-fold transport
`overlapTriv C D`). The proof is pure conjugation: the inner `tripleTriv` round-trips cancel, the
base cocycle `chartTripleTransitionK_cocycle` collapses the middle, the outer `tripleTriv`
round-trip closes it. DONE, axiom-clean.

The OPERATOR additionally requested a NATURALITY lemma (their item (iv)):
"restrict_overlapTransition_to_triple_eq_tripleTransition — the restricted 2-fold
`overlapTransition C D` (transported to the triple presentation) EQUALS the directly-constructed
canonical triple transition `tripleTransition C D E`. THIS is the load-bearing lemma; with it, the
atlas's actual transition IS the canonical localization transition on the triple, so the cocycle
transfers."

The 2-fold atlas transition is
`overlapTransition C D : targetChartLoc C D ≃ₐ[k] targetChartLoc D C`
(`targetChartLoc C D = Away (C.trivK (overlapElt C D))`, an `M`-localization), built by conjugating
the base 2-fold transition through `overlapTriv`.

## The OBSTRUCTION I have found (need your adjudication)

`targetTripleLoc C D E = Away (overlapTriv C D (tripleElt C D E))` is a FURTHER localization of
`targetChartLoc C D` (localize at the image of the chart-`E` element). So there IS a canonical
localization structure map `targetChartLoc C D → targetTripleLoc C D E`, and `overlapTransition C D`
functorially induces a map on the further localizations. BUT that induced map's TARGET is
`Away (overlapTransition C D (overlapTriv C D (tripleElt C D E)))` — a localization of
`targetChartLoc D C` at the TRANSPORTED E-element. The natural name for that is `targetTripleLoc D C E`
(the chart-`D` presentation built over the `D, C` overlap, localized at E). But `tripleTransition C D E`
TARGETS `targetTripleLoc D E C` (built over the `D, E` overlap, localized at C). These are
localizations of `M` at DIFFERENT elements via DIFFERENT 2-fold transports (`overlapTriv D C` vs
`overlapTriv D E`). So a literal "restricted overlapTransition C D = tripleTransition C D E" is a
TYPE MISMATCH on the target.

To bridge `targetTripleLoc D C E ≃ targetTripleLoc D E C` I would need to prove an element-level
equality `overlapTransition C D (overlapTriv C D (tripleElt C D E)) = (something) (overlapTriv D E (...))`
ENTERING the reducible triply-localized localization elements — exactly the kernel-cost trap the
recon flagged for this `@[reducible]` triple type, and which the pure-conjugation cocycle proof
SIDESTEPS entirely.

Note the BASE-side template (Localization/Overlap.lean) did NOT build a "restrict 2-fold to triple =
triple transition" lemma. It built the triple cocycle directly by subsingleton, plus a SINGLE-CHART
restriction lemma `awayOverlapTransition_restrict_left` (restricting the 2-fold transition along ONE
chart's localization map equals the canonical single-chart map into the swapped overlap). That
single-chart restriction is provable by subsingleton (`algHom_subsingleton` at `powers f`), NO
element entry.

## My questions

1. FIDELITY: Is the directly-built `tripleTransition` (canonical base triple transition conjugated
   through canonical transports) ALREADY "the atlas's actual transition on the triple", such that
   the proved cocycle faithfully discharges the operator's "full standard coherence package" —
   i.e. is the naturality lemma (iv) a SEPARATE compatibility (nice to have) rather than REQUIRED
   for the cocycle to mean `g_jk∘g_ij=g_ik` on the triple overlap? Or is it genuinely required for
   faithfulness, such that without (iv) the cocycle is "self-consistent but not the atlas's"?

2. The target-reorder mismatch (`targetTripleLoc D C E` vs `targetTripleLoc D E C`): is this a REAL
   obstruction making (iv) unprovable AS STATED (literal equality), or merely a re-indexing that a
   canonical denominator-reorder iso resolves cleanly WITHOUT element entry (e.g. via subsingleton /
   `algHom_subsingleton` on the common base submonoid, mirroring how the base cocycle realigns
   `powers` across cyclic orders)? Is there a route to (iv) that stays at the AlgEquiv/subsingleton
   level and never enters reducible triple-localization elements?

3. If (iv) as literally stated is a wall, what is the FAITHFUL weaker-but-honest lemma that captures
   "the atlas's 2-fold transition restricts correctly to the triple" WITHOUT element entry —
   analogous to the base-side single-chart restriction `awayOverlapTransition_restrict_left`? E.g.
   the single-chart restriction `targetChartLoc C D → targetTripleLoc C D E` of `overlapTransition`
   equals a canonically-built map, provable by subsingleton. Would THAT be a faithful rendering of
   the operator's intent, or does it drop the load-bearing content?

4. VERDICT: Given the operator explicitly said "do NOT fabricate a weaker cocycle that doesn't mean
   g_jk∘g_ij=g_ik on the triple overlap" and "if naturality is unprovable as stated, STOP and report
   the precise obstruction" — should I (a) ship the proved cocycle + report (iv) as a precise
   obstruction with the target-mismatch reason, (b) attempt the subsingleton route to (iv) if you
   judge it sound, or (c) build the honest single-chart-restriction analogue instead? Pick one and
   justify.
</task>

<output_contract>
  Four numbered sections (Q1-Q4), each a crisp verdict + 2-4 sentence justification. Then a
  "DECISION" section: exactly one of (a)/(b)/(c) with the reason, and if (b) or (c), the precise
  lemma statement shape (types + the subsingleton/initiality argument) you would commit to.
</output_contract>

<grounding_rules>
  Distinguish what FOLLOWS from the localization universal property (provable, no element entry)
  from INFERENCES about Lean v4.29 defeq/instance behavior you cannot verify without the build.
  Flag guesses about Mathlib API. If (iv)-as-stated is genuinely a wall, say so plainly; do not
  salvage an unfaithful statement. Faithfulness to "the atlas's transitions satisfy g_jk∘g_ij=g_ik
  on the triple overlap" is the bar — a self-consistent but disconnected cocycle does NOT clear it.
</grounding_rules>
