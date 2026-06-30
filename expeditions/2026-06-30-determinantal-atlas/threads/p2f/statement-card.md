# Statement card — P2.f target-side triple cocycle

> **Claim.** For a constructive pivot-chart atlas of a Zariski-locally-trivial affine product, the
> canonical triple transitions on any common triple overlap `D(c)∩D(d)∩D(e)` satisfy the standard
> cocycle condition `g_jk ∘ g_ij = g_ik` (cyclic form: the cyclic composite of the three pivot-swap
> triple transitions is the identity).
>
> - **Lean:** `Algebra.AtlasChart.tripleTransition_cocycle`
>   (`lean/DLNFibre/Core/RingTheory/Determinantal/AtlasTransition.lean` @ `93e998e6`),
>   surfaced on the predicate as
>   `Algebra.IsZariskiLocallyTrivialAffineProduct.tripleTransition_cocycle`
>   (`lean/DLNFibre/Core/RingTheory/Determinantal/LocalTriviality.lean`).
> - **Gloss.** For three atlas charts `C, D, E`, the composite
>   `(tripleTransition C D E).trans (tripleTransition D E C)).trans (tripleTransition E C D)` of the
>   three target-side (model `M`) triple-overlap transitions equals `AlgEquiv.refl` — i.e. going
>   around the triple `C → D → E → C` returns to the identity. Each `tripleTransition C D E :
>   targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D E C` is the pivot-`C`→pivot-`D` change of
>   coordinates on the SAME triple overlap, built by conjugating the canonical base-side localization
>   transition through the chart trivializations — identically to the 2-fold `overlapTransition`.
> - **Proved.** The cyclic composite of the three canonical pivot-swap triple transitions is the
>   identity, unconditionally, for any three `AtlasChart`s. Automatic by localization initiality
>   (`IsLocalization.algHom_subsingleton` on the common base submonoid `powers (c·d·e)`) +
>   `AlgEquiv` groupoid laws; no localization elements entered. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** None beyond the `AtlasChart` data (each chart: `chartElt : Base` + bare-`k`
>   trivialization `trivK : Away chartElt ≃ₐ[k] M`).
> - **Cited.** None (Mathlib localization API: `IsLocalization.algEquiv`, `algHom_subsingleton`,
>   `Away.mul'`, `Away.of_associated`).
> - **Deferred.** The **naturality** tie `tripleTransition C D E = (further-localization of the
>   2-fold overlapTransition C D)` is NOT proved (roadmap **R1**). The symmetric triple presentation
>   `targetTripleLoc C D E` localizes the pivot chart at the PRODUCT `d·e`, the 2-fold
>   `targetChartLoc C D` at `d` alone, so the tie needs the `Away.mul'` refinement iso
>   `Away (d*e) ≃ (Away d) away e` + a transition-compatibility lemma. The shipped cocycle is the
>   cocycle of the **canonical** triple transitions, NOT of the restricted 2-fold transition; the
>   docstrings and the surfaced lemma name/gloss carry this caveat. (This is the bounded obstruction
>   that motivated the symmetric redesign over the operator's nested-form description — see thread.md
>   "DESIGN PIVOT".)
> - **Route.** Base-side template `Localization.awayTriple_cocycle` (subsingleton/initiality) lifted
>   to the target by conjugation through `tripleTriv`/`overlapTriv`-analogue transports; symmetric
>   triple object (localize at the non-pivot product) to make the standard pivot-swap cocycle
>   well-typed with matching composition targets. Decorrelated Codex confirmed conjugation sound,
>   target-side subsingleton-on-`M` unsound, orientation faithful.
> - **Status.** sorry-free + reviewed (fidelity reviewer approved the statements/names/proofs as
>   faithful + honest Proved/Deferred split; one docstring overclaim found and fixed @ `93e998e6`).
