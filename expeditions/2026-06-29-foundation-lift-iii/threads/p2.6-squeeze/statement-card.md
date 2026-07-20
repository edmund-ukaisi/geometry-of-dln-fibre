# Statement card — P2.6 the abstract orbit-dimension squeeze headline (the Phase-2 capstone)

The Phase-2 capstone: the **abstract orbit-dimension theorem** `varietyDim Z = finrank k (range G.δ)`
on the deformation carrier `AffineGVarietyDeformation k`, assembled by `le_antisymm` from the four
landed-and-reviewed bricks (B1, B3, B4) + the A4.1 anchor + the Phase-1 trdeg bound. The DLN
`VoigtDischarge` squeeze (`varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`, signature
unchanged) is re-derived as the first instance, discharging the full hypothesis bundle. Folds the two
cosmetic non-blockers: an in-file B4 non-vacuity witness + a stale-docstring fix.

**This completes the Phase-2 orbit-dimension engine** (carrier + anchors + 4 bricks + the abstract
squeeze headline), DLN-free and consumer-free.

---

## (1) The abstract squeeze headline — the Phase-2 capstone

> **Claim.** On `G : AffineGVarietyDeformation k`, the variety dimension of an orbit-image closure `Z`
> equals the dimension of the deformation tangent image: `varietyDim Z = finrank k (range G.δ)`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.varietyDim_eq_finrank_range_δ`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Squeeze.lean`, NEW)
> - **Signature (the full hypothesis bundle — name = content, NONE hidden; minimal char typeclass:
>   `[PerfectField k]` only, NO `[CharZero k]` — see the review finding below):**
>   `[PerfectField k] (G : AffineGVarietyDeformation k) [Finite G.ρ]`
>   `(δAdj : G.C1 →ₗ[k] G.C0) (L : (Frac G.R ⊗[k] G.C0) →ₗ[Frac G.R] Ω[Frac G.R⁄k])`
>   `(hMC : G.DifferentialFactors δAdj L) (hRank : finrank (range δAdj) = finrank (range G.δ))`
>   `(hcrit : DiffIndepCriterion k G.R) {I : Ideal (MvPolynomial G.ρ k)} (H : G.InfinitesimalAction I)`
>   `[FiniteDimensional k (H.basePtIdeal).Cotangent] [hI : I.IsPrime] [hm : (H.basePtIdeal).IsMaximal]`
>   `[Algebra.IsSmoothAt k (H.basePtIdeal)] (hrat : Ideal.ResidueField (H.basePtIdeal) ≃ₐ[k] k)`
>   `{Z : Set (G.ρ → k)} (hZ : vanishingIdeal k Z = I) (hIker : I = ker G.pullback.toRingHom) :`
>   `varietyDim Z = (finrank k (range G.δ) : ℕ∞)`.
> - **The hypothesis bundle (all INPUTS the DLN instance discharges; name = content):**
>   - **(H1)** `δAdj`, `L`, `hMC` (the transpose Maurer–Cartan factorisation) + `hRank` (rank-tie) — B1's inputs;
>   - **char-0 criterion** `hcrit : DiffIndepCriterion k G.R` — the A4.2 content, carried as an
>     explicit input (at the abstract level this is the ONLY char hypothesis; the DLN instance
>     discharges it via `diffIndepCriterion_groupRing`, where `[CharZero k]` is the exact line and
>     `[PerfectField]` would be FALSE, banked Phase-1 finding);
>   - **(H2)** `H : G.InfinitesimalAction I` (dual-number ideal-killing) + `[FiniteDimensional k m.Cotangent]` — B3's input;
>   - **smooth `k`-rational point** at `m = H.basePtIdeal`: `[m.IsMaximal]`, `[IsSmoothAt k m]`,
>     `hrat` (residue field `≃ₐ[k] k`) + `[PerfectField k]` (M3) — B4's inputs (the point IS smooth, NOT an existence claim);
>   - **A0/orbit↔kernel bridges**: `hZ`, `hIker`; carrier hyps `[Finite G.ρ]`, `[I.IsPrime]`.
> - **The `≤`/`≥` composition (`le_antisymm`):**
>   - **`≤`**: `varietyDim Z =[A4.1 `varietyDim_eq_trdeg_of_eq_ker`, via `hZ.trans hIker`]`
>     `(trdeg k G.pullback.range).toNat`; `=[range_pullback] (trdeg k (adjoin k (range fρ))).toNat`
>     `≤[Phase-1 `trdeg_adjoin_le_genericDifferentialRank`, via `hcrit`] genericDifferentialRank k G.R G.fρ`
>     `≤[B1 `genericRankBound`, via `hMC`+`hRank`] finrank (range G.δ)`; cast `ℕ → ℕ∞` (`exact_mod_cast`).
>   - **`≥`**: `finrank (range G.δ) ≤[B3 `finrank_range_δ_le_finrank_cotangent`, via `H`] finrank (m.Cotangent)`
>     `=[B4 `finrank_cotangent_eq_varietyDim`, via `hrat`+`hZ`] varietyDim Z`; B3 in `ℕ`, cast up.
> - **Object-eq vs finrank-eq.** The conclusion is an `ℕ∞` object-equality `varietyDim Z = ↑(finrank …)`;
>   the RHS finrank is a `ℕ` cast in. The intermediate `genericDifferentialRank`/B3 bounds live in `ℕ`; the
>   casts are explicit (`exact_mod_cast`), never silent.
> - **Proved.** From the landed bricks + Phase-1 facts; no new mathematical content (pure assembly). The
>   bricks (B1/B3/B4, the A4.1 anchor, the Phase-1 trdeg bound) were each independently reviewed in P2.3/P2.4/P2.5.
> - **Cited.** none. **Monument-free:** no Aoyagi/RLCT axiom enters.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## (2) DLN `VoigtDischarge` squeeze — re-derived from the headline

> **Claim.** `DLNFibre.Core.varietyDim_orbitRankLocus_eq_finrank_range_deformationδ` —
> **signature unchanged** (`[CharZero k] (M : Tuple d) : varietyDim (canonicalCoord '' orbitRankLocus M)`
> `= (finrank k (range (deformationδ M M)) : ℕ∞)`) — re-derived from the abstract headline at the DLN
> deformation instance `dlnOrbitDef M`.
>
> - **Lean:** `DLNFibre.Core.varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`
>   (`lean/DLNFibre/Core/VoigtDischarge.lean`)
> - **The full discharge.** The matrix tuple supplies every bundle input: (H1) `dlnOrbitDef_differentialFactors M`
>   (adjoint `deltaT M`, `L` the `pairMC` lift, inferred from `hMC`'s type), rank-tie `finrank_range_deltaT M`;
>   the criterion `diffIndepCriterion_groupRing`; (H2) `dlnInfinitesimalAction M`; the smooth `k`-rational
>   point — `[m.IsMaximal]` = `orbitPointIdeal_isMaximal M 1`, `[IsSmoothAt]` = `isSmoothAt_normalFormIdeal M`,
>   `hrat` = `residueFieldAtPrimeNormalFormEquiv M`; the cotangent finiteness
>   `finiteDimensional_cotangent_normalFormIdeal M`; A0 `vanishingIdeal_orbitRankLocus_eq_orbitSet M`; the
>   orbit↔kernel linkage `hIker : orbitIdeal M = ker (dlnOrbitDef M).pullback` (`range_orbitMap` +
>   `vanishingIdeal_range_orbitMap_eq_ker`). `(dlnInfinitesimalAction M).basePtIdeal = normalFormIdeal M`
>   and `(dlnOrbitDef M).δ = deformationδ M M` **definitionally**, so the abstract conclusion IS this statement.
> - **The whnf-timeout fix (Codex-diagnosed).** A monolithic `exact` of the headline timed out at `whnf`
>   (even at 1M heartbeats). Cause: instance search across the defeq `H.basePtIdeal ≡ normalFormIdeal M`
>   + an implicit-`L` metavariable. Fix: pass instances explicitly via `@`-application keyed SYNTACTICALLY on
>   `H.basePtIdeal` (frozen by `set H`), provide `Finite (dlnOrbitDef M).ρ` explicitly, and leave `L` implicit
>   (inferred from `dlnOrbitDef_differentialFactors M`'s type — the private `pairMC` need not be named). No
>   heartbeat bump (band-aid rejected). Collapses the old `le_antisymm` of the two DLN halves into one
>   transport of the abstract headline.
> - **Consumers (L2 sweep).** All downstream consumers of the squeeze green unchanged: L7
>   `codimRep_orbitRankLocus_eq_orbitLinearCodim` (same file), the unconditional headlines
>   `codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1_unconditional` /
>   `…_eq_multSum_unconditional`, the `(2,2,2)/ℝ`/`AlgebraicClosure ℚ` witnesses. Full aggregator build green.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]` (monument-free — no Aoyagi).

## (3) B4 non-vacuity witness — the affine point `Spec ℚ` (bedrock §2.1)

> **Claim.** A self-contained, **non-DLN** in-file `example` firing abstract B4
> (`finrank_cotangent_eq_varietyDim`) at the affine point: `σ = Empty`, `I = ⊥`,
> `A = MvPolynomial Empty ℚ ⧸ ⊥ ≃ₐ[ℚ] ℚ` (a field), `m = ⊥`, `Z = univ`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.B4Witness.*`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean`, NEW namespace + final `example`)
> - **Every B4 antecedent shown satisfiable in-file:** `[I.IsPrime]` (`Ideal.bot_prime`); `[m.IsMaximal]`
>   (`pointRing ⧸ ⊥` is a field, transported from `ℚ`); `[Algebra.IsSmoothAt ℚ ⊥]` (`pointRing ≃ₐ[ℚ] ℚ`
>   is formally smooth over `ℚ`, localization preserves it); `hrat : ResidueField ⊥ ≃ₐ[ℚ] ℚ` (the
>   genuinely `ℚ`-rational residue field, via the `IsFractionRing`-bijectivity-of-a-field trick); A0
>   `hZ : vanishingIdeal univ = ⊥` (`ℚ` infinite, `MvPolynomial.funext`). `finrank (m.Cotangent) = 0 = varietyDim univ`.
> - **Why this and not the DLN instance.** The DLN model is a witness, but it is network-coupled and lives
>   elsewhere; bedrock §2.1 wants an in-file witness that the antecedent bundle is satisfiable — this is a
>   tiny, free-standing, non-DLN model in the same file as B4.
> - **Status.** sorry-free; new imports `Mathlib.RingTheory.Smooth.Basic`,
>   `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Mathlib.Algebra.MvPolynomial.Funext` (all lightweight Mathlib).

## (4) Stale docstring fix

> `lean/DLNFibre/Core/FibreDimFibration.lean:82` — the bridge `height_eq_ringKrullDim_of_isMaximal_fintype`
> was re-homed (P2.5b) from `OrbitTangentCotangent` to `Dimension/AffineDomain` (ns `DLNFibre.Core.Dimension`);
> the docstring reference `OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype` is corrected to
> `Dimension.height_eq_ringKrullDim_of_isMaximal_fintype`. L2 sweep: no other stale references (`rg` = 0).

---

## Files

- NEW `lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Squeeze.lean` — the abstract squeeze headline
  `varietyDim_eq_finrank_range_δ`. Bare Mathlib-mirror namespace `AlgebraicGeometry.Group.Orbit` (L7).
  Imports `Orbit.{Deformation,Dimension}` + `Dimension.Trdeg`. Enters the aggregator transitively via
  `VoigtDischarge` (which now imports it).
- EDIT `lean/DLNFibre/Core/VoigtDischarge.lean` (+36/−5) — import `Orbit.Squeeze`; re-derive the DLN squeeze
  from the abstract headline (the `@`-application + the whnf-fix). Squeeze + all consumers signature-unchanged.
- EDIT `lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean` (+~75) — the `B4Witness` namespace +
  the firing `example`; 3 lightweight Mathlib imports.
- EDIT `lean/DLNFibre/Core/FibreDimFibration.lean` (docstring only) — the stale bridge home reference.

## Gates

- Full aggregator build `scripts/lb DLNFibre` — green (~3800 jobs).
- `scripts/sorries` — 0 sorry / 0 axiom / 0 native_decide / 0 #exit.
- `#print axioms` = `[propext, Classical.choice, Quot.sound]` on: the abstract headline
  `varietyDim_eq_finrank_range_δ`; the re-derived DLN squeeze
  `varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`. **Monument-free** — no Aoyagi/RLCT axiom in
  the squeeze (confirmed: the axiom set is exactly the three logical axioms).
- L7 (bare Mathlib-mirror namespace), L2 sweep (consumers + stale-ref `rg`), L4 (codepoint long-line: my
  regions clean), L6 (full-build green).

## Decorrelated-review focus (controller / reviewer)

1. **Is the hypothesis bundle the honest minimal conjunction** (name = content), with NONE hiding a cited
   step? — every hypothesis is an explicit `input` the DLN instance discharges; the bricks were each
   reviewed; no Aoyagi axiom enters.
2. **Object-eq vs finrank-eq + the casts.** The `ℕ∞` conclusion and the `ℕ` intermediate bounds are bridged
   by explicit `exact_mod_cast`; confirm no silent coercion or off-by-cast.
3. **Is the DLN re-derivation faithful** (squeeze signature unchanged, all consumers green, defeqs sound)?
   — `(dlnInfinitesimalAction M).basePtIdeal = normalFormIdeal M` and `(dlnOrbitDef M).δ = deformationδ M M`
   by `rfl`; the whnf-fix is an elaboration guidance, not a mathematical change.
4. **Is the B4 witness genuinely non-vacuous** (a real model, all antecedents proved not assumed)? — the
   `Spec ℚ` point, every antecedent constructed.

## Decorrelated review outcome — SURVIVED (+ one precision finding, FIXED)

Decorrelated reviewer (opus + own xhigh Codex) verdict: **SURVIVED.** Q1 name=content CLEAN, Q2
composition/casts SOUND, Q3 monument-free CONFIRMED (both headlines exactly `[propext, Classical.choice,
Quot.sound]`), Q4 DLN re-derivation faithful (signature byte-identical, defeqs sound), Q5 B4 witness
genuinely non-vacuous. **One precision finding (FIXED in this thread before commit):** `[CharZero k]` was a
**dead hypothesis on the abstract headline** — the char-0 content is carried entirely by the explicit
input `hcrit : DiffIndepCriterion k G.R`; B4 needs only `[PerfectField k]`. Reviewer + Codex independently
flagged it and the reviewer build-confirmed removal is green. Tightened: the abstract headline now carries
`[PerfectField k]` only (the weakest char typeclass that suffices), `hcrit` carrying the char-0 content;
docstrings + card corrected; the banned word "honestly" dropped from the `Squeeze.lean` section header.
(At the DLN level `[CharZero k]` stays load-bearing — it supplies `[PerfectField k]`/`[Infinite k]` and
discharges `hcrit` — so the DLN squeeze signature is unchanged.) Review artefact:
`threads/p2.6-squeeze/codex/bundle-and-casts-{prompt,answer}.md`.
