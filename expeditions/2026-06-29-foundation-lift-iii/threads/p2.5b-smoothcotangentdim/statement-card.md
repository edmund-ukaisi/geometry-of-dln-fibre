# Statement card — P2.5b B4 `SmoothCotangentDim` (A6.1 second half)

The squeeze's **reverse (≥) half, second equality**: `finrank (cotangent at the base point) =
varietyDim Z`, lifted to an abstract statement at a smooth `k`-rational maximal point of a
finite-type `k`-domain `A = MvPolynomial σ k ⧸ I`. Completes A6.1's reverse half (B3 gave
`finrank (range δ) ≤ finrank (cotangent)`; B4 gives `finrank (cotangent) = varietyDim Z`). The
existing DLN reverse-inequality R6 step `finrank_cotangent_eq_varietyDim` (statement unchanged) is
re-derived from abstract B4 + the DLN smooth-`k`-point discharge; the duplicated GAP2/GAP3 dimension
bridges are re-homed to the dimension stack.

**Scope.** ONLY B4: `finrank (m.Cotangent) = varietyDim Z` at a smooth `k`-rational point. The
composition B3∘B4 into the A6.1 reverse `≥` (and then the squeeze headline P2.6) is OUT of scope.

**GUARD-first (L8).** Before fixing the abstract hypothesis shape, the existing R6 discharge (M3 +
κ/k GAP2 + GAP3 + L2a localization collapse) was re-derived in a scratch from a candidate abstract
B4, AND the DLN model was shown to discharge it (`isSmoothAt_normalFormIdeal` +
`residueFieldAtPrimeNormalFormEquiv` + the orbit-rank-locus A0 bridge). Both elaborated sorry-free
before promotion. **The forward shape pins** (no transpose pivot, unlike B1's H1): B4's chain is R6's
chain verbatim, so the hypotheses are exactly R6's inputs read abstractly.

---

## (0) The pinned abstract smooth-`k`-point hypothesis — the CRUX of this rung

> **B4's hypothesis is "the point IS smooth + `k`-rational", NOT "a smooth point exists".** The
> existence (M3 generic-smoothness density) is the concrete model's burden, discharged in the DLN
> instance — never a hypothesis of B4.

The minimal abstract input B4 needs at a maximal ideal `m` of `A = MvPolynomial σ k ⧸ I`:

- **`[Algebra.IsSmoothAt k m]`** — the point IS smooth (consumed by M3, not produced);
- **`hrat : Ideal.ResidueField m ≃ₐ[k] k`** — the point IS `k`-rational (residue field `≃ₐ[k] k`).
  This is the **genuine sub-crux**: over a non-algebraically-closed `k` (e.g. ℝ) a closed point of
  `Spec A` need only be closed-over-`k̄`; B4 demands the residue field be **exactly `k`**, the
  precise meaning of `k`-rational. (`Ideal.ResidueField m` is a Mathlib `abbrev` for
  `IsLocalRing.ResidueField (Localization.AtPrime m)`, so `hrat` feeds the κ/k tower bridge directly,
  no transport.)
- side conditions: `[PerfectField k]` (M3's residue-field formal smoothness — NO algebraic
  closedness; `ℝ` qualifies via `CharZero ⟹ PerfectField`); `[Finite σ]` (`A` finite-type;
  affine-domain dimension); `[I.IsPrime]` (`A` a domain); `hZ : vanishingIdeal Z = I` (the A0 bridge
  linking `varietyDim Z` to `ringKrullDim A`). **No `[Infinite k]`** in B4 itself — it appears only in
  the DLN discharge (where it feeds the orbit irreducibility / density existence).

**`I` is parameterized** (a prime ideal of `MvPolynomial σ k`, NOT hard-wired to `ker μ*`). Like B3's
`InfinitesimalAction`, this lets the DLN model instantiate `I = orbitIdeal M` so that
`m = normalFormIdeal M : Ideal (orbitRing M)` matches B4's `m : Ideal (MvPolynomial σ k ⧸ I)`
**definitionally** (`orbitRing M = MvPolynomial (RepCoord d) k ⧸ orbitIdeal M`), avoiding any
quotient/cotangent transport. B4 uses no deformation/carrier data, so it is a free-standing
dimension-stack fact (not on `AffineGVariety`); for the carrier orbit-image presentation
`I = ker G.pullback`, the same A0 bridge as the P2.3 A4.1 anchor applies.

## (1) Abstract B4 — the cotangent-dimension identity

> **Claim.** `finrank k (m.Cotangent) = varietyDim Z`, at a smooth `k`-rational maximal `m` of
> `A = MvPolynomial σ k ⧸ I` (`σ` finite, `I` prime), given `vanishingIdeal Z = I`.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.finrank_cotangent_eq_varietyDim`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean`)
> - **Signature:**
>   `[PerfectField k] {σ} [Finite σ] (I : Ideal (MvPolynomial σ k)) [I.IsPrime]`
>   `(m : Ideal (MvPolynomial σ k ⧸ I)) [m.IsMaximal] [Algebra.IsSmoothAt k m]`
>   `(hrat : Ideal.ResidueField m ≃ₐ[k] k) {Z} (hZ : vanishingIdeal k Z = I) :`
>   `(finrank k (m.Cotangent) : ℕ∞) = varietyDim Z`
> - **Route (R6's chain stated abstractly).** `varietyDim Z =[hZ + def] ringKrullDim A` (a finite
>   nat `n`, via `ringKrullDim_quotient_le` + `ringKrullDim_mvPolynomial_finite` bounding
>   `0 ≤ dim A ≤ card σ < ⊤`); `=[GAP3] ringKrullDim (AtPrime m)`
>   (`ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`); `=[M3] finrank κ (CotangentSpace m)`
>   (`finrank_cotangentSpace_eq_of_isSmoothAt` — the smooth-point input); `=[GAP2, hrat] finrank k
>   (CotangentSpace m)` (`finrank_eq_finrank_of_residueField_equiv`); `=[L2a] finrank k (m.Cotangent)`
>   (`Ideal.finrank_cotangentSpace_localization_eq_cotangent`).
> - **Phase-1 bricks used:** M3 `finrank_cotangentSpace_eq_of_isSmoothAt` (`Dimension/Regular`);
>   L2a `Ideal.finrank_cotangentSpace_localization_eq_cotangent` (`CotangentLocalization`); GAP2/GAP3
>   `finrank_eq_finrank_of_residueField_equiv` / `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`
>   (`Dimension/AffineDomain`, re-homed this rung); `varietyDim` (`Dimension/Codimension`). The
>   A4.1 anchor (P2.3) is a sibling in the same file (not invoked by B4, but the A0 bridge `hZ` is the
>   same input both consume).
> - **Proved.** Char carried via `[PerfectField k]` (M3 only); no `[Infinite k]`, no algebraic
>   closedness, no density (density is the DLN discharge's burden). Mechanism: a `WithBot ℕ∞`
>   finiteness extraction + the four dimension bridges.
> - **Cited.** none new.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## (2) DLN discharge of B4 — establishing the `k`-rationality over non-alg-closed `k`

> **Claim.** R6 `DLNFibre.Core.finrank_cotangent_eq_varietyDim`
> (`finrank k ((normalFormIdeal M).Cotangent) = varietyDim (canonicalCoord '' orbitRankLocus M)`,
> **signature unchanged**) is re-derived from abstract B4 at `σ = RepCoord d`, `I = orbitIdeal M`,
> `m = normalFormIdeal M`.
>
> - **Lean:** `DLNFibre.Core.finrank_cotangent_eq_varietyDim`
>   (`lean/DLNFibre/Core/OrbitTangentCotangent.lean`) — body is now a 3-line `exact` of abstract B4.
> - **How `k`-rationality is established (the sub-crux).** The smooth point comes from M3 density
>   (`OrbitSmooth`): the dense, open scheme smooth locus meets the dense orbit closed points
>   (`exists_orbitPointIdeal_isSmoothAt`), giving a smooth point that **is an orbit point**
>   `orbitPointIdeal M P`; the `G_d`-action transports its smoothness to the normal-form point
>   `m_M = orbitPointIdeal M 1` (`isSmoothAt_normalFormIdeal`). Crucially the smooth point is
>   **genuinely `k`-rational**, NOT merely closed-over-`k̄`: the orbit points are images of `k`-points
>   of the group under the orbit map, and the normal-form evaluation `orbitEval M 1 : orbitRing M → k`
>   is a **surjective `k`-algebra hom with kernel `m_M`**, so the first isomorphism theorem gives
>   `orbitRing M ⧸ m_M ≃ₐ[k] k` (`residueFieldNormalFormEquiv`), hence
>   `Ideal.ResidueField (normalFormIdeal M) ≃ₐ[k] k` (`residueFieldAtPrimeNormalFormEquiv`) — exactly
>   B4's `hrat`. So the density supplies *smoothness at a `k`-point*, and the `k`-rationality is the
>   `k`-point-ness made into the residue-field equivalence. (`OrbitSmooth` carries `[PerfectField k]
>   [Infinite k]`; `ℝ`/`ℚ` qualify, witnessed in-file on the `(2,2,2)/ℚ` tuple — non-alg-closed.)
> - **The defeq that avoids transport.** `orbitIdeal M = vanishingIdeal (orbitSet M)` (def) and
>   `orbitRing M = MvPolynomial (RepCoord d) k ⧸ orbitIdeal M` (def), so `normalFormIdeal M` has
>   exactly B4's `m` type. The A0 bridge `hZ` is `vanishingIdeal_orbitRankLocus_eq_orbitSet M`
>   (`vanishingIdeal (canonicalCoord '' orbitRankLocus M) = vanishingIdeal (orbitSet M) = orbitIdeal
>   M`, the last by def).
> - **Collapse.** The old DLN R6 chain (`exists_ringKrullDim_orbitRing_eq` + the inline
>   GAP3/M3/GAP2/L2a `have`s) is **removed** — now provided by abstract B4. The DLN-free GAP2/GAP3
>   bridges (`height_eq_ringKrullDim_of_isMaximal_fintype`,
>   `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`,
>   `finrank_eq_finrank_of_residueField_equiv`) are **re-homed** from `OrbitTangentCotangent`
>   (namespace `DLNFibre.Core`) to `Dimension/AffineDomain` (namespace `DLNFibre.Core.Dimension`,
>   their true low-level home, next to the `Fin`-indexed L4d they lift). The DLN-specific
>   `residueFieldAtPrimeNormalFormEquiv` stays (the discharge's `k`-rationality witness).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## (3) Consumer sweep (L2)

- **R6 `finrank_cotangent_eq_varietyDim`** — signature unchanged; A6.1 headline
  `finrank_range_deformationδ_le_varietyDim` (same file) consumes it unchanged (axiom-clean,
  verified). `VoigtDischarge` consumes the A6.1 headline unchanged.
- **Re-homed GAP2/GAP3 bridges** — the only external consumers `FibreDimFibration` and
  `FibreSmoothBlock` reference them **unqualified** under `open DLNFibre.Core.Dimension` (resp.
  `open Dimension`), so they resolve to the new `Dimension/AffineDomain` home; both green in the full
  build. (`rg` for qualified `DLNFibre.Core.<helper>` references = 0; ambiguity avoided by removing
  the old `DLNFibre.Core` copies.)
- **`exists_ringKrullDim_orbitRing_eq`** removed — `rg` = 0 references outside the deleted block.

## Files

- EDIT `lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Dimension.lean` (+135/−~12) — module
  docstring expanded for B4; added the abstract `finrank_cotangent_eq_varietyDim` (B4) in namespace
  `AlgebraicGeometry.Group.Orbit` (bare Mathlib-mirror, L7) alongside the P2.3 A4.1 anchor; added the
  3 dimension-stack imports (`Regular`, `CotangentLocalization`, `AffineDomain`).
- EDIT `lean/DLNFibre/Core/Dimension/AffineDomain.lean` (+62) — re-homed the 3 DLN-free dimension
  bridges (`height_eq_ringKrullDim_of_isMaximal_fintype`,
  `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`, `finrank_eq_finrank_of_residueField_equiv`)
  next to the `Fin`-indexed L4d they generalise; `@[stacks 00OS]`-adjacent, name=content.
- EDIT `lean/DLNFibre/Core/OrbitTangentCotangent.lean` (−~150 net) — removed the 3 re-homed bridges +
  `exists_ringKrullDim_orbitRing_eq` + the inline R6 chain; R6 now a 3-line transport of abstract B4
  + the DLN discharge; import `Orbit.Dimension`. R6/A6.1 statements unchanged.

## Gates

- Full aggregator build `scripts/lb DLNFibre` — green, **3826 jobs**.
- `scripts/sorries` — **0** sorry / 0 axiom / 0 native_decide / 0 #exit.
- `#print axioms` = `[propext, Classical.choice, Quot.sound]` on: abstract B4
  `AlgebraicGeometry.Group.Orbit.finrank_cotangent_eq_varietyDim`; the re-derived R6
  `DLNFibre.Core.finrank_cotangent_eq_varietyDim`; the re-homed bridges
  `height_eq_ringKrullDim_of_isMaximal_fintype` / `finrank_eq_finrank_of_residueField_equiv`; the
  A6.1 headline `finrank_range_deformationδ_le_varietyDim` (consumes R6).
- L7 (bare Mathlib-mirror namespace `AlgebraicGeometry.Group.Orbit`), L2 sweep (re-homed-bridge `rg`
  consumers retarget cleanly; removed `exists_ringKrullDim_orbitRing_eq` `rg` = 0), L4 (codepoint
  long-line: my regions clean — reflowed the B4 + AffineDomain docstrings), L6 (full-build green),
  L8 (GUARD-first: scratch discharge pinned the forward shape before promotion).

## Decorrelated-review focus (controller CRUX review)

1. **Is `hrat : Ideal.ResidueField m ≃ₐ[k] k` the faithful `k`-rationality content** (residue field
   is exactly `k`), or does it smuggle the conclusion? — It is the standard `k`-rational-point
   condition; the DLN discharge *proves* it from the surjective orbit-evaluation (first iso), not
   assumes it. Over non-alg-closed `k`, this is the load-bearing distinction (closed-over-`k̄` would
   NOT suffice).
2. **Is "the point IS smooth + `k`-rational" (not "exists") the right B4 boundary?** — yes; existence
   is the M3 density argument, confined to the DLN discharge (`OrbitSmooth`), correctly out of B4.
3. **Is parameterizing `I` honest** (vs hard-wiring `ker μ*`)? — yes; `I = orbitIdeal M` for the DLN
   instance, the parameterization buys the defeq `m = normalFormIdeal M` (no transport), the engine is
   named generically. Mirrors B3's `InfinitesimalAction` `I`-parameterization (Codex-blessed in P2.5a).
4. **Is the GAP2/GAP3 re-home sound?** — the 3 bridges are genuinely DLN-free general dimension facts
   (any `MvPolynomial σ k ⧸ I`); their true home is the dimension stack next to L4d, not the DLN
   `OrbitTangentCotangent`. Consumers retarget via existing `open`; full build green.

## What P2.6 needs (flag, NOT built here)

P2.6 assembles the squeeze headline `varietyDim Z = finrank (range δ)` from:
- **B1** `genericRankBound` (A4.3 `≤`, on `AffineGVarietyDeformation`) + **A4.1/A4.2** anchor
  (`varietyDim = trdeg ≤ genericDifferentialRank`) for the `≤` half;
- **B3** `finrank (range δ) ≤ finrank (m.Cotangent)` (on `InfinitesimalAction`, `m = H.basePtIdeal`)
  ∘ **B4** `finrank (m.Cotangent) = varietyDim Z` (this rung) for the reverse `≥` half — compose at
  `σ = G.ρ`, `I = H`'s `InfinitesimalAction` ideal, `m = H.basePtIdeal`, supplying B4's smooth-point
  hypotheses (the model discharges via M3 density) and `hZ`;
- `le_antisymm` + the `ℕ∞`/`ℕ` cast already in `VoigtDischarge`.
The DLN squeeze headline already exists (R6 + A6.1 + A4 + VoigtDischarge); P2.6's job is the
*abstract* assembly on the carrier so the engine is consumer-free. B4 is the last engine brick.
