# Statement card — P2.5a B3 `CotangentInjection` (A6.1 first half) on `AffineGVarietyDeformation`

The squeeze's **reverse (≥) half, first inequality**: `finrank (range δ) ≤ finrank (cotangent at the
base point)`, lifted to the abstract deformation carrier with the infinitesimal-action data (H2) as a
**named hypothesis bundle** the DLN matrix-tuple discharges. The existing DLN reverse-inequality R5
step `finrank_range_deformationδ_le_finrank_cotangent` (statement unchanged) is re-derived from the
abstract B3 + the DLN (H2) discharge; the duplicated DLN-specific R3–R5 chain is collapsed.

**Scope.** This is ONLY the first inequality `finrank (range δ) ≤ finrank (cotangent)`. The
`= varietyDim` half (B4 `SmoothCotangentDim`, smooth `k`-point + density) is the NEXT rung P2.5b — out
of scope here. The B3 engine needs ONLY `[FiniteDimensional k m.Cotangent]`, NOT a smooth point.

**CRUX outcome (GUARD-first, L8):** unlike B1's (H1) — where the forward shape was undischargeable and
the transpose/adjoint carrier was needed — the **forward (H2) shape PINS**. The GUARD scratch
(uncommitted) built BOTH the DLN discharge of the candidate forward (H2) AND the full abstract B3 from
it, sorry-free, before promotion. No pivot. **This is the controller-routed decorrelated-review CRUX:
the pinned (H2) signature + the discharge are below.**

---

## (0) The (H2) infinitesimal-action hypothesis bundle — pinned forward shape

> **Claim.** A `structure InfinitesimalAction (I : Ideal (MvPolynomial G.ρ k))` over the carrier `G`,
> bundling the abstract directional-derivative-at-base-point data.
>
> - **Lean:** `AlgebraicGeometry.Group.Orbit.AffineGVarietyDeformation.InfinitesimalAction`
>   (`lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Deformation.lean`)
> - **Gloss (the pinned fields).**
>   - `basePt : MvPolynomial G.ρ k →ₐ[k] k` — evaluation at the base `k`-point;
>   - `dirDeriv : G.C0 →ₗ[k] (MvPolynomial G.ρ k →ₗ[k] k)` — directional-derivative functional,
>     `k`-linear in the direction `φ ∈ C0`;
>   - `c1coord : G.C1 →ₗ[k] (G.ρ → k)` + `hc1coord : Function.Injective c1coord` — the coordinate map;
>   - `hkill : ∀ φ f, f ∈ I → dirDeriv φ f = 0` (R2★: each `dirDeriv φ` kills the orbit ideal);
>   - `hbase : ∀ f, f ∈ I → basePt f = 0` (the base point lies on the orbit closure);
>   - `hLeibniz : dirDeriv φ (f*g) = basePt f · dirDeriv φ g + basePt g · dirDeriv φ f`;
>   - `hcoord : dirDeriv φ (X x) = c1coord (G.δ φ) x` (coordinate test).
> - **name = content.** (H2) is an abstract **INPUT** the concrete model discharges — NOT a consequence
>   of a bare orbit map (the dual-number infinitesimal curve `1 + εφ` and its ideal-killing are model
>   facts). The ideal `I` is parameterized (the concrete model's orbit ideal); for DLN `I = orbitIdeal
>   M = ker pullback` (equal by theorem). Conditional docstring.
> - **The forward shape PINS (vs B1's transpose pivot).** B1's forward (H1) was undischargeable because
>   `range (L ∘ δ.bc) = L(range δ)` saw only the coboundary image; B3's `dirDeriv`/`c1coord` carry the
>   geometric content directly — the coordinate test recovers `δ φ`'s components from `dirDeriv φ` and
>   the injective `c1coord`, no adjoint/transpose needed. Verified by the GUARD scratch (discharge body
>   = the existing R2★/Leibniz lemmas, no `deltaT`/`dualMap`).
> - **Status.** structure (data) + the field props are hypotheses; sorry-free.

## (1) Abstract B3 — the cotangent injection (A6.1 first half)

> **Claim.** From `H : G.InfinitesimalAction I`, with `[FiniteDimensional k (H.basePtIdeal).Cotangent]`:
> `finrank k (range G.δ) ≤ finrank k ((H.basePtIdeal).Cotangent)`,
> where `m = H.basePtIdeal = ker (basePt descended to A = MvPolynomial ρ k ⧸ I)`.
>
> - **Lean:** `…InfinitesimalAction.finrank_range_δ_le_finrank_cotangent`
>   (`…/Orbit/Deformation.lean`)
> - **Route (the supporting chain, all in the same engine).** Descend `dirDeriv`/`basePt` to `A`
>   (`dirDerivQuot`/`basePtA`, kills `I`); `m = ker basePtA`; build the cotangent functional
>   `cotFunctional φ : m.Cotangent →ₗ k` (Leibniz vanishing: `basePtA x = basePtA y = 0` for `x,y ∈ m`);
>   the pairing `cotPairing : C0 →ₗ Dual k m.Cotangent`; the coordinate-test class `X x − C (basePt(X
>   x)) ∈ m` recovers `cotPairing φ (test x) = c1coord (δ φ) x` (`cotPairing_coordTest`); so
>   `ker cotPairing ≤ ker δ` (`ker_cotPairing_le_ker_δ`, via injectivity of `c1coord`); rank–nullity for
>   `δ` and `cotPairing` (same domain `C0`) + `range cotPairing ⊆ Dual k m.Cotangent` + `finrank (Dual k
>   V) = finrank V` (`Subspace.dual_finrank_eq`) close it (`omega`).
> - **Assumed.** `[FiniteDimensional k (H.basePtIdeal).Cotangent]` (the ONLY analytic input — the
>   smooth-`k`-point / `= varietyDim` half is B4, kept out); (H2) as the hypothesis bundle.
> - **Proved.** Char-free; no smooth-point, no density, no perfect field. Mechanism: rank–nullity +
>   `Subspace.dual_finrank_eq` + `Ideal.Cotangent.lift`/`Submodule.liftQ`.
> - **Cited.** none new. Mathlib `Subspace.dual_finrank_eq`, `Ideal.Cotangent.lift`,
>   `LinearMap.finrank_range_add_finrank_ker`, `Submodule.finrank_mono`/`finrank_le`.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## (2) DLN discharge of (H2)

> **Claim.** The DLN deformation instance `dlnOrbitDef M` satisfies `InfinitesimalAction (orbitIdeal M)`
> with `basePt = aeval (canonicalCoord (1 • M))`, `dirDeriv = dirDeriv M`, `c1coord = canonicalCoord d`.
>
> - **Lean:** `DLNFibre.Core.dlnInfinitesimalAction` (`lean/DLNFibre/Core/OrbitTangentCotangent.lean`)
> - **Proved.** The fields are the LANDED reverse-inequality lemmas, unchanged: `hkill` =
>   `dirDeriv_orbitIdeal_eq_zero` (R2★, the dual-number `1 + εφ` certificate); `hbase` =
>   `eval_orbitPoint_mem_orbitIdeal M 1`; `hLeibniz` = `dirDeriv_mul` (with `one_smul`); `hcoord` =
>   `dirDeriv_X`; φ-linearity of `dirDeriv` = `dirDeriv_add`/`dirDeriv_smul`; `c1coord` injective =
>   `(canonicalCoord d).injective`.
> - **The defeq that avoids transport.** `basePt = aeval (canonicalCoord (1 • M))` is *syntactically*
>   the map defining `orbitEval M 1`, so the descended `basePtA = orbitEval M 1` and the base ideal
>   `H.basePtIdeal = ker (orbitEval M 1) = normalFormIdeal M` **definitionally** (`rfl`). With
>   `I = orbitIdeal M`, the quotient `A` is `orbitRing M` definitionally — no quotient/cotangent
>   transport (Codex-confirmed wiring choice (B): parameterize `I`, instantiate to `orbitIdeal M`).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

## (3) DLN R5 re-derivation (the existing reverse-inequality step)

> **Claim.** `finrank_range_deformationδ_le_finrank_cotangent` — **signature unchanged** —
> `finrank (range (deformationδ M M)) ≤ finrank ((normalFormIdeal M).Cotangent)` — re-derived from
> abstract B3 + the discharge.
>
> - **Lean:** `DLNFibre.Core.finrank_range_deformationδ_le_finrank_cotangent`
>   (`lean/DLNFibre/Core/OrbitTangentCotangent.lean`)
> - **Proved.** `haveI : FiniteDimensional k ((dlnInfinitesimalAction M).basePtIdeal).Cotangent :=`
>   `finiteDimensional_cotangent_normalFormIdeal M` (defeq `m = normalFormIdeal M`), then
>   `exact (dlnInfinitesimalAction M).finrank_range_δ_le_finrank_cotangent`. `(dlnOrbitDef M).δ =
>   deformationδ M M` by `rfl`, `m = normalFormIdeal M` by `rfl` — the abstract bound IS this statement.
> - **Collapse.** The old DLN R3–R5 chain (`dirDerivQuot`, `dirDerivQuot_mk`, `dirDerivQuot_mul`,
>   `cotFunctional`, `cotFunctional_toCotangent`, `coordTest_mem_normalFormIdeal`, `cotPairing`,
>   `cotPairing_coordTest`, `ker_cotPairing_le_ker_deformationδ`) is **removed** — now provided by the
>   abstract engine. Kept (the discharge inputs): `dirDeriv`/`dirDeriv_X`/`dirDeriv_mul`/`dirDeriv_add`/
>   `dirDeriv_smul`/`dirDeriv_C`/`dirDeriv_orbitIdeal_eq_zero`/`finiteDimensional_cotangent_normalFormIdeal`.
> - **Consumers (sweep).** R6 `finrank_cotangent_eq_varietyDim`, A6.1 headline
>   `finrank_range_deformationδ_le_varietyDim` (same file), and `VoigtDischarge` consume R5 unchanged.
>   Full aggregator build green. None of the removed lemmas had external consumers (`rg` = 0).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## Files

- EDIT `lean/DLNFibre/Core/AlgebraicGeometry/Group/Orbit/Deformation.lean` (+217/−5) — module docstring
  expanded for B3; added (H2) `InfinitesimalAction` structure + the engine chain (`basePtA`,
  `basePtIdeal`, `dirDerivQuot`(+`_mk`/`_mul`), `cotFunctional`(+`_toCotangent`), `dirDeriv_one`/`_C`,
  `basePt_C`, `coordTest_mem`, `cotPairing`, `cotPairing_coordTest`, `ker_cotPairing_le_ker_δ`,
  `finrank_range_δ_le_finrank_cotangent`). Bare Mathlib-mirror namespace `AlgebraicGeometry.Group.Orbit`
  (L7). B1 (P2.4) untouched.
- EDIT `lean/DLNFibre/Core/OrbitTangentCotangent.lean` (+~150/−~120 net; 182 lines changed) — import
  `OrbitDifferentialRank` (for `dlnOrbitDef`); add `dlnInfinitesimalAction` (the (H2) discharge); rewire
  R5's body to the abstract B3; remove the duplicated DLN R3–R5 chain; R5 statement + R6/A6.1 unchanged.

## Gates

- Full aggregator build `scripts/lb DLNFibre` — green, **3826 jobs**.
- `scripts/sorries` — **0** sorry / 0 axiom / 0 native_decide / 0 #exit.
- `#print axioms` = `[propext, Classical.choice, Quot.sound]` on: abstract B3
  `finrank_range_δ_le_finrank_cotangent`; the discharge `dlnInfinitesimalAction`; the re-derived R5
  `finrank_range_deformationδ_le_finrank_cotangent`.
- L7 (bare namespace `AlgebraicGeometry.Group.Orbit`), L2 sweep (removed-lemma `rg` = 0 external; new
  names `InfinitesimalAction`/`dlnInfinitesimalAction` no sibling clash), L4 (codepoint long-line: my
  regions clean; pre-existing >100cp docstrings in R6/A6.1 untouched), L6 (full-build green).

## CRUX FINDING — the forward (H2) PINS (no transpose pivot), feeding decorrelated review

**The forward (H2) is dischargeable** (contrast B1's (H1), which needed the transpose). The
asymmetry: B1's (H1) forward `span ≤ range (L ∘ δ.bc)` could only see `L(range δ)` (the coboundary
image), failing the bound; B3's (H2) carries the directional derivative `dirDeriv φ` and an injective
coordinate map `c1coord` **directly**, so the coordinate test `dirDeriv φ (X x) = c1coord (δ φ) x`
recovers each component of `δ φ` and `ker cotPairing ≤ ker δ` follows by injectivity — no adjoint, no
rank-tie, no `deltaT`/`dualMap`. The GUARD scratch confirmed both the DLN discharge of this forward
(H2) AND the full abstract B3 from it, sorry-free, before any promotion (L8 GUARD-first satisfied; no
contorted signature forced).

**Decorrelated-review focus (the (H2) shape + discharge):**
1. Is the (H2) bundle faithful to the dual-number infinitesimal-action content (R2★ + Leibniz at the
   base point + the `1 + εφ`-curve coordinate identity), or does any field smuggle in the conclusion?
   (The `dirDeriv` IS the ε-coefficient functional; `hcoord` IS `dirDeriv_X`; `hkill` IS R2★.)
2. Is parameterizing `I` (vs hard-coding `ker pullback`) honest? — Codex (B): yes, `I = orbitIdeal M =
   ker pullback` for DLN (equal by theorem), and the parameterization buys the defeq `m = normalFormIdeal
   M` that avoids transport; the engine is named generically.
3. Is `[FiniteDimensional k m.Cotangent]` the minimal/correct B3 input (NOT smuggling B4's smooth point)?
   — yes; the finrank bound uses only finite-dimensionality (`Subspace.dual_finrank_eq`).

## Hooks B4 (P2.5b) will need (flag, NOT built here)

The `= varietyDim` half (B4 `SmoothCotangentDim`) needs, abstractly:
- a **smooth `k`-rational point** at `m` (the abstract analogue of `isSmoothAt_normalFormIdeal` +
  `residueFieldAtPrimeNormalFormEquiv`: residue field `≃ₐ[k] k`, `IsSmoothAt k m`);
- the cotangent-dimension bridge `finrank k m.Cotangent = varietyDim Z` — the DLN concrete is the
  EXISTING `finrank_cotangent_eq_varietyDim` (R6, untouched here), which already chains L2a localization
  collapse + the κ/k bridge (GAP2) + M3 (`finrank_cotangentSpace_eq_of_isSmoothAt`) + GAP3 + L6.4. B4
  should lift R6 onto the carrier with the smooth-point + `k`-rational-residue-field hypotheses;
- `[PerfectField k] [Infinite k]` (M3's perfect-field generic-smoothness density; not needed for B3).

B3 (this rung) is the strict first inequality; B4 supplies `finrank m.Cotangent = varietyDim`, and the
two compose (via the existing A6.1 headline `finrank_range_deformationδ_le_varietyDim`) for the full
reverse `≥`.
