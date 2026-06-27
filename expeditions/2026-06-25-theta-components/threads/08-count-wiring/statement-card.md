# Statement card — fibre-θ count wiring: the reusable localization-survival keystone + W3/chart-e/W2-avoidance rungs

Thread 08 (fibre-count wiring tide). Branch `expedition/theta-components`, base commit `4476b2c1`
(+ uncommitted: `lean/DLNFibre/Core/{TopDimMinPrimesLocalization, TopDimMinPrimesRadical,
TopDimMinPrimesChartE, TopDimMinPrimesGfibAvoid}.lean`). All theorems below build green, sorry-free,
axiom-clean (`[propext, Classical.choice, Quot.sound]`). Modules NOT yet wired into `DLNFibre.lean`
(single-writer aggregator — controller to add the four imports at the end).

**Status: `reviewed`.** Reviewer fidelity+soundness pass SURVIVED (all four modules faithful; no
card overclaim). The keystone's `hper` confirmed required-and-honest via a decorrelated-Codex
counterexample (`A = k[t]_(t) × k[t]`, `f = (t,1)`: `hdim`+`havoid` hold but `hper` fails — a
DVR-at-uniformizer realization), so it is neither vacuous nor conclusion-baking.

---

## What this tide is

Builds the **keystone reusable localization-survival lemma** for `TopDimMinPrimes` (the rung shared
by W1 and W2 of the count chain), plus three further rungs that compose toward `numTop(fibre d E_r) =
cTheta(d−r)`: the **W3 radical wire**, the **chart-`e` ring-equiv wire**, and the **W2 avoidance
certificate**. The two genuinely-remaining pieces — the **W0 indexing bridge** and the full **W2/W1
survival applications** — are precisely characterized in "The remaining wall" below (W0 is a real but
cheap bridge; the survival applications hit a chart-`e`-ring instance-diamond friction).

---

> **Claim (the keystone — away-localization survival of the count).** Inverting a single element `f`
> of `A` preserves the top-dimensional minimal-prime count, given avoidance + a per-prime no-drop.
>
> - **Lean:** `DLNFibre.Core.topDimMinPrimes_ncard_away_eq`,
>   `DLNFibre.Core.bijOn_comap_topDimMinPrimes_away` (`TopDimMinPrimesLocalization.lean`).
> - **Gloss.** For `S = Localization.Away f A` (`IsLocalization.Away f S`), with `hdim :
>   ringKrullDim S = ringKrullDim A`, `havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p`, and the
>   **componentwise no-drop** `hper : ∀ p ∈ TopDimMinPrimes A, ringKrullDim (Localization.Away
>   (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)`: `comap (algebraMap A S)` is a `Set.BijOn`
>   `TopDimMinPrimes S → TopDimMinPrimes A`, count-preserving. The minimal-prime correspondence is
>   `IsLocalization.minimalPrimes_map M S ⊥` + `Ideal.map_bot`; the A-side / S-side dimension bridge
>   is the helper `ringKrullDim_quotient_map_localizationAway_eq` (`S ⧸ map φ p ≃+* Localization.Away
>   (mk p f)`, by hand from `IsLocalization.Away.map` surjective + `IsLocalization.ker_map` +
>   `Submonoid.map_powers` + `RingHom.quotientKerEquivOfSurjective`).
> - **Design (Codex-vetted).** `hper` is phrased on the **A-side** (not on `S`-side comap quotients):
>   the two call sites W1/W2 discharge it from the f.g.-domain no-drop
>   (`Core.AffineLocalizationNoDrop.ringKrullDim_localizationAway_eq_of_fg_domain`) on `A ⧸ p`, a
>   f.g. `k`-domain with `f̄ ≠ 0`. **The componentwise no-drop is a required input**, NOT inferable
>   from the ambient `hdim` + `havoid` (a domain localized at a non-unit can drop dimension — a DVR at
>   a uniformizer).
> - **Proved.** Any commutative ring `A`, any `f`.
> - **Status.** sorry-free, axiom-clean. **The keystone the brief flagged to land first.**

> **Claim (W3 — the count is radical-insensitive).** The top-dimensional minimal-prime count of a
> quotient depends only on the radical of the ideal.
>
> - **Lean:** `DLNFibre.Core.topDimMinPrimes_quotient_radical_ncard_eq`,
>   `DLNFibre.Core.topDimMinPrimes_quotient_ncard_eq_of_minimalPrimes_eq` (+ helpers
>   `quotTopDimSet`, `bijOn_comap_quotTopDimSet`, `ncard_topDimMinPrimes_quotient_eq`)
>   (`TopDimMinPrimesRadical.lean`).
> - **Gloss.** `(TopDimMinPrimes (R ⧸ J)).ncard = (TopDimMinPrimes (R ⧸ J.radical)).ncard`. Both
>   reduce to the `R`-side set `{q ∈ minimalPrimes · | ringKrullDim (R ⧸ q) = ringKrullDim (R ⧸ ·)}`
>   (`comap (Quotient.mk ·)` bijection, `ringKrullDim_doubleQuot_eq`); `minimalPrimes` is
>   radical-insensitive (`Ideal.radical_minimalPrimes`) and the quotient Krull dim is too
>   (`ringKrullDim_quotient` + `PrimeSpectrum.zeroLocus_radical`). The abstract `_of_minimalPrimes_eq`
>   version is reusable. The W3 rung: `O(F) = R ⧸ vanishingIdeal(fibre) = R ⧸ radical(fibreGenIdeal)`
>   and `O(fibre) = R ⧸ fibreGenIdeal` carry the same count.
> - **Proved.** Any commutative ring `R`, any `J`.
> - **Status.** sorry-free, axiom-clean.

> **Claim (chart-`e` count wire).** The localized chart `AlgEquiv` carries the count across.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_chartE_eq` (`TopDimMinPrimesChartE.lean`).
> - **Gloss.** `(TopDimMinPrimes (Localization.Away (chartDsig …))).ncard = (TopDimMinPrimes
>   (Localization.Away (chartGfib …))).ncard`, i.e. `O(Σ^r)[1/dsig]` and `(O(F)[SchurVar])[1/gF]`
>   agree, via `topDimMinPrimes_ncard_eq_of_ringEquiv` on `Core.ChartLocalizedAlgEquiv.
>   chartLocalizedAlgEquiv`. `[Infinite k]` (the chart `e` hypothesis).
> - **Note.** The codomain ring is a localization of a polynomial ring over a quotient — a
>   doubly-nested `CommRing` whose instance synthesis overruns the default budget; the statement pins
>   the ambient `CommRing` via `letI := inferInstance` so it elaborates.
> - **Status.** sorry-free, axiom-clean.

> **Claim (W2 avoidance certificate).** `gF` avoids every extended prime `map C q`.
>
> - **Lean:** `DLNFibre.Core.chartGfib_not_mem_map_C` (`TopDimMinPrimesGfibAvoid.lean`).
> - **Gloss.** `chartGfib ∉ Ideal.map C q` for `q` any prime of `O(F) = sweepFibreRing`. The
>   reduction `map (mk q)` kills `map C q` but sends `chartGfib = map (algebraMap k O(F)) detSchurS`
>   to the nonzero `map (algebraMap k (O(F)⧸q)) detSchurS` (`detSchurS_ne_zero` survives the
>   coefficient injection). The standalone form of the avoidance buried inside `Core.SchurSideNoDrop`.
>   After the poly descent (`Core.TopDimMinPrimesPoly`, `bijOn_comap_C_topDimMinPrimes`) every top
>   minimal prime of `O(F)[SchurVar]` is `map C q`, so this is exactly the keystone's `havoid` at W2.
> - **Status.** sorry-free, axiom-clean.

---

## The count chain — status after this tide

```
topComponents(Σ̄^r) ↔ TopDimMinPrimes(O(Σ̄^r)) = cTheta(d−r)   ✓ LANDED (thread 06, TopComponentsTopDim)
  │  [W0] closed Σ̄^r (Fin N+1) ↔ exact-rank Σ^r (chart side)   — REAL but CHEAP bridge (see below)
  ▼
TopDimMinPrimes(O(Σ^r))
  │  [W1] localization survival at dsig (detΔ)                  — keystone applies; avoidance SETTLED, survival app blocked by instance friction
  ▼
TopDimMinPrimes(O(Σ^r)[1/dsig])
  │  ── chart e (ring iso) ──                                   ✓ LANDED (TopDimMinPrimesChartE)
  ▼
TopDimMinPrimes((O(F)[SchurVar])[1/gF])
  │  [W2] localization survival at gF                           — keystone applies; avoidance LANDED, survival app blocked by instance friction
  ▼
TopDimMinPrimes(O(F)[SchurVar])
  │  ── poly descent ──                                         ✓ LANDED (thread 06, TopDimMinPrimesPoly)
  ▼
TopDimMinPrimes(O(F))
  │  [W3] O(F) (radical) ↔ O(fibre) (generator)                 ✓ LANDED (TopDimMinPrimesRadical)
  ▼
TopDimMinPrimes(O(fibre)) = TopDimMinPrimes(O(fibre)[1/detΔ])   ✓ LANDED (thread 06, FibreTopDimDetUnit)
```

---

## The remaining wall (precise — for the controller's decision)

### W0 — closed `Σ̄^r` ↔ exact-rank `Σ^r` (a REAL but CHEAP bridge; NOT the declined density theorem)

The LANDED `Σ̄^r` count endpoint is over `sigmaIdeal = vanishingIdeal(productRankLocusLE)` (rank
`≤ r`, CLOSED); the chart-`e` source ring `sweepSigmaRing` is `vanishingIdeal(productRankLocus)`
(rank `= r`, EXACT). `ClosureBridge` proves only a **dimension** equality (`varietyDim Σ^r =
varietyDim Σ̄^r`, by catenary cancellation) — NOT a `vanishingIdeal` equality or a minimal-prime
identity; the codebase explicitly DECLINED `Σ̄^r = repClosure(Σ^r)` ("unbuilt rank-raising/density
theorem"). **So W0 is a real bridge at the count level.**

Codex (decorrelated, `codex/w0-bridge-answer.md`) verdict: **cheap route exists**, strictly weaker
than the declined density theorem. The cleanest sufficient lemma:
- `vanishingIdeal(Σ^r) ≤ p` for every top component `p` of `Σ̄^r` — because each top component is
  `vanishingIdeal(Ō_{realizerD m})` for a minimising Kostant partition `m` (LANDED *unconditional*
  recovery `Core.CCodimCornerMono.exists_kostantPartition_partitionIdeal_eq_of` discharged by the
  LANDED strict mono `cCodim_zero_strict`), and the realizer's orbit lies in `Σ^r`
  (`orbitAsTuples_realizerD_subset_productRankLocus` + `vanishingIdeal_orbitRankLocus_eq_orbitSet`);
- then the top minimal primes of `vanishingIdeal(exact)` and `vanishingIdeal(LE)` coincide (lower
  strata are strictly lower-dimensional, so contribute no top component — the strict
  corner-monotonicity), via the height-coincidence `q.height = C` + strict prime-height monotonicity.

**HAZARD (Codex):** needs `productRankLocus` nonempty (the `kostantPartitions d r`.Nonempty / realizer
hypothesis rules this out); reducibility of `Σ^r` is harmless (proof is componentwise). **W0 is a
focused successor sub-tide (~1 module): the `J ≤ p` containment + the top-min-prime coincidence.**

### W1 / W2 — the survival APPLICATIONS (keystone applies; blocked by a chart-`e`-ring instance diamond)

The keystone `topDimMinPrimes_ncard_away_eq` is the exact tool. Its three inputs for W1/W2:
- **`havoid`** — W2 LANDED (`chartGfib_not_mem_map_C` + the poly-descent characterization of top
  primes as `map C q`); W1 SETTLED mathematically (`Core.SourceNoDrop.chartDsig_not_mem_partitionIdeal`
  proves `detΔ ∉ vanishingIdeal(Ō_{realizerD m})` for ANY `m ∈ kostantPartitions d r`, and the
  topComponents-as-`partitionIdeal` recovery quantifies it over all top components).
- **`hper`** — the per-prime f.g.-domain no-drop. For W2 the math is one line
  (`ringKrullDim_localizationAway_eq_of_fg_domain` on `A ⧸ map C q ≅ MvPolynomial SchurVar (O(F)⧸q)`,
  a f.g. `k`-domain, with `mk(map C q) gF ≠ 0` = the avoidance) — **BUT** elaborating `Ideal.map C q`
  / `A ⧸ map C q` over the chart-`e` ring `MvPolynomial SchurVar (MvPolynomial (RepCoord) k ⧸ I)`
  hits a `CommRing`/`HasQuotient` **instance-diamond/fuel** wall (`AddMonoidAlgebra.semiring` vs
  `Ring.toSemiring`; default `synthInstance.maxHeartbeats` exhausted). This is a Lean-engineering
  obstruction, not a mathematical one — surmountable with disciplined `letI`-pinning + a fixed
  codomain annotation throughout, but verbose and fragile; left for a focused successor pass.
- **`hdim`** — the ambient no-drop. W2 = `Core.SchurSideNoDrop.ringKrullDim_localizationAway_eq_of_
  schurSide` (needs a top-dim prime witness of `O(F)` — its existence is itself a small lemma, no
  direct Mathlib `ringKrullDim = sup over minimal primes`); W1 = `Core.SourceNoDrop.ringKrullDim_
  localizationAway_chartDsig_eq` (LANDED, the ambient `detΔ` no-drop).

---

## Assessment

The **keystone** (the reusable away-localization survival of the `TopDimMinPrimes` count) is LANDED
sorry-free + axiom-clean — the brief's first priority and the rung reused by both W1 and W2. Three
further rungs LANDED clean: the **W3 radical wire** (reusable), the **chart-`e` count wire**, and the
**W2 avoidance certificate**. The full headline `numTop(fibre d E_r) = cTheta(d−r)` is the
composition of all arrows; the two remaining pieces are the **W0 indexing bridge** (a real but cheap
successor sub-tide — the recovery + a containment + a height coincidence, NOT the declined density
theorem) and the **W1/W2 survival applications** (keystone + avoidance + per-prime no-drop all in
hand mathematically; blocked only by a chart-`e`-ring instance-diamond that needs disciplined
instance-pinning). Both are scoped precisely above for the controller's decision.
