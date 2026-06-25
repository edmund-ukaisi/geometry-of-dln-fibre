# Statement card — fibre-θ count transport: `TopDimMinPrimes` framework + the `Σ̄^r` / fibre endpoints

Thread 06 (fibre-count transport tide). Branch `expedition/theta-components`, base commit
`9f25dd10` (+ uncommitted: `lean/DLNFibre/Core/{TopDimMinPrimes, TopDimMinPrimesPoly,
TopDimMinPrimesBridge, TopComponentsTopDim, FibreTopDimDetUnit}.lean`). All theorems below build
green, sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Modules NOT yet wired
into `DLNFibre.lean` (single-writer aggregator — controller to add the five imports at the end).

---

## What this tide is

The recalibration (thread 05) pinned the remaining wall as a **component-count transport** through
the chart `e`, whose hardest isolated piece is the polynomial-extension minimal-prime descent. This
tide builds the **reusable `TopDimMinPrimes` framework** for that transport and lands the two
**endpoints** of the count chain (the `Σ̄^r` coordinate-ring side `= cTheta (d−r)`, and the fibre
side's `detΔ`-unit localization), plus the **genuine math wall** (the polynomial descent). The
middle rungs (the two *non-unit* localization survivals + their avoidance certificates, and the
chart-`e` ring-equiv wire) are NOT yet built — precise statements in "The remaining wall" below.

---

> **Claim (the top-dimensional-component notion).** `TopDimMinPrimes A := {p ∈ minimalPrimes A |
> ringKrullDim (A ⧸ p) = ringKrullDim A}` — the minimal primes whose quotient carries the full
> Krull dimension (top-dimensional components, dimension reading).
>
> - **Lean:** `DLNFibre.Core.TopDimMinPrimes` (`TopDimMinPrimes.lean`).
> - **Gloss.** Any commutative ring `A`. The dimension-based reading of "top-dimensional
>   irreducible component" — the transport-clean notion (Codex-vetted choice over the height-based
>   one, which sees only the quotient's own minimal primes).
> - **Proved.** Definition + `isPrime_of_mem_topDimMinPrimes`, `mem_topDimMinPrimes`.
> - **Status.** sorry-free.

> **Claim (ring-isomorphism invariance).** A ring iso `e : A ≃+* B` carries `TopDimMinPrimes`
> bijectively by `comap`; the count is preserved.
>
> - **Lean:** `DLNFibre.Core.bijOn_comap_topDimMinPrimes`,
>   `DLNFibre.Core.topDimMinPrimes_ncard_eq_of_ringEquiv` (`TopDimMinPrimes.lean`).
> - **Gloss.** `(TopDimMinPrimes A).ncard = (TopDimMinPrimes B).ncard` for `e : A ≃+* B`. Both
>   `minimalPrimes` membership (`comap_minimalPrimes_eq_of_surjective`) and the `ringKrullDim`
>   quotient equality (`Ideal.quotientEquiv` + `ringKrullDim_eq_of_ringEquiv`) transport.
> - **Proved.** Unconditionally, any commutative rings.
> - **Status.** sorry-free.

> **Claim (the polynomial-extension descent — THE MATH WALL, now LANDED).** The count is invariant
> under a finite-variable polynomial extension: `(TopDimMinPrimes (MvPolynomial ι A)).ncard =
> (TopDimMinPrimes A).ncard`.
>
> - **Lean:** `DLNFibre.Core.topDimMinPrimes_mvPolynomial_ncard_eq`,
>   `DLNFibre.Core.bijOn_comap_C_topDimMinPrimes` (`TopDimMinPrimesPoly.lean`).
> - **Gloss.** `A` Noetherian, `ι` finite. `Ideal.comap C` is a bijection `TopDimMinPrimes
>   (MvPolynomial ι A) ≃ TopDimMinPrimes A`, inverse `Ideal.map C`. The minimal-prime
>   correspondence is hand-built (no packaged Mathlib lemma): `comap C (map C q) = q`
>   (`comap_map_C_eq`); `map C q` prime (`Core.SchurSideNoDrop.isPrime_map_C_of_isPrime`); both
>   directions of minimality through the `map C ⊣ comap C` adjunction
>   (`map_C_mem_minimalPrimes`, `comap_C_mem_minimalPrimes`, `map_comap_C_of_mem_minimalPrimes`).
>   Top-dimensionality: `ringKrullDim (B ⧸ map C q) = ringKrullDim (A ⧸ q) + card ι`
>   (`quotientEquivQuotientMvPolynomial` + `MvPolynomial.ringKrullDim_of_isNoetherianRing`), and the
>   `card ι` shift cancels on both sides (`ENat.WithBot.add_natCast_cancel`).
> - **Proved.** Unconditionally, `A` Noetherian, `ι` finite.
> - **Cited.** none.
> - **Status.** sorry-free. This is the cleanest isolated reusable rung the brief flagged to land
>   first; it strips the `|δ| = card SchurVar`-variable Schur extension off the count.

> **Claim (height ↔ dimension bridge).** On a polynomial ring `R = MvPolynomial σ k` (`σ` finite),
> for a minimal prime `p` of a proper ideal `I`: `ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ I) ↔
> p.height = I.height`.
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_quotient_eq_iff_height_eq` (+ helpers
>   `ringKrullDim_quotient_prime_eq`, `ringKrullDim_quotient_eq_of_ne_top`, `height_prime_le_card`,
>   `height_prime_ne_top`) (`TopDimMinPrimesBridge.lean`).
> - **Gloss.** Both quotient dims are `card − height ·` (per-prime + reducible-locus catenary,
>   `Core.NullstellensatzCodim` / `Core.RadicalCatenary`); subtraction from the finite `card` is
>   injective on the finite heights. Connects the height-based `topComponents` to `TopDimMinPrimes`.
> - **Proved.** Any field `k`, finite `σ`, proper `I`. Pure commutative algebra.
> - **Status.** sorry-free.

> **Claim (`Σ̄^r` count endpoint).** Over `[IsAlgClosed k][CharZero k]`, the `TopDimMinPrimes`
> count of the `Σ̄^r` coordinate ring is `cTheta (d − r)`.
>
> - **Lean:** `DLNFibre.Core.ncard_topComponents_eq_ncard_topDimMinPrimes_sigma`,
>   `DLNFibre.Core.ncard_topDimMinPrimes_sigma_eq_cTheta_dminus` (+ helpers
>   `ringKrullDim_doubleQuot_eq`, `height_sigmaIdeal_eq_cCodim`) (`TopComponentsTopDim.lean`).
> - **Gloss.** `(TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)).ncard = cTheta
>   (dminus d r)` for `Monotone d`, `r ≤ d k`, both Kostant sets nonempty. The quotient
>   minimal-prime bijection `comap (Quotient.mk)` carries `TopDimMinPrimes (O(Σ̄^r))` onto the
>   LANDED `topComponents d r h` (using `(sigmaIdeal).height = (cCodim).toNat` + the height↔dim
>   bridge + the third isomorphism theorem at `ringKrullDim`), then
>   `ncard_topComponents_sigma_eq_cTheta_dminus` (thread 05). The entry point of the chart count
>   transport on the source side.
> - **Proved.** Under field + monotonicity + rank + nonemptiness hypotheses.
> - **Status.** sorry-free.

> **Claim (fibre count endpoint — `detΔ` unit).** Inverting `detΔ` preserves the fibre's
> `TopDimMinPrimes` count: `(TopDimMinPrimes (O(fibre))).ncard = (TopDimMinPrimes
> (O(fibre)[1/detΔ])).ncard`.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_fibre_eq_localization`
>   (`FibreTopDimDetUnit.lean`).
> - **Gloss.** `detΔ` is a unit on `O(fibre) = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`
>   (`Core.FibreDetUnit.fibreLocalizationAwayDetΔ_algEquiv`), so the localization is a ring iso, and
>   `topDimMinPrimes_ncard_eq_of_ringEquiv` carries the count. The reducedness-free Route-A
>   kill-condition (thread 04) at the count level. Any `d`, `r ≤ d last`, `r ≤ d 0`, any field.
> - **Proved.** Unconditionally (no reducedness).
> - **Status.** sorry-free.

---

## The remaining wall (NOT yet in Lean — precise statements for the successor tide)

The count chain, with each arrow's status:

```
topComponents(Σ̄^r) ↔ TopDimMinPrimes(O(Σ̄^r)) = cTheta(d−r)   ✓ LANDED (TopComponentsTopDim)
  │  [W0] exact-rank Σ^r (Fin N+2, chart side) ↔ closed Σ̄^r (Fin N+1) — NOT a TopDimMinPrimes wire yet
  ▼
TopDimMinPrimes(O(Σ^r))
  │  [W1] localization survival at dsig (detΔ) — NON-unit on O(Σ^r); needs all-top avoidance + no-drop
  ▼
TopDimMinPrimes(O(Σ^r)[1/dsig])
  │  ── chart e (ring iso) ──   ✓ available via topDimMinPrimes_ncard_eq_of_ringEquiv (NOT yet wired)
  ▼
TopDimMinPrimes((O(F)[SchurVar])[1/gF])
  │  [W2] localization survival at gF — NON-unit; avoidance EASY after the poly descent
  ▼
TopDimMinPrimes(O(F)[SchurVar])
  │  ── poly descent ──   ✓ LANDED (TopDimMinPrimesPoly)
  ▼
TopDimMinPrimes(O(F))
  │  [W3] O(F) (= P/vanishingIdeal(fibre), radical) ↔ O(fibre) (= P/fibreGenIdeal) — same minimal
  │       primes (Ideal.height_radical / radical_minimalPrimes); a dim-level wire
  ▼
TopDimMinPrimes(O(fibre)) = TopDimMinPrimes(O(fibre)[1/detΔ])   ✓ LANDED (FibreTopDimDetUnit, unit case)
```

### W1 / W2 — localization survival of `TopDimMinPrimes` (the genuine remaining work)

> **Target.** For `S = Localization M A` (`M = Submonoid.powers f`), with (i) every top-dim minimal
> prime of `A` avoiding `M` (`havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p`) and (ii) the ambient no-drop
> (`ringKrullDim S = ringKrullDim A`): `comap (algebraMap A S)` is a bijection `TopDimMinPrimes S ≃
> TopDimMinPrimes A`, hence `(TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard`.
>
> - **Status.** NOT built. The minimal-prime correspondence is **one line**
>   (`IsLocalization.minimalPrimes_map M S ⊥` + `Ideal.map_bot`: `minimalPrimes S = comap ⁻¹'
>   minimalPrimes A`). The remaining pieces:
>   - **per-prime quotient dimension** `ringKrullDim (S ⧸ P) = ringKrullDim (A ⧸ comap P)` for a
>     surviving prime `P` (the quotient `S ⧸ P` is a localization of the domain `A ⧸ comap P` at the
>     image of `M`, dimension-preserving by the affine-domain no-drop
>     `Core.AffineLocalizationNoDrop.ringKrullDim_localizationAway_eq_of_fg_domain`) — a per-prime
>     analogue of the LANDED ambient `ringKrullDim_localizationAway_eq_of_avoids_top_prime`; ~1
>     module of wiring. **NOTE (reviewer + Codex, decorrelated):** this per-prime / *componentwise*
>     no-drop `dim ((A ⧸ comap P)_f) = dim (A ⧸ comap P)` does NOT fold out of the ambient no-drop +
>     avoidance — a domain localized at a non-unit can drop dimension (DVR at a uniformizer). Treat
>     it as a *required lemma* of the successor tide (it holds here because `A ⧸ comap P` is a f.g.
>     `k`-domain and `f̄ ≠ 0`, so the affine-domain no-drop applies — but it must be invoked
>     per-prime, not inferred from the global no-drop).
>   - **the avoidance certificate `havoid`** is the genuine math input:
>     - **`gF` (W2): EASY** — after the poly descent every minimal prime of `O(F)[SchurVar]` is
>       `map C q`, and `gF = map (algebraMap k O(F)) detSchurS` avoids it (`detSchurS ≠ 0` survives
>       to the domain `MvPolynomial SchurVar (O(F) ⧸ q)`); this is exactly the LANDED
>       `Core.SchurSideNoDrop` argument, lifted from the one witness to all top primes.
>     - **`dsig` (W1): the HARD certificate** — needs **source recovery of every top-dimensional
>       component of `Σ̄^r`** avoiding `detΔ`. The LANDED `Core.SourceNoDrop` proves this for ONE
>       realizer; generalising to *all* top components is a pen-and-paper-level input (Codex
>       concurred; thread 05 recalibration flagged it). **Commission a pen-and-paper cert** if it
>       blocks the successor tide — assert: every top-dimensional minimal prime of `sigmaIdeal d r`
>       has `detΔ ∉ p` (equivalently the realizer of a minimising Kostant partition has a nonzero
>       deep `r×r` pivot minor).

### W0 — exact-rank `Σ^r` ↔ closed `Σ̄^r` indexing bridge

The chart `e` is stated for **rank-exactly-`r`** `Σ^r` over `Fin (N+2)` (`sweepSigma`,
`vanishingIdeal (productRankLocus)`); the LANDED `Σ̄^r` count endpoint is the **closed** rank-`≤ r`
`Σ̄^r` over `Fin (N+1)` (`sigmaIdeal = vanishingIdeal (productRankLocusLE)`). Whether the
top-dimensional minimal primes of the two coincide (they should — the closure adds only lower-codim
components, and inverting `detΔ` removes the exact-vs-closed difference on the chart) needs a
`TopDimMinPrimes`-level bridge. **Check `Core.RouteCAssembly` / `Core.ClosureBridge`**: the codim
assembly proved a *dimension* equality between the two; whether it identifies the top-dimensional
*minimal primes* is the thing to verify (Codex: it does not automatically).

### W3 — `O(F)` (radical) ↔ `O(fibre)` (generator) minimal-prime identity

`O(F) = P / vanishingIdeal(fibre)` (radical) and `O(fibre) = P / fibreGenIdeal` differ by radical;
`Ideal.radical_minimalPrimes` / `Core.FibreHeightDirect.Ideal.height_radical` give the same minimal
primes and (via the dim reading) the same `TopDimMinPrimes`. A short dim-level wire, NOT a wall.

---

## Assessment

The two **isolated reusable** pieces the brief prioritised are LANDED sorry-free + axiom-clean: the
`TopDimMinPrimes` framework (definition + ring-iso invariance) and the **polynomial-extension
descent** (the math wall). The two **count endpoints** (`Σ̄^r` side `= cTheta(d−r)`, fibre side's
`detΔ`-unit localization) are LANDED. The remaining wall is the **non-unit localization survival**
(W1/W2 — wiring + the `dsig` all-top avoidance certificate, the latter a genuine pen-and-paper
input), the **chart-`e` ring-equiv wire** (mechanical, the iso is available), the **W0 indexing
bridge**, and the **W3 radical wire**. The full `numTop(fibre d E_r) = cTheta(d−r)` headline is the
composition of all arrows — a successor tide once the `dsig` avoidance certificate is in hand.
