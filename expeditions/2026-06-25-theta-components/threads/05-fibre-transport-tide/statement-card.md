# Statement card — fibre-θ Route A: entry lemma + the shifted component count

Thread 05 (fibre-transport tide). Branch `expedition/theta-components`, worktree state at
`58189a37` (+ uncommitted: `lean/DLNFibre/Core/{FibreDetUnit,CThetaShiftCount}.lean`). Build green,
sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`) on all five theorems below.

---

> **Claim (entry lemma).** The deep pivot minor `detΔ = ΔPdeep d r` is `≡ 1` on the rank-`r` fibre
> `mult⁻¹(E)`, `E = diag(I_r,0)` — so `detΔ` is a **unit** on the fibre coordinate ring.
>
> - **Lean:** `DLNFibre.Core.ΔPdeep_sub_one_mem_fibreGenIdeal`,
>   `DLNFibre.Core.isUnit_mk_ΔPdeep_fibreGenIdeal` (`lean/DLNFibre/Core/FibreDetUnit.lean` @ `58189a37`).
> - **Gloss.** `ΔPdeep d r hp hq − 1 ∈ fibreGenIdeal d (normalForm (d last) (d 0) r)`; equivalently the
>   class of `ΔPdeep` in `MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E` is `1`, hence `IsUnit`. Any
>   field `k`, any `d`, any `r ≤ d last`, `r ≤ d 0`. Proof: `det` commutes with the quotient map and each
>   generic-product entry `multPoly d a b` reduces to `C (E a b)`; the top-left `r×r` minor of
>   `E = diag(I_r,0)` is `det I_r = 1`.
> - **Proved.** The membership / unit fact, unconditionally, no `IsAlgClosed`/`CharZero`/radicality.
> - **Assumed.** `r ≤ d (last N)`, `r ≤ d 0` (well-typed pivot block). None beyond.
> - **Cited.** none.
> - **Deferred.** none (this is the complete entry lemma).
> - **Status.** sorry-free.

> **Claim (Route-A fibre-side payoff).** Inverting `detΔ` on the fibre coordinate ring is an algebra
> isomorphism — passing to the pivot chart `{detΔ ≠ 0}` is invisible on the fibre.
>
> - **Lean:** `DLNFibre.Core.fibreLocalizationAwayDetΔ_algEquiv`
>   (`lean/DLNFibre/Core/FibreDetUnit.lean` @ `58189a37`).
> - **Gloss.** With `Q := MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`, an `AlgEquiv`
>   `Q ≃ₐ[Q] Localization.Away (mk (ΔPdeep d r))`, via `IsLocalization.atUnits` (powers of a unit are
>   units). The reducedness-free statement of thread 04's kill-condition.
> - **Proved.** The localization-at-`detΔ` iso, unconditionally.
> - **Assumed.** as above.
> - **Cited.** none.
> - **Deferred.** none for this lemma; it is the fibre-side **endpoint** of the full transport (see the
>   wall card below).
> - **Status.** sorry-free.

> **Claim (combinatorial shifted count).** The rank-`r` minimiser count is the closed form of the
> shifted vector: `numTop d r = cTheta (d − r) = C(m,|δ|)`.
>
> - **Lean:** `DLNFibre.Core.numTop_eq_cTheta_dminus`
>   (`lean/DLNFibre/Core/CThetaShiftCount.lean` @ `58189a37`).
> - **Gloss.** For `Monotone d` and `r ≤ d k` everywhere, `numTop d r hr' = cTheta (dminus d r)`.
>   Field-free. Assembles the LANDED `numTop_rankShift` (LR Lemma 4.5) + `numTop_zero_eq_cTheta`
>   (LR Thm 7.10, `r = 0`) + `monotone_dminus`.
> - **Proved.** The equality, given `Monotone d` and the rank bound.
> - **Assumed.** `Monotone d` (genuine — `cTheta` reads order-sensitive prefix data); `∀ k, r ≤ d k`;
>   `kostantPartitions` nonempty on both sides.
> - **Cited.** none (LR Lemmas 4.5 / 7.10 are themselves Proved upstream in `Core`, not cited).
> - **Deferred.** none.
> - **Status.** sorry-free.

> **Claim (geometric `Σ̄^r` shifted count).** The number of top-dimensional irreducible components of
> the closed rank-`≤ r` product locus `Σ̄^r` equals `cTheta (d − r) = C(m,|δ|)`.
>
> - **Lean:** `DLNFibre.Core.ncard_topComponents_sigma_eq_cTheta_dminus`
>   (`lean/DLNFibre/Core/CThetaShiftCount.lean` @ `58189a37`). The `_sigma_` token carries the
>   `Σ̄^r`-locus (not fibre) scope in the name.
> - **Gloss.** Over `[Field k][IsAlgClosed k][CharZero k]`, for `Monotone d` and `r ≤ d k` everywhere,
>   `(topComponents d r hr').ncard = cTheta (dminus d r)`. Stacks the unconditional headline
>   `numTop_eq_ncard_topComponents` onto the combinatorial count.
> - **Proved.** The equality, under the field + monotonicity + rank hypotheses.
> - **Assumed.** `[IsAlgClosed k][CharZero k]`, `Monotone d`, `∀ k, r ≤ d k`, nonemptiness.
> - **Cited.** none.
> - **Deferred.** This counts the **`Σ̄^r`** top components, NOT the **fibre** `mult⁻¹(E)` top
>   components — that is the Route-A transport (next card).
> - **Status.** sorry-free.

---

## The remaining wall (NOT yet in Lean — precise correct statement for the successor tide)

> **Target (fibre θ-count).** The number of top-dimensional irreducible components of the fibre
> `mult⁻¹(E)` equals that of `Σ̄^r`, hence `= cTheta (d − r) = C(m,|δ|)`.
>
> - **Lean:** NOT formalised. Correct statement shape (Codex-vetted formulation, thread 05):
>   define `TopDimMinPrimes A := {p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A}`
>   (top dimension = full coheight), then
>   `#TopDimMinPrimes (O(fibre)) = #TopDimMinPrimes (O(Σ̄^r)) = cTheta (d − r)`.
> - **Why deferred.** The transport rides the existing chart `e : (O(Σ^r))[1/detΔ] ≃ₐ[k]
>   (O(F)[SchurVar])[1/detSchurS]` (`Core.ChartLocalizedAlgEquiv`, built for the *codim* result, used
>   there via `ringKrullDim` only). The fibre side of `e` carries an **extra polynomial extension** by
>   `|δ| = card SchurVar` variables **and** a localization. So transporting the component count requires,
>   in order (Codex-confirmed multi-tide, no single packaged Mathlib lemma):
>   1. ambient-ring → coordinate-ring top primes (catenary, `vanishingIdeal_image_fibre_eq_radical`);
>   2. **polynomial-extension descent** `TopDimMinPrimes (O(F)[SchurVar]) ≃ TopDimMinPrimes (O(F))`
>      (hand-built: `comap C ∘ map C = id`, `map C` of a prime is prime — generalise the LANDED
>      `SchurSideNoDrop.isPrime_map_C_of_isPrime` — both quotient dims gain `card SchurVar`);
>   3. Schur-side localization descent (all fibre top primes avoid `detSchurS`);
>   4. the chart `e` ring-equiv transport (`ringKrullDim_eq_of_ringEquiv`);
>   5. source localization descent (all `Σ̄^r` top primes avoid `detΔ` — generalise the LANDED
>      `SourceNoDrop.chartDsig_not_mem_partitionIdeal` from one realizer to all top components);
>   6. exact-rank source ↔ closed-`Σ̄^r` top-component bridge.
>   The **`detΔ`-unit fact (entry lemma above) removes the reducedness blocker** for this transport —
>   it is the load-bearing input, now LANDED — but does not by itself prove the count.
> - **Cited.** LR Lemma 4.5 / 4.6(B) for the block-triangular mechanism (the shift-width identity is its
>   combinatorial shadow, already Proved as `numTop_rankShift`); the geometric transport is to be Proved
>   zero-cite.
> - **Status.** NOT started in Lean — recommended as a dedicated successor tide (Codex: "several tides,
>   not one ≤400 LoC tide"). The cleanest isolated intermediate to land first is the
>   polynomial-extension + localization descent `topDimMinPrimes_polyAway_equiv`.
