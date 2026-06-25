# Statement card — fibre-θ closer: W1 keystone application + the composed headline

Thread 09 (fibre-θ count CLOSER tide). Branch `expedition/theta-components`, base commit `4a44bf45`
(+ uncommitted: `lean/DLNFibre/Core/{TopDimMinPrimesW1W2, FibreThetaCount}.lean`; peer-owned
`TopDimMinPrimesW0.lean`, `TopDimMinPrimesW2.lean`). All theorems below build green via `lake env lean`,
sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Modules NOT yet wired into
`DLNFibre.lean` (single-writer aggregator — controller integrates).

---

## What this tide is

The CLOSER for the fibre-θ count: build the two keystone-application rungs (W1 + the abstract wrapper;
W2 delegated to a peer) and **compose the headline** `numTop(fibre d E_r) = cTheta(d − r)` from the
seven landed chain rungs. The W0 bridge landed independently (peer); this tide consumes it.

---

> **Claim (abstract diamond-avoiding wrapper).** Away-localization preserves the top-dimensional
> minimal-prime count over a finitely-generated `k`-algebra, given the global no-drop + avoidance —
> the per-prime no-drop `hper` of the keystone discharged generically.
>
> - **Lean:** `DLNFibre.Core.topDimMinPrimes_ncard_away_eq_of_fgDomain`
>   (`TopDimMinPrimesW1W2.lean`).
> - **Gloss.** `A` a f.g. `k`-algebra (Noetherian), `f : A`, `hdim : ringKrullDim (Away f) =
>   ringKrullDim A`, `havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p` ⟹
>   `(TopDimMinPrimes (Away f)).ncard = (TopDimMinPrimes A).ncard`. Wraps the thread-08 keystone
>   `topDimMinPrimes_ncard_away_eq`, discharging its `hper` per top prime via
>   `ringKrullDim_localizationAway_eq_of_fg_domain` (`A ⧸ p` an f.g. `k`-domain, `mk p f ≠ 0` from
>   the avoidance). Reused by W1 here and by the peer's W2 (flat-ring route).
> - **Status.** sorry-free, axiom-clean.

> **Claim (W1 keystone application).** Inverting `chartDsig` (the deep pivot minor) over `O(Σ^r)`
> preserves the top-dimensional minimal-prime count.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_away_chartDsig_eq` (`TopDimMinPrimesW1W2.lean`).
> - **Gloss.** `(TopDimMinPrimes (Localization.Away (chartDsig ..))).ncard =
>   (TopDimMinPrimes (sweepSigmaRing ..)).ncard`, over `[IsAlgClosed k][CharZero k]`, `d : Fin (N+2) → ℕ`,
>   `hN`, `h : (kostantPartitions d r).Nonempty`. The base ring `sweepSigmaRing = R ⧸ vanishingIdeal(Σ^r)`
>   is a *single* quotient (flat), so the wrapper applies directly — **no instance diamond** (contrast
>   W2). `hdim` = LANDED `Core.SourceNoDrop.ringKrullDim_localizationAway_chartDsig_eq`; `havoid` =
>   `chartDsig_not_mem_of_mem_topDimMinPrimes` (every top prime of `O(Σ^r)` comaps to a `topComponents`
>   member via the peer's W0 `quotTopDimSet_sweepSigma_eq_topComponents`, recovered as a corner-`r`
>   `partitionIdeal` by the unconditional `exists_kostantPartition_partitionIdeal_eq_of` /
>   `cCodim_zero_strict`, which `chartDsig` avoids via `Core.SourceNoDrop.chartDsig_not_mem_partitionIdeal`).
> - **Status.** sorry-free, axiom-clean.

> **Claim (W2 havoid helper).** `chartGfib` avoids every top-dimensional minimal prime of
> `MvPolynomial SchurVar O(F)`.
>
> - **Lean:** `DLNFibre.Core.chartGfib_not_mem_of_mem_topDimMinPrimes` (`TopDimMinPrimesW1W2.lean`).
> - **Gloss.** A top minimal prime `P` is `Ideal.map C (comap C P)`
>   (`map_comap_C_of_mem_minimalPrimes`), `comap C P` prime, and `chartGfib ∉ map C q`
>   (`chartGfib_not_mem_map_C`). Feeds the peer's W2 application.
> - **Status.** sorry-free, axiom-clean.

> **Claim (THE COMPOSED HEADLINE, `_of` form).** The number of top-dimensional irreducible components
> of the fibre `mult⁻¹(E_r)` over the rank-`r` normal form equals `cTheta (d − r) = C(m, |δ|)`, given
> the W2 survival as one explicit hypothesis.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of` (`FibreThetaCount.lean`).
> - **Gloss.** Over `[IsAlgClosed k][CharZero k]`, `d : Fin (N+2) → ℕ`, `hN`, `Monotone d`, `∀ i, r ≤ d i`,
>   `(kostantPartitions (dminus d r) 0).Nonempty`, `(kostantPartitions d r).Nonempty`, and
>   `hW2 : (TopDimMinPrimes (Away chartGfib)).ncard = (TopDimMinPrimes (MvPolynomial SchurVar O(F))).ncard`:
>   `(TopDimMinPrimes (R ⧸ fibreGenIdeal d E_r)).ncard = cTheta (dminus d r)`, where `R = MvPolynomial
>   (RepCoord d) k`, `E_r = normalForm (d (Fin.last (N+1))) (d 0) r hp hq`. A `calc` telescoping the
>   seven rungs:
>   `cTheta(d−r) =[E0] O(Σ̄^r) =[W0] O(Σ^r) =[W1] Away dsig =[chartE] Away gF =[W2] MvPoly Schur O(F)
>   =[poly] O(F) =[W3] R ⧸ fibreGenIdeal`. The `[IsAlgClosed][CharZero]` give `Infinite k` (so chartE
>   fires) and the Nullstellensatz `vanishingIdeal(fibre) = radical(fibreGenIdeal)` for W3.
> - **Rungs consumed (all LANDED):** `ncard_topDimMinPrimes_sigma_eq_cTheta_dminus` (E0, thread 06/08),
>   `ncard_topDimMinPrimes_sigma_eq_sweepSigma` (W0, peer), `ncard_topDimMinPrimes_away_chartDsig_eq`
>   (W1, this tide), `ncard_topDimMinPrimes_chartE_eq` (chartE, thread 08),
>   `topDimMinPrimes_mvPolynomial_ncard_eq` (poly, thread 06),
>   `topDimMinPrimes_quotient_radical_ncard_eq` (W3, thread 08) + `vanishingIdeal_image_fibre_eq_radical`.
> - **Status.** sorry-free, axiom-clean. The UNCONDITIONAL headline (plugging the peer's W2 into `hW2`)
>   is a one-liner pending W2 building green.

---

## The instance-diamond finding (Lean-engineering, Codex-vetted)

The W2 base ring `A = MvPolynomial SchurVar (R ⧸ I)` (`MvPolynomial`-over-quotient) hits a
`whnf`/`isDefEq` **non-termination** (the `AddMonoidAlgebra.semiring` vs `Ring.toSemiring` diamond)
when an abstract lemma is APPLIED to it — confirmed NOT fixable by `maxHeartbeats` (does not finish at
4 000 000). Fuel defers, never closes. Resolutions found:

- **W1 (single-quotient base):** no diamond — the wrapper applies directly.
- **W2 (nested base):** Option A (Codex) — transport across the flat iso
  `MvPolynomial.quotientEquivQuotientMvPolynomial : MvPolynomial ι (R ⧸ I) ≃ₐ[R] MvPolynomial ι R ⧸ (map C I)`
  to a SINGLE-quotient flat ring `B`, apply the wrapper on `B` (confirmed clean), transport back via
  `topDimMinPrimes_ncard_eq_of_ringEquiv` + `IsLocalization.ringEquivOfRingEquiv`. The peer's
  `TopDimMinPrimesW2.lean` implements this; two residual wrinkles flagged to controller (the `eAway`
  `Submonoid.map_powers` needs `.toMonoidHom`; a `whnf` at the theorem boundary).
- **Statement-level:** `letI : CommRing (MvPolynomial ι (sweepFibreRing)) := inferInstance` in the
  *statement* is needed for `Localization.Away (chartGfib)` to elaborate; a *body* `letI` of the same
  poisons the canonical-instance match and must be avoided.

Codex artefacts: `codex/composition-{prompt,answer}.md`, `codex/diamond-{prompt,answer}.md`.
