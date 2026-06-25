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
> - **Status.** sorry-free, axiom-clean.

> **Claim (THE COMPOSED HEADLINE, UNCONDITIONAL).** Same conclusion as the `_of` form, with the W2
> rung discharged from the LANDED flat-route keystone — no open hypothesis.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` (`FibreThetaCount.lean`,
>   `section UnivZero`).
> - **Gloss.** `(TopDimMinPrimes (R ⧸ fibreGenIdeal d E_r)).ncard = cTheta (dminus d r)` over
>   `[IsAlgClosed k][CharZero k]` + `Monotone d` + `∀ i, r ≤ d i` + the two Kostant nonemptinesses +
>   `hN`. The W2 rung is `Core.TopDimMinPrimesW2.ncard_topDimMinPrimes_away_chartGfib_eq`.
> - **Stated at `k : Type` (universe 0).** The peer's W2 theorem is monomorphic at `Type` (not
>   `Type u`); the universe-polymorphic rungs E0/W0/W1/chartE/poly/W3 specialise to `u = 0` freely, and
>   `Type 0` carries the operative fields (`AlgebraicClosure ℚ`, `ℂ`). (Re-generalising W2 to `Type u`
>   would lift this to `Type u`; W2 is peer-owned.)
> - **Discharge is NOT via the `_of` form** — applying `_of` forces an `isDefEq`-across-the-diamond at
>   its `hW2` binder type (the `MvPolynomial`-over-quotient `AddMonoidAlgebra.semiring` vs
>   `Ring.toSemiring` diamond, which leaves a `Field sorry` metavariable). Instead the theorem **inlines
>   the 7-rung calc** under a body `letI : CommRing (MvPolynomial SchurVar (sweepFibreRing)) :=
>   inferInstance`, obtaining W2 as `have hW2 := ncard_topDimMinPrimes_away_chartGfib_eq (k := k) …`
>   (under the `letI` the instance path matches the chain — no diamond).
> - **Status.** sorry-free, **axiom-clean** `[propext, Classical.choice, Quot.sound]` (verified
>   `#print axioms` — NO `sorryAx`).

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
