# Statement card — thread 09 sub-task W2: chartGfib away-survival (Option A, diamond-free)

Thread 09 (count composition), expedition `theta-components`. Branch `expedition/theta-components`,
base commit `4a44bf45` (+ uncommitted: `lean/DLNFibre/Core/TopDimMinPrimesW2.lean`). The theorem
below builds green, sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Module NOT
yet wired into `DLNFibre.lean` (single-writer aggregator — controller to add the import at the end).

---

## What this sub-task is

The W2 rung of the fibre-`θ` count transport: inverting the Schur-side localizing element
`chartGfib` (`gF`) over the **nested** Schur-side ring `A = MvPolynomial SchurVar O(F)` does not
change the top-dimensional minimal-prime count. This is the Schur-side analogue of the W1
source-side `chartDsig` survival (`ncard_topDimMinPrimes_away_chartDsig_eq`), but `A` here is
`MvPolynomial` over a *quotient* `O(F) = R ⧸ I` — a doubly-nested `CommRing` on which the abstract
away-survival wrapper hangs (non-terminating `isDefEq` at the conclusion unification). The fix is the
**Option-A flat-ring transport**: move every hypothesis across the flat iso
`MvPolynomial SchurVar (R ⧸ I) ≃ₐ[R] MvPolynomial SchurVar R ⧸ map C I` to a *single* quotient `B`
of a flat polynomial ring, where the wrapper applies cleanly.

---

> **Claim (W2 — chartGfib away-survival over the nested ring).** Over an algebraically closed field
> of characteristic zero, for a dimension vector `d : Fin (N+2) → ℕ` and `r` with `r ≤ d_last`,
> `r ≤ d_0`, the end vertices distinct (`0 ≠ last`), and the corner-`r` Kostant set nonempty:
> inverting `chartGfib` over `A = MvPolynomial SchurVar O(F)` preserves the top-dimensional
> minimal-prime count.
>
> - **Lean:** `DLNFibre.Core.ncard_topDimMinPrimes_away_chartGfib_eq`
>   (`lean/DLNFibre/Core/TopDimMinPrimesW2.lean` @ `4a44bf45` + uncommitted).
> - **Signature.**
>   ```
>   theorem ncard_topDimMinPrimes_away_chartGfib_eq [IsAlgClosed k] [CharZero k]
>       (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
>       (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (h : (kostantPartitions d r).Nonempty) :
>       letI : CommRing (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
>         (sweepFibreRing k d r hp hq)) := inferInstance
>       (TopDimMinPrimes (Localization.Away (chartGfib k d r hp hq))).ncard
>         = (TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
>             (sweepFibreRing k d r hp hq))).ncard
>   ```
> - **Gloss.** `(TopDimMinPrimes (Away gF)).ncard = (TopDimMinPrimes (MvPolynomial SchurVar O(F))).ncard`,
>   where `O(F) = sweepFibreRing = R ⧸ vanishingIdeal(F)`, `R = MvPolynomial (RepCoord d) k`,
>   `SchurVar = SchurVar (d_0) (d_last) r`, `gF = chartGfib`. The number of top-dimensional
>   irreducible components is invisible to inverting the Schur-block-determinant unit `gF`.
> - **Proved.** Unconditionally given the stated hypotheses, via the Option-A flat transport. Set
>   `B = MvPolynomial SchurVar R ⧸ map C I` (`I = vanishingIdeal(F)`), `e = quotientEquivQuotientMvPolynomial I`
>   (the flat `R`-algebra iso, domain pinned to the `sweepFibreRing` form by ascription so the
>   `MvPolynomial`-CommRing instance matches the goal), `gB = e gF`. Then:
>   1. `topDimMinPrimes_ncard_eq_of_ringEquiv e.toRingEquiv` — count `A = B`;
>   2. `eAway = IsLocalization.ringEquivOfRingEquiv … e.toRingEquiv (Submonoid.map_powers e.toRingEquiv gF)`
>      transports the count across the localizations (`Away gF = Away gB`);
>   3. `hdim_B`: `ringKrullDim (Away gB) = ringKrullDim B` chains
>      `ringKrullDim_localizationAway_chartGfib_eq` (LANDED nested hdim) through the two iso transports;
>   4. `havoid_B`: `gB ∉ p` for every top prime `p` of `B`, transported from the LANDED nested
>      `chartGfib_not_mem_of_mem_topDimMinPrimes` along `comap e` (`comap_mem_topDimMinPrimes` carries
>      `p ↦ comap e p ∈ TopDimMinPrimes A`, then `Ideal.mem_comap`);
>   5. `topDimMinPrimes_ncard_away_eq_of_fgDomain (k := k) gB hdim_B havoid_B` — the wrapper on the
>      flat `B` (single quotient of a flat poly ring — applies at default budget, no diamond);
>   6. `calc` the chain `Away gF = Away gB = B = A`.
> - **Assumed.** None beyond the stated hypotheses (`[IsAlgClosed k] [CharZero k]`, `hp`, `hq`, `hN`,
>   `(kostantPartitions d r).Nonempty`).
> - **Cited.** None new. Inputs are LANDED in-repo lemmas
>   (`ringKrullDim_localizationAway_chartGfib_eq`, `chartGfib_not_mem_of_mem_topDimMinPrimes`,
>   `topDimMinPrimes_ncard_away_eq_of_fgDomain`, `topDimMinPrimes_ncard_eq_of_ringEquiv`,
>   `comap_mem_topDimMinPrimes`) and Mathlib lemmas
>   (`MvPolynomial.quotientEquivQuotientMvPolynomial`, `IsLocalization.ringEquivOfRingEquiv`,
>   `Submonoid.map_powers`, `ringKrullDim_eq_of_ringEquiv`).
> - **Deferred.** None for W2 itself. (Downstream: the controller chains W1-localization → chart `e`
>   → W2-localization → W0 to land `numTop(fibre) = cTheta(d−r)` — that composition is a separate
>   sub-task, not carried here.)
> - **Status.** sorry-free, axiom-clean. Fidelity review PENDING (reviewer to confirm the Lean
>   statement matches the W2 claim).

---

## Build / audit

- `scripts/lb DLNFibre.Core.TopDimMinPrimesW2` — green, no warnings on the file (all lines ≤100).
- `#print axioms DLNFibre.Core.ncard_topDimMinPrimes_away_chartGfib_eq` → `[propext,
  Classical.choice, Quot.sound]`.
- `scripts/sorries` — 0 sorry / 0 axiom / 0 native_decide / 0 #exit (whole library).
- 115 LoC.

## Note (instance-path fidelity — the load-bearing detail)

The `letI : CommRing (MvPolynomial SchurVar (sweepFibreRing ..)) := inferInstance` in the **statement**
is required for `Localization.Away (chartGfib)` to elaborate (the doubly-nested ring overruns the
default synthesis budget); it is copied verbatim from the LANDED `ncard_topDimMinPrimes_chartE_eq`
RHS, so the headline shape is `calc`-consumable against the chart-`e` arrow. The flat iso `e` has its
**domain type pinned** to `MvPolynomial ι (sweepFibreRing ..)` by ascription — without this,
`e.toRingEquiv`'s domain is `MvPolynomial ι (R ⧸ I)` with the `AddMonoidAlgebra` instance path, which
fails to unify against the goal's `CommRing` instance path (defeq-but-not-syntactic). The Option-A
route deliberately avoids applying the wrapper to the nested `A` directly (verified non-terminating
`isDefEq`, fuel does not fix it).
