/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.TopDimMinPrimesLocalization
import DLNFibre.Core.TopDimMinPrimesPoly
import DLNFibre.Core.TopDimMinPrimesGfibAvoid
import DLNFibre.Core.SchurSideNoDrop
import DLNFibre.Core.FibreCodimFinal
import DLNFibre.Core.Dimension.Localization
import DLNFibre.Core.SourceNoDrop
import DLNFibre.Core.TopDimMinPrimesW0
import DLNFibre.Core.TopDimMinPrimesRadical

/-!
# `DLNFibre.Core.TopDimMinPrimesW1W2` — the keystone localization-survival applications (W1 + W2 inputs)

The W1 rung of the fibre-`θ` count transport (expedition `theta-components`, thread 09): inverting
the source localizing element `chartDsig` over `O(Σ^r) = sweepSigmaRing` preserves the top-dimensional
minimal-prime count. The base ring is a *single* quotient (flat), so the diamond-avoiding wrapper
`topDimMinPrimes_ncard_away_eq_of_fgDomain` applies directly.

Also provides:
* the **abstract wrapper** `topDimMinPrimes_ncard_away_eq_of_fgDomain` — away-survival of the count
  over a finite-type `k`-algebra (the per-prime no-drop `hper` of the keystone discharged generically),
  reused by W1 here and by W2 (`Core.TopDimMinPrimesW2`, the flat-ring route);
* the **W2 `havoid`** `chartGfib_not_mem_of_mem_topDimMinPrimes` — every top minimal prime `P` of
  `MvPolynomial SchurVar O(F)` is `Ideal.map C (comap C P)` and `chartGfib` avoids every `map C q`.

The W2 keystone application itself lives in `Core.TopDimMinPrimesW2` (it routes through a flat
presentation to dodge the `MvPolynomial`-over-quotient instance diamond).

* **W1 `hdim`** — `ringKrullDim (Away dsig) = ringKrullDim O(Σ^r)` is the LANDED
  `Core.SourceNoDrop.ringKrullDim_localizationAway_chartDsig_eq`;
* **W1 `havoid`** — every top minimal prime of `O(Σ^r)` comaps to a `topComponents` member
  (`Core.TopDimMinPrimesW0`), recovered as a corner-`r` `partitionIdeal`, which `chartDsig` avoids
  (`Core.SourceNoDrop.chartDsig_not_mem_partitionIdeal`).

> **`ncard_topDimMinPrimes_away_chartDsig_eq`** — `(TopDimMinPrimes (Away chartDsig)).ncard =
> (TopDimMinPrimes (O(Σ^r))).ncard`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix Dimension

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Abstract wrapper — away-survival over a finite-type `k`-algebra with a global no-drop

The reusable away-survival keystone `topDimMinPrimes_ncard_away_eq` needs a *per-prime* no-drop
`hper`. Over a finitely-generated `k`-algebra `A`, that `hper` is automatic: every top prime quotient
`A ⧸ p` is an f.g. `k`-domain, and `f̄ ≠ 0` (the avoidance) makes the away-localization
dimension-preserving (`ringKrullDim_localizationAway_eq_of_fg_domain`). Packaging this here keeps the
diamond-heavy `whnf` work inside one abstract proof — the two call sites W1/W2 then `apply` the
wrapper, unifying only the base ring `A` (no nested-ring `whnf` blowup at the application). -/

/-- **Away-survival of the count over a finite-type `k`-algebra.** For `A` a finitely-generated
`k`-algebra (Noetherian), `f : A` avoiding every top-dimensional minimal prime, with the **global**
no-drop `ringKrullDim (Localization.Away f) = ringKrullDim A`: inverting `f` preserves the
top-dimensional minimal-prime count. The per-prime `hper` of the underlying keystone is discharged
generically from `ringKrullDim_localizationAway_eq_of_fg_domain` (`A ⧸ p` an f.g. `k`-domain,
`mk p f ≠ 0`). The diamond-avoiding wrapper the W1/W2 chart-ring applications consume. -/
theorem topDimMinPrimes_ncard_away_eq_of_fgDomain {A : Type u} [CommRing A] [IsNoetherianRing A]
    [Algebra k A] [Algebra.FiniteType k A] (f : A)
    (hdim : ringKrullDim (Localization.Away f) = ringKrullDim A)
    (havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p) :
    (TopDimMinPrimes (Localization.Away f)).ncard = (TopDimMinPrimes A).ncard := by
  refine topDimMinPrimes_ncard_away_eq f (Localization.Away f) hdim havoid (fun p hp ↦ ?_)
  haveI : p.IsPrime := isPrime_of_mem_topDimMinPrimes hp
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  haveI : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p) (Ideal.Quotient.mkₐ_surjective k p)
  have hgne : Ideal.Quotient.mk p f ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact havoid p hp
  exact ringKrullDim_localizationAway_eq_of_fg_domain (k := k) (A ⧸ p) (Ideal.Quotient.mk p f) hgne

/-! ## W1 — `chartDsig` survival over `A = O(Σ^r) = sweepSigmaRing`

The base ring `sweepSigmaRing = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(Σ^r)` is a *single*
quotient (flat), so the keystone wrapper applies directly — no instance diamond. The only substantive
input is the `havoid`: every top-dimensional minimal prime of `O(Σ^r)` avoids `chartDsig`. -/

/-- **W1 `havoid`: `chartDsig` avoids every top-dimensional minimal prime of `O(Σ^r)`.** A top prime
`p` of `sweepSigmaRing = R ⧸ Ieq` (`Ieq = vanishingIdeal(Σ^r)`) comaps to `q ∈ quotTopDimSet Ieq =
topComponents` (`bijOn_comap_quotTopDimSet` + the W0 `quotTopDimSet_sweepSigma_eq_topComponents`); the
unconditional recovery (`exists_kostantPartition_partitionIdeal_eq_of` discharged by
`cCodim_zero_strict`) writes `q = partitionIdeal m` for a corner-`r` Kostant partition `m`, and
`chartDsig_not_mem_partitionIdeal` gives `ΔPdeep ∉ q`. Since `chartDsig = mk Ieq ΔPdeep`,
`chartDsig ∈ p ↔ ΔPdeep ∈ q`, so `chartDsig ∉ p`. -/
theorem chartDsig_not_mem_of_mem_topDimMinPrimes [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (h : (kostantPartitions d r).Nonempty)
    {p : Ideal (sweepSigmaRing k d r)} (hp' : p ∈ TopDimMinPrimes (sweepSigmaRing k d r)) :
    chartDsig k d r hp hq ∉ p := by
  set Ieq : Ideal (MvPolynomial (RepCoord d) k) := vanishingIdeal k (sweepSigma k d r) with hIeq
  -- `comap (mk Ieq) p ∈ quotTopDimSet Ieq = topComponents`.
  have hqmem : p.comap (Ideal.Quotient.mk Ieq) ∈ quotTopDimSet Ieq :=
    (bijOn_comap_quotTopDimSet Ieq).1 hp'
  have hqtop : p.comap (Ideal.Quotient.mk Ieq) ∈ topComponents (k := k) d r h := by
    rw [← quotTopDimSet_sweepSigma_eq_topComponents d r h]; exact hqmem
  -- recovery: `comap (mk Ieq) p = partitionIdeal m` for a corner-`r` Kostant partition `m`.
  obtain ⟨m, hmem, hmeq⟩ := exists_kostantPartition_partitionIdeal_eq_of
    (fun he he' hlt ↦ cCodim_zero_strict he he' hlt) d r h (p.comap (Ideal.Quotient.mk Ieq)) hqtop
  -- `ΔPdeep ∉ comap (mk Ieq) p` (Fact B, transported through the recovery).
  have hΔ : ΔPdeep (k := k) d r hp hq ∉ p.comap (Ideal.Quotient.mk Ieq) := by
    rw [← hmeq, partitionIdeal_of_mem hmem]
    exact chartDsig_not_mem_partitionIdeal d r hp hq hN hmem
  -- `chartDsig = mk Ieq ΔPdeep ∈ p ↔ ΔPdeep ∈ comap (mk Ieq) p`.
  intro hmem'
  exact hΔ (Ideal.mem_comap.mpr hmem')

/-- **W1 keystone application.** Inverting `chartDsig` over `O(Σ^r) = sweepSigmaRing` preserves the
top-dimensional minimal-prime count:

> `(TopDimMinPrimes (Away chartDsig)).ncard = (TopDimMinPrimes (O(Σ^r))).ncard`.

The base ring is a single quotient (flat), so the wrapper `topDimMinPrimes_ncard_away_eq_of_fgDomain`
applies directly with `hdim` = `ringKrullDim_localizationAway_chartDsig_eq` (LANDED) and `havoid` =
`chartDsig_not_mem_of_mem_topDimMinPrimes`. -/
theorem ncard_topDimMinPrimes_away_chartDsig_eq [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (h : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (Localization.Away (chartDsig k d r hp hq))).ncard
      = (TopDimMinPrimes (sweepSigmaRing k d r)).ncard :=
  topDimMinPrimes_ncard_away_eq_of_fgDomain (k := k) (chartDsig k d r hp hq)
    (ringKrullDim_localizationAway_chartDsig_eq d r hp hq hN h)
    (fun _ hp' ↦ chartDsig_not_mem_of_mem_topDimMinPrimes d r hp hq hN h hp')

/-! ## W2 — `chartGfib` survival over `A = MvPolynomial SchurVar O(F)` -/

/-- **W2 `havoid`: `chartGfib` avoids every top-dimensional minimal prime of `MvPolynomial SchurVar
O(F)`.** A top minimal prime `P` is `Ideal.map C (comap C P)` (`map_comap_C_of_mem_minimalPrimes`),
with `comap C P` prime, so `chartGfib_not_mem_map_C` applies. -/
theorem chartGfib_not_mem_of_mem_topDimMinPrimes (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    {P : Ideal (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq))}
    (hP : P ∈ TopDimMinPrimes (MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq))) :
    chartGfib k d r hp hq ∉ P := by
  set A := sweepFibreRing k d r hp hq
  -- `comap C P` is a (minimal) prime of `O(F)`; `P = map C (comap C P)`.
  have hPmin := hP.1
  haveI : P.IsPrime := isPrime_of_mem_topDimMinPrimes hP
  haveI : (P.comap (C : A →+* _)).IsPrime := (comap_C_mem_minimalPrimes P hPmin).1.1
  have hPeq : Ideal.map (C : A →+* _) (P.comap (C : A →+* _)) = P :=
    map_comap_C_of_mem_minimalPrimes P hPmin
  rw [← hPeq]
  exact chartGfib_not_mem_map_C d r hp hq (P.comap (C : A →+* _))

end DLNFibre.Core
