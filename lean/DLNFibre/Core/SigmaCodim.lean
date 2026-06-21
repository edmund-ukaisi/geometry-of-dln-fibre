import DLNFibre.Core.CCodimZeroMono

/-!
# `DLNFibre.Core.SigmaCodim` — the geometric codimension of the closed rank-`≤ r` locus

**Brick A (Proved, zero-cited, general in `r`).** The geometric codimension of the *closed rank-`≤ r`
product locus* `Σ̄^r = productRankLocusLE d r` equals the combinatorial codimension `C = cCodim d r`:

* `codimRepCanonical_productRankLocusLE_eq_cCodim` (the `ℤ` form `(codim Σ̄^r).toNat = C`),
* `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (the `ℕ∞` form `codim Σ̄^r = (C.toNat : ℕ∞)`).

This is **network-free `Core` geometry** — no `DLNFibre.DLN` dependency. It is the same orbit-closure
machinery that proved the `r = 0` case (`DLN.codimRepCanonical_fibre_zero_eq_cCodim`), run at general
`r`: `sigmaIdeal d r = sInf (orbitIdeals d r)` and `minimalPrimes_sigmaIdeal_eq` (both general in `r`,
`Core.SigmaComponents`); the per-orbit Voigt codim; the realizer of a minimising Kostant partition
(`Core.ThetaComponentCount`). The per-orbit lower bound uses only the **weak**
dimension-monotonicity (`Core.CCodimZeroMono.cCodim_zero_mono`) through
`cCodim_le_codimRepCanonical_of` — it does **not** need the strict version, so Brick A is independent
of the θ-strict gap. `Σ̄^r` is `GL_d`-stable (a finite union of orbit closures), so there is no
fibre-dimension wall (that wall appears only when passing to `mult⁻¹(B)` for `B ≠ 0`, the Cited
Lemma 4.5/4.6 step carried in `DLN.RlctPayoffGeneral`).

The companion `r = 0` chain — stated about the zero-product *fibre* `mult⁻¹(0)` rather than `Σ̄^0`,
because that statement needs the `ℝ`-loss application layer — lives in `DLN.RlctPayoff`.

**Dependency rule:** `Core` never imports `DLN`; this module sits entirely in `Core`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {N : ℕ}

/-! ## Brick A — `codim Σ̄^r = cCodim d r` (Proved, general in `r`)

Mirrors the LANDED `r = 0` chain (`DLN.codimRepCanonical_fibre_zero_eq_cCodim`), but stated *about
`Σ̄^r` itself* (`productRankLocusLE d r`), not the fibre — the fibre needs the Cited bundle shift.
Every brick in the chain is general in `r`. -/

variable {k : Type u} [Field k]

/-- `codimRepCanonical Σ̄^r` is the height of the aggregate ideal `sigmaIdeal d r` of `Σ̄^r`
(definitional: `codimRepCanonical` unfolds to the height of the vanishing ideal of the flattened
locus, which is `sigmaIdeal d r`). -/
theorem codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal (d : Fin (N + 1) → ℕ) (r : ℕ) :
    codimRepCanonical (productRankLocusLE (k := k) d r) = (sigmaIdeal (k := k) d r).height :=
  rfl

/-- **Bridge (a), general `r`: `codim Σ̄^r = min codim` over its orbit closures.** The geometric
codimension of `Σ̄^r = productRankLocusLE d r` equals the infimum, over the corner-`≤ r` orbit
closures `Ō_M`, of their geometric codimensions — "codimension of a finite union is the minimum
codimension of its irreducible components". General in `r`: `sigmaIdeal d r = sInf (orbitIdeals d r)`
and `minimalPrimes_sigmaIdeal_eq` are both general in `r` (`Core.SigmaComponents`). `[IsAlgClosed k]`
(orbit-ideal primality). -/
theorem codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim
    [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ) :
    codimRepCanonical (productRankLocusLE (k := k) d r)
      = ⨅ M ∈ {M : Tuple (k := k) d | (mult d M).rank ≤ r},
          codimRepCanonical (orbitRankLocus M) := by
  rw [codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal, Ideal.height]
  apply le_antisymm
  · -- every orbit ideal contains a minimal prime of `≤` height ⟹ LHS ≤ each RHS summand
    refine le_iInf₂ (fun M hM ↦ ?_)
    have hmem : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M)) ∈ orbitIdeals (k := k) d r := ⟨M, hM, rfl⟩
    have hle : sigmaIdeal (k := k) d r
        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus M) := by
      rw [sigmaIdeal_eq_sInf_orbitIdeals]; exact sInf_le hmem
    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M)).IsPrime :=
      isPrime_vanishingIdeal_orbitRankLocus M
    obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le hle
    haveI := Ideal.minimalPrimes_isPrime hp
    calc ⨅ J ∈ (sigmaIdeal (k := k) d r).minimalPrimes,
            @Ideal.primeHeight _ _ J (Ideal.minimalPrimes_isPrime ‹_›)
        ≤ p.primeHeight := by
          refine iInf₂_le_of_le p hp ?_
          exact le_of_eq (by congr)
      _ ≤ _ := by
          rw [← Ideal.height_eq_primeHeight]
          exact (Ideal.height_mono hple).trans_eq
            (codimRepCanonical_orbitRankLocus_eq_height d M).symm
  · -- each minimal prime IS an orbit ideal ⟹ RHS ≤ LHS
    refine le_iInf₂ (fun J hJ ↦ ?_)
    haveI := Ideal.minimalPrimes_isPrime hJ
    have hJfam : J ∈ orbitIdeals (k := k) d r :=
      ((minimalPrimes_sigmaIdeal_eq (k := k) d r) ▸ hJ).1
    obtain ⟨M, hM, rfl⟩ := hJfam
    refine iInf₂_le_of_le M hM ?_
    rw [codimRepCanonical_orbitRankLocus_eq_height, Ideal.height_eq_primeHeight]

/-- **Brick A (`ℕ∞` form): `codim Σ̄^r = C`.** The geometric codimension of `Σ̄^r` as an `ℕ∞` equals
the combinatorial `C = cCodim d r`. Both inequalities come from bridge (a): the per-orbit lower bound
(`cCodim_le_codimRepCanonical_of cCodim_zero_mono` — uses only the **weak** monotonicity) and the
realizer of a minimising Kostant partition attaining the minimum. `[IsAlgClosed k] [CharZero k]`
(the Voigt-discharge scope where `C` is the geometric codimension). -/
theorem codimRepCanonical_productRankLocusLE_eq_cCodim_enat [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    codimRepCanonical (productRankLocusLE (k := k) d r) = ((cCodim d r h).toNat : ℕ∞) := by
  rw [codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim]
  apply le_antisymm
  · -- ≤ : the realizer of a minimising partition is a corner-`≤ r` orbit attaining `C`
    obtain ⟨m₀, hm₀, hval⟩ := Finset.exists_mem_eq_inf' h (fun m ↦ codimForm N (extendℤ m))
    have hcorner : (mult d (realizerD (k := k) hm₀)).rank ≤ r := (rank_mult_realizerD hm₀).le
    have hreal : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))
        = ((cCodim d r h).toNat : ℕ∞) := by
      have hfin : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀)) ≠ ⊤ := by
        rw [codimRepCanonical_orbitRankLocus_eq_height]
        exact Ideal.height_ne_top
          (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
      have hnn : 0 ≤ cCodim d r h := by
        rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
        exact fun m' _ ↦ Int.natCast_nonneg _
      have hceq : cCodim d r h = codimForm N (extendℤ m₀) := hval
      have htn : ((codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))).toNat : ℤ)
          = (cCodim d r h).toNat := by
        rw [codimRepCanonical_orbitRankLocus_realizerD hm₀, hceq]
        omega
      rw [← ENat.coe_toNat hfin]
      exact_mod_cast htn
    refine iInf₂_le_of_le (realizerD (k := k) hm₀) hcorner ?_
    rw [hreal]
  · -- ≥ : every corner-`≤ r` orbit codim is ≥ C (the per-orbit lower bound, WEAK mono only)
    exact le_iInf₂ (fun M hM ↦
      cCodim_le_codimRepCanonical_of (fun he he' hle ↦ cCodim_zero_mono he he' hle) d r h M hM)

/-- **Brick A: `codim Σ̄^r = C`.** The geometric codimension of the closed rank-`≤ r` product locus
`Σ̄^r = productRankLocusLE d r` equals the combinatorial codimension `cCodim d r = C`
(Lehalleur–Rimányi's `C`). The same orbit-closure machinery that proved the `r = 0` case, general in
`r`; the per-orbit lower bound uses only the **weak** dimension-monotonicity (`cCodim_zero_mono` — not
the strict version). `[IsAlgClosed k] [CharZero k]`. -/
theorem codimRepCanonical_productRankLocusLE_eq_cCodim [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) = cCodim d r h := by
  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
  have hnn : 0 ≤ cCodim d r h := by
    rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
    exact fun m' _ ↦ Int.natCast_nonneg _
  omega

end DLNFibre.Core
