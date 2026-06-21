import DLNFibre.DLN.RlctPayoff
import DLNFibre.Core.CCodimZeroMono

/-!
# `DLNFibre.DLN.RlctPayoffGeneral` — the general-rank-`r` RLCT payoff

Extends the LANDED corner-`0` payoff (`DLNFibre.DLN.RlctPayoff`) to a **rank-`r` target `B`**: the
real log-canonical threshold of the DLN square-Frobenius loss `K^DLN_B` (for `B` of rank `r`) is
`(C + r(d_0+d_N−r))/2`, where `C = cCodim d r` is the combinatorial codimension and the
`+ r(d_0+d_N−r)` is the bundle shift of Lehalleur–Rimányi Lemma 4.6.

The result splits into two bricks of **different status** (expedition thread 11 sizing):

* **Brick A (Proved, zero-cited, general in `r`).** `codimRepCanonical Σ̄^r = cCodim d r`
  (`codimRepCanonical_productRankLocusLE_eq_cCodim`): the geometric codimension of the *closed
  rank-`≤ r` product locus* `Σ̄^r = productRankLocusLE d r` equals the combinatorial `C`. The same
  orbit-closure machinery that proved the `r = 0` case (`sigmaIdeal d r = sInf orbitIdeals`, general
  in `r`; the per-orbit Voigt codim; the realizer of a minimising Kostant partition), run at general
  `r`. The per-orbit lower bound uses only the **weak** dimension-monotonicity
  (`Core.CCodimZeroMono.cCodim_zero_mono`, LANDED) through `cCodim_le_codimRepCanonical_of` — it does
  **not** need the open strict version `hMonoStrict`, so Brick A is independent of the θ-strict gap.
  `Σ̄^r` is `GL_d`-stable (a finite union of orbit closures), so there is no fibre-dimension wall.

* **Brick B (Cited, named — LR Lemma 4.6).** The passage `Σ̄^r ⤳ mult⁻¹(B)` (for `B ≠ 0`) is the
  bundle shift `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)`. This is NOT zero-cited-provable at
  Mathlib v4.29: `mult⁻¹(B)` (`B ≠ 0`) is not `GL_d`-stable, not an orbit closure, and the shift is a
  locally-trivial-bundle / fibre-dimension count Mathlib lacks (thread 11, four routes, all hit the
  same wall). We carry it as a **Cited interface** `BundleShiftInterface` — a structure FIELD
  `cited_bundle_shift_lemma46` (a hypothesis, NOT a global `axiom`), separate from `RlctInterface` so
  both Cited dependencies (Aoyagi rlct + Lemma 4.6 shift) are independently visible in any consumer.

**R2-general** (`rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`) is pure transport: the (already
general-in-`r`) Cited Aoyagi equality gives `rlct = ½·codim mult⁻¹(B)`; Brick B rewrites the fibre
codim as `codim Σ̄^r + shift`; Brick A rewrites `codim Σ̄^r = cCodim d r`. Both interfaces `I`, `J`
are explicit in the type; `via_aoyagi` names the rlct source. This is **not** an unconditional
`rlct = (C + shift)/2`.

**Dependency rule:** `DLN` depends on `Core`; `Core` never imports `DLN`.
-/

namespace DLNFibre.DLN

open Matrix DLNFibre.Core

universe u v

variable {N : ℕ}

/-! ## Brick A — `codim Σ̄^r = cCodim d r` (Proved, general in `r`)

Mirrors the LANDED `r = 0` chain (`codimRepCanonical_fibre_zero_eq_cCodim`), but stated *about `Σ̄^r`
itself* (`productRankLocusLE d r`), not the fibre — the fibre needs Brick B. Every brick in the chain
is general in `r`. -/

section BrickA

open MvPolynomial Ideal

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
(`cCodim_le_codimRepCanonical_of cCodim_zero_mono` — uses only the **weak** monotonicity, LANDED) and
the realizer of a minimising Kostant partition attaining the minimum. `[IsAlgClosed k] [CharZero k]`
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
`r`; the per-orbit lower bound uses only the **weak** dimension-monotonicity (`cCodim_zero_mono`,
LANDED — not the open strict version). `[IsAlgClosed k] [CharZero k]`. -/
theorem codimRepCanonical_productRankLocusLE_eq_cCodim [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) = cCodim d r h := by
  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
  have hnn : 0 ≤ cCodim d r h := by
    rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
    exact fun m' _ ↦ Int.natCast_nonneg _
  omega

end BrickA

/-! ## Brick B — the bundle shift (Cited, named: LR Lemma 4.6)

The passage `Σ̄^r ⤳ mult⁻¹(B)` is a locally-trivial-bundle dimension count Mathlib v4.29 lacks
(thread 11). We carry it as a Cited interface, separate from `RlctInterface`. -/

section BrickB

open MvPolynomial

/-- **The Cited bundle-shift interface (Lehalleur–Rimányi Lemma 4.6 = `lem:rank_vs_fibers`,
main.tex:844–858).** An ASSUMED geometric interface, not proved here: for `B` of rank `r ≤ min d`,
`mult⁻¹(B)` is a locally-trivial bundle over the rank-`r` matrix orbit `Mat^{rk=r}` (of dimension
`r(d_0+d_N−r)`), so its geometric codimension is that of `Σ̄^r` shifted by the base dimension. The
field `cited_bundle_shift_lemma46` is a carried hypothesis (NOT a global `axiom`); it hits the
fibre-dimension wall of Mathlib v4.29 (thread 11) and is named for the citation, not proved. Separate
from `RlctInterface` so the two Cited dependencies (Aoyagi rlct + Lemma 4.6 shift) are independently
visible in any consumer's type. -/
structure BundleShiftInterface (d : Fin (N + 1) → ℕ)
    (K : Type v) [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K) where
  /-- **Cited (LR Lemma 4.6):** the geometric codimension of the multiplication fibre `mult⁻¹(B)`
  (base-changed to `K`) equals that of the rank-`≤ r` product locus `Σ̄^r` plus the base dimension
  `r(d_0+d_N−r)`. Assumed geometric content (a fibre-dimension count absent from Mathlib v4.29), not a
  proved fact. -/
  cited_bundle_shift_lemma46 : ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ),
    B.rank = r → (∀ k', r ≤ d k') →
    codimRepCanonical (fibre (k := K) d (B.map ι))
      = codimRepCanonical (productRankLocusLE (k := K) d r)
        + ((r * (d 0 + d (Fin.last N) - r) : ℕ) : ℕ∞)

end BrickB

/-! ## R2-general — the payoff `rlct(K^DLN_B) = (C + r(d_0+d_N−r))/2`

Pure transport through both Cited interfaces and Brick A. -/

section R2General

variable {d : Fin (N + 1) → ℕ}
  {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

/-- **The general-`r` RLCT payoff, through the Cited Aoyagi rlct AND the Cited Lemma-4.6 shift.**
Given the Cited interfaces `I` (Aoyagi rlct) and `J` (Lemma 4.6 bundle shift), for `B` of rank
`r ≤ min d` the rlct of the DLN square-Frobenius loss `K^DLN_B` equals
`(cCodim d r + r(d_0+d_N−r))/2`: the combinatorial `C/2` plus the half-shift. Proof: `I.cited_aoyagi_dln`
(general in `r`) gives `rlct = ½·codim mult⁻¹(B)`; `J.cited_bundle_shift_lemma46` rewrites the fibre
codim as `codim Σ̄^r + shift`; Brick A (`codimRepCanonical_productRankLocusLE_eq_cCodim`) rewrites
`codim Σ̄^r = cCodim d r`. Both interfaces `I`, `J` are explicit in the type (both Cited dependencies
visible); `via_aoyagi` names the rlct source. This is **not** an unconditional `rlct = (C + shift)/2`.
`[IsAlgClosed K] [CharZero K]` (the scope where `C` is the geometric codimension). -/
theorem rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi
    (I : RlctInterface d K ι) (J : BundleShiftInterface d K ι)
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ} {r : ℕ}
    (hB : B.rank = r) (hr : ∀ k', r ≤ d k') (h : (kostantPartitions d r).Nonempty) :
    I.rlct (lossDLN d B)
      = (((cCodim d r h).toNat : ℝ) + (r * (d 0 + d (Fin.last N) - r) : ℕ)) / 2 := by
  -- the Aoyagi guard `r ≤ univ.inf' d` is `∀ k, r ≤ d k`
  have hrinf : r ≤ Finset.univ.inf' Finset.univ_nonempty d := by
    rw [Finset.le_inf'_iff]; exact fun b _ ↦ hr b
  rw [I.cited_aoyagi_dln B r hB hrinf, J.cited_bundle_shift_lemma46 B r hB hr]
  -- split the `ℕ∞.toNat` of the sum: both summands finite
  have hAfin : codimRepCanonical (productRankLocusLE (k := K) d r) ≠ ⊤ := by
    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]; exact ENat.coe_ne_top _
  have hAval : (codimRepCanonical (productRankLocusLE (k := K) d r)).toNat = (cCodim d r h).toNat := by
    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
  rw [ENat.toNat_add hAfin (ENat.coe_ne_top _), hAval, ENat.toNat_coe]
  push_cast
  ring

end R2General

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 1`

The worked example `d = (2,2,2)` at rank `r = 1` (Lehalleur–Rimányi §4): the combinatorial
`C = cCodim d222 1 = 1` (LANDED `Core.CTheta.cCodim_d222_one`), the bundle shift
`1·(2+2−1) = 3`, so the predicted fibre codim is `4` and the RLCT payoff is `(1+3)/2 = 2`. The
codimension of `Σ̄^1` is shown over `AlgebraicClosure ℚ`; the rlct payoff over `ℂ` (which carries
the embedding `ℝ →+* ℂ` the interface needs — as the LANDED `r = 0` `(2,2,2)` witness does). The fibre
codim and the rlct value were independently checked by direct Jacobian rank (thread 11). -/

section Witness

/-- **`(2,2,2)`, `r = 1`: the geometric codimension of `Σ̄^1` is `1`**, over `AlgebraicClosure ℚ` —
the geometric reading of the combinatorial `C = cCodim d222 1 = 1` (LR §4), via Brick A. -/
theorem codimRepCanonical_productRankLocusLE_d222_one :
    (codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) Core.d222 1)).toNat = 1 := by
  have h := codimRepCanonical_productRankLocusLE_eq_cCodim (k := AlgebraicClosure ℚ) Core.d222 1
    Core.kostantPartitions_d222_one_nonempty
  rw [Core.cCodim_d222_one] at h
  omega

/-- **`(2,2,2)`, `r = 1`: the RLCT payoff `rlct(K^DLN_B) = 2`**, over `ℂ`, for `B` of rank `1`,
through the Cited Aoyagi interface `I` and the Cited Lemma-4.6 bundle-shift interface `J`. The
combinatorial `C = cCodim d222 1 = 1` and the shift `1·(2+2−1) = 3` give `rlct = (1+3)/2 = 2`: the
`(2,2,2)` rank-`1` DLN is mildly singular. Both interfaces `I`, `J` are the explicit Cited
hypotheses. -/
theorem rlct_lossDLN_d222_one_eq_two_via_aoyagi
    (I : RlctInterface Core.d222 ℂ Complex.ofRealHom)
    (J : BundleShiftInterface Core.d222 ℂ Complex.ofRealHom)
    {B : Matrix (Fin (Core.d222 (Fin.last 2))) (Fin (Core.d222 0)) ℝ} (hB : B.rank = 1) :
    I.rlct (lossDLN Core.d222 B) = 2 := by
  have hr : ∀ k', (1 : ℕ) ≤ Core.d222 k' := Core.d222_one_le
  rw [rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi I J hB hr
    Core.kostantPartitions_d222_one_nonempty, Core.cCodim_d222_one]
  have hshift : (1 : ℕ) * (Core.d222 0 + Core.d222 (Fin.last 2) - 1) = 3 := by decide
  rw [hshift]
  norm_num

end Witness

end DLNFibre.DLN
