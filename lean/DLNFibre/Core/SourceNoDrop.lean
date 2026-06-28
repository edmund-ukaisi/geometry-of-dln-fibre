/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartLocalizedCoordinates
import DLNFibre.Core.ClosureBridge
import DLNFibre.Core.ThetaComponentCount
import DLNFibre.Core.ChartEvalRealize
import DLNFibre.Core.FibreNormalForm

/-!
# `DLNFibre.Core.SourceNoDrop` — `hsig`: the source no-drop over `O(Σ^r)`

The source no-drop the localized-chart sweep wiring (`Core.ChartSweepWiring`) consumes:

> `hsig : ringKrullDim (Localization.Away (chartDsig …)) = ringKrullDim (sweepSigmaRing …)`

i.e. inverting the deep pivot minor `detΔ = ΔPdeep d r` over the chart-closure coordinate ring
`O(Σ^r) = sweepSigmaRing` does not drop the Krull dimension.

Discharged via the LANDED reducible-ring no-drop
`Core.AffineLocalizationNoDrop.ringKrullDim_localizationAway_eq_of_avoids_top_prime` at the prime
`p₀ = P / I_eq` of `O(Σ^r)`, where:

- `P = partitionIdeal d r m₀` for a *minimising* Kostant partition `m₀` — a corner-`r` top minimal
  prime of `sigmaIdeal d r` (Fact A, `Core.CCodimCornerMono`; here we use the minimiser directly so
  the height read-off is free);
- `I_eq = vanishingIdeal (Σ^r) ⊆ P` is FREE: the corner-`r` realizer orbit sits in `Σ^r`
  (`Core.ClosureBridge.orbitAsTuples_realizerD_subset_productRankLocus`), and `vanishingIdeal` is
  invisible to the orbit closure (`Core.OrbitClosure.vanishingIdeal_repClosure`), so the orbit-rank
  locus (= closure of the orbit) is contained in `Σ^r` *as far as `vanishingIdeal` sees*;
- `p₀ = P/I_eq` carries the full dimension (catenary `height + dim = card`, with `height P = C =
  height I_eq` both reading the combinatorial codimension `C = cCodim d r`, the latter via the
  closure-bridge `codim Σ^r = C`);
- `detΔ ∉ P` (**Fact B**): the realizer `M₀` has `rank (mult M₀) = r`, so an end-factor base change
  (`Core.FibreNormalForm.exists_baseChange_of_rank_eq`) carries `mult M₀` to the rank-`r` normal
  form `E = diag(I_r, 0)`, with top-left `r×r` minor `1 ≠ 0`; the base-changed tuple stays in
  `orbitRankLocus M₀` (rank-pattern invariance), so `ΔPdeep` does not vanish on the locus.

No global rank-raising / density theorem, no `I_eq = I_le` ideal equality.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Fact B — `detΔ ∉ P` for the corner-`r` realizer's orbit-rank-locus ideal -/

/-- **`chartΔ` of the rank-`r` normal form is the identity.** The top-left `r×r` block of
`normalForm p q r = diag(I_r, 0)` is `I_r`, so its determinant is `1`. -/
theorem chartΔ_normalForm (p q r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    chartΔ (normalForm (k := k) p q r hp hq) hp hq = 1 := by
  ext i j
  rw [chartΔ, normalForm, Matrix.submatrix_apply, Matrix.submatrix_apply,
    finSplit_castLE, finSplit_castLE, Matrix.fromBlocks_apply₁₁]

/-- **Fact B (the avoidance, locus form).** The deep pivot minor `ΔPdeep d r` does not vanish on the
orbit-rank locus of the corner-`r` realizer `M₀`: there is a point `A ∈ orbitRankLocus M₀` (a base
change of `M₀`) at which `ΔPdeep` evaluates to a nonzero scalar (the top-left `r×r` minor of the
rank-`r` normal form, `= 1`). So `ΔPdeep` is not in the orbit-rank-locus vanishing ideal. -/
theorem chartDsig_not_mem_partitionIdeal [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    {m : Fin (N + 2) × Fin (N + 2) → ℕ} (hm : m ∈ kostantPartitions d r) :
    ΔPdeep (k := k) d r hp hq ∉
      MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm)) := by
  set M₀ := realizerD (k := k) hm with hM₀
  -- the realizer has product rank exactly `r`; the rank-`r` normal form `E` has the same rank.
  have hrankM₀ : (mult d M₀).rank = r := rank_mult_realizerD hm
  set E : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k :=
    normalForm (d (Fin.last (N + 1))) (d 0) r hp hq with hE
  have hrankE : E.rank = r := rank_normalForm _ _ _ hp hq
  -- an end-factor base change `P` carrying `mult M₀` to `E`.
  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN (mult d M₀) E (hrankM₀.trans hrankE.symm)
  -- the base-changed tuple `A = P • M₀` has product `mult A = E` and stays in `orbitRankLocus M₀`.
  set A := P • M₀ with hA
  have hmultA : mult d A = E := by rw [hA, mult_smul, ← hP]
  have hAmem : A ∈ orbitRankLocus M₀ := by
    intro i j hij
    rw [← rankPattern_eq_of_smul P hA.symm i j hij]
  -- `ΔPdeep` evaluates at `A` to `det (chartΔ (mult A)) = det (chartΔ E) = 1 ≠ 0`.
  have heval : eval (canonicalCoord d A) (ΔPdeep (k := k) d r hp hq) = 1 := by
    rw [ΔPdeep, eval_det_submatrix_multPoly]
    change (chartΔ (mult d A) hp hq).det = 1
    rw [hmultA, chartΔ_normalForm, Matrix.det_one]
  -- so `ΔPdeep` does not vanish on the locus.
  intro hmem
  have hvan : eval (canonicalCoord d A) (ΔPdeep (k := k) d r hp hq) = 0 := by
    rw [← aeval_eq_eval]
    exact (mem_vanishingIdeal_iff.mp hmem) _ ⟨A, hAmem, rfl⟩
  rw [heval] at hvan
  exact one_ne_zero hvan

/-! ## Step 2 — `I_eq ⊆ P` (the free per-component containment) -/

/-- **`I_eq ⊆ P` (step 2, the FREE per-component containment).** The vanishing ideal `I_eq` of
`Σ^r = canonicalCoord '' productRankLocus d r` is contained in the orbit-rank-locus ideal `P` of the
corner-`r` realizer `M₀`: the realizer's orbit sits in `Σ^r`
(`orbitAsTuples_realizerD_subset_productRankLocus`), and the orbit-rank locus has the same vanishing
ideal as the orbit (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), so anti-monotonicity of
`vanishingIdeal` against `orbitSet M₀ ⊆ Σ^r` gives `I_eq ⊆ P`. No density / rank-raising theorem. -/
theorem vanishingIdeal_sweepSigma_le_orbitRankLocus [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    {m : Fin (N + 2) × Fin (N + 2) → ℕ} (hm : m ∈ kostantPartitions d r) :
    (vanishingIdeal k (sweepSigma k d r) : Ideal (MvPolynomial (RepCoord d) k))
      ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm)) := by
  -- `P = vanishingIdeal (orbitSet M₀)` (the orbit-rank locus is `vanishingIdeal`-equivalent to it).
  rw [vanishingIdeal_orbitRankLocus_eq_orbitSet]
  -- `orbitSet M₀ ⊆ Σ^r = sweepSigma`: the realizer orbit is contained in `Σ^r`.
  have hsub : orbitSet (realizerD (k := k) hm) ⊆ sweepSigma k d r := by
    rw [← image_orbitAsTuples]
    exact Set.image_mono (orbitAsTuples_realizerD_subset_productRankLocus hm)
  -- anti-monotonicity of `vanishingIdeal`.
  exact MvPolynomial.vanishingIdeal_anti_mono hsub

/-! ## The source no-drop `hsig` -/

/-- **`hsig`: the source no-drop over `O(Σ^r)`.** Inverting the deep pivot minor `detΔ = ΔPdeep d r`
over the chart-closure coordinate ring `O(Σ^r) = sweepSigmaRing` does not drop the Krull dimension:

> `ringKrullDim (Localization.Away (chartDsig …)) = ringKrullDim (sweepSigmaRing …)`.

The exact source no-drop that `Core.ChartSweepWiring.sweep_of_localizedChartAlgEquiv` consumes,
anchored on the rank-exactly-`r` ring (no wrapper restate). -/
theorem ringKrullDim_localizationAway_chartDsig_eq [CharZero k] [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1))
    (h : (kostantPartitions d r).Nonempty) :
    ringKrullDim (Localization.Away (chartDsig k d r hp hq))
      = ringKrullDim (sweepSigmaRing k d r) := by
  classical
  -- step 0: a minimising Kostant partition `m₀` and its realizer's orbit-rank-locus ideal `P`.
  obtain ⟨m₀, hm₀, hval⟩ :=
    Finset.exists_mem_eq_inf' h (fun m ↦ codimForm (N + 1) (extendℤ m))
  set Ieq : Ideal (MvPolynomial (RepCoord d) k) := vanishingIdeal k (sweepSigma k d r) with hIeq
  set P : Ideal (MvPolynomial (RepCoord d) k) :=
    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
      (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm₀)) with hP
  -- step 1: `P` is prime (the orbit-rank locus is irreducible).
  haveI hPprime : P.IsPrime := isPrime_vanishingIdeal_orbitRankLocus _
  -- step 2: `Ieq ⊆ P` (the free per-component containment).
  have hle : Ieq ≤ P := vanishingIdeal_sweepSigma_le_orbitRankLocus d r hm₀
  -- `height P = C.toNat` (the minimiser realizer is top-dimensional) and `height Ieq = C.toNat`
  -- (closure-bridge `codim Σ^r = C`); so `height P = height Ieq`.
  have hcCnn : 0 ≤ cCodim d r h := by
    rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
    exact fun m' _ ↦ Int.natCast_nonneg _
  have hPfin : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀)) ≠ ⊤ := by
    rw [codimRepCanonical_orbitRankLocus_eq_height]
    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
  -- the realizer orbit attains codim `C` (mirrors `ClosureBridge`'s `hreal`).
  have hcodP : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))
      = ((cCodim d r h).toNat : ℕ∞) := by
    have hceq : cCodim d r h = codimForm (N + 1) (extendℤ m₀) := hval
    have htn : ((codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))).toNat : ℤ)
        = (cCodim d r h).toNat := by
      rw [codimRepCanonical_orbitRankLocus_realizerD hm₀, hceq]; omega
    rw [← ENat.coe_toNat hPfin]; exact_mod_cast htn
  -- step 5: the top prime `p₀ = P/Ieq` of `O(Σ^r) = sweepSigmaRing`; prime, full-dimensional.
  set p₀ : Ideal (sweepSigmaRing k d r) := P.map (Ideal.Quotient.mk Ieq) with hp₀
  haveI hp₀prime : p₀.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hle)
  -- `htop`: `ringKrullDim (O(Σ^r) ⧸ p₀) = ringKrullDim O(Σ^r)`, via equal `varietyDim`s at `ℕ∞`.
  have htop : ringKrullDim (sweepSigmaRing k d r ⧸ p₀)
      = ringKrullDim (sweepSigmaRing k d r) := by
    -- `O(Σ^r) ⧸ p₀ ≃+* MvPoly ⧸ P` (third iso, `Ieq ≤ P`); `sweepSigmaRing = MvPoly ⧸ Ieq`.
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle),
      (rfl : ringKrullDim (sweepSigmaRing k d r)
        = ringKrullDim (MvPolynomial (RepCoord d) k ⧸ Ieq))]
    -- both quotients are nontrivial (proper ideals), so their `ringKrullDim` is a genuine `ℕ∞`.
    have hIeqne : Ieq ≠ ⊤ :=
      vanishingIdeal_ne_top_of_nonempty (nonempty_image_productRankLocus d r h)
    haveI : Nontrivial (MvPolynomial (RepCoord d) k ⧸ P) :=
      Ideal.Quotient.nontrivial_iff.mpr hPprime.ne_top
    haveI : Nontrivial (MvPolynomial (RepCoord d) k ⧸ Ieq) :=
      Ideal.Quotient.nontrivial_iff.mpr hIeqne
    -- recover each `ringKrullDim` as `↑(varietyDim ·)` (`varietyDim = (ringKrullDim).unbotD 0`),
    -- where the loci are `Worb` (orbit-rank locus) and `Wsig` (`Σ^r`).
    have hPne : ringKrullDim (MvPolynomial (RepCoord d) k ⧸ P) ≠ ⊥ := by
      have : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (RepCoord d) k ⧸ P) :=
        ringKrullDim_nonneg_of_nontrivial
      intro hb; rw [hb] at this; exact absurd this (by simp)
    have hIne : ringKrullDim (MvPolynomial (RepCoord d) k ⧸ Ieq) ≠ ⊥ := by
      have : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (RepCoord d) k ⧸ Ieq) :=
        ringKrullDim_nonneg_of_nontrivial
      intro hb; rw [hb] at this; exact absurd this (by simp)
    obtain ⟨aP, haP⟩ := WithBot.ne_bot_iff_exists.mp hPne
    obtain ⟨aI, haI⟩ := WithBot.ne_bot_iff_exists.mp hIne
    -- `varietyDim Worb = aP`, `varietyDim Wsig = aI` (`P`/`Ieq` the respective vanishing ideals).
    have hvP : varietyDim (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm₀)) = aP := by
      change (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ P)).unbotD 0 = aP
      rw [← haP, WithBot.unbotD_coe]
    have hvI : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r) = aI := by
      change (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ Ieq)).unbotD 0 = aI
      rw [← haI, WithBot.unbotD_coe]
    -- equal codims (`= C`) ⟹ equal `varietyDim`s (the `ℕ∞` catenary on each, left-cancel `C`).
    have hcodI : codimRepCanonical (productRankLocus (k := k) d r)
        = ((cCodim d r h).toNat : ℕ∞) :=
      codimRepCanonical_productRankLocus_eq_cCodim_enat d r h
    have hcatP := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := k)
      (Z := orbitRankLocus (realizerD (k := k) hm₀))
      (Set.Nonempty.image _ ⟨_, self_mem_orbitRankLocus _⟩)
    have hcatI := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := k)
      (Z := productRankLocus (k := k) d r) (nonempty_image_productRankLocus d r h)
    rw [hcodP] at hcatP
    rw [hcodI] at hcatI
    have hveq : varietyDim (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm₀))
        = varietyDim (canonicalCoord d '' productRankLocus (k := k) d r) :=
      ENat.add_right_injective_of_ne_top (ENat.coe_ne_top _) (hcatP.trans hcatI.symm)
    rw [← haP, ← haI]; exact_mod_cast hvP ▸ hvI ▸ hveq
  -- step 7: `chartDsig = mk Ieq (ΔPdeep) ∉ p₀` (transport Fact B across the quotient).
  have hg : chartDsig k d r hp hq ∉ p₀ := by
    rw [chartDsig, hp₀]
    intro hmem
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hmem
    obtain ⟨x, hxP, hxeq⟩ := hmem
    -- `mk Ieq (ΔPdeep − x) = 0`, so `ΔPdeep − x ∈ Ieq ⊆ P`; with `x ∈ P` ⟹ `ΔPdeep ∈ P` (Fact B).
    have hdiff : ΔPdeep (k := k) d r hp hq - x ∈ Ieq := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hxeq, sub_self]
    have : ΔPdeep (k := k) d r hp hq ∈ P := by
      have : ΔPdeep (k := k) d r hp hq = (ΔPdeep (k := k) d r hp hq - x) + x := by ring
      rw [this]; exact P.add_mem (hle hdiff) hxP
    exact chartDsig_not_mem_partitionIdeal d r hp hq hN hm₀ this
  -- step 8: apply the LANDED no-drop.
  exact ringKrullDim_localizationAway_eq_of_avoids_top_prime (k := k)
    (sweepSigmaRing k d r) (chartDsig k d r hp hq) p₀ htop hg

end DLNFibre.Core
