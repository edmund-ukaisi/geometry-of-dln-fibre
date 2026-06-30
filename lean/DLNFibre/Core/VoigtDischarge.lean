import DLNFibre.Core.OrbitTangentCotangent
import DLNFibre.Core.OrbitDifferentialRank
import DLNFibre.Core.AlgebraicGeometry.Group.Orbit.Squeeze
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.Algebra.CharZero.Infinite

/-!
# `DLNFibre.Core.VoigtDischarge` — A6.2: the squeeze + L7, discharging `hVoigt`

The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
dimension). The additive **L7** arithmetic then yields **Voigt's lemma** `hVoigt`:

> `codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`,

cancelling the finite `r = finrank (range δ⁰)` from the two additive identities
`codimRep + r = card` (L0 + squeeze) and `orbitLinearCodim + r = card` (rank-nullity + `card = finrank C¹`).
Discharging `hVoigt` makes `codimRepCanonical_orbitRankLocus_eq_multSum` **UNCONDITIONAL** over any
characteristic-zero field — the expedition's deliverable.

**Typeclass.** `[Field k] [CharZero k]` only. `CharZero` supplies both `PerfectField` (smooth point ⟹
regular, A6.1/M3) and `Infinite` (orbit primeness L0/L1, A4 separability) as Mathlib instances; algebraic
closedness is not used. The squeeze holds over `ℝ` (witnessed below). **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix Module MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/

/-- **The squeeze (Voigt's geometric heart).** The variety dimension of the orbit closure `Z_M =
canonicalCoord '' orbitRankLocus M` equals the dimension of the orbit tangent image `range δ⁰`.

Now a transport of the **abstract orbit-dimension squeeze headline**
(`AlgebraicGeometry.Group.Orbit.varietyDim_eq_finrank_range_δ`, `Orbit/Squeeze.lean`) at the DLN
deformation instance `dlnOrbitDef M`: the matrix tuple discharges the full hypothesis bundle —
(H1) via `dlnOrbitDef_differentialFactors M` (adjoint `deltaT M`, rank-tie `finrank_range_deltaT`),
the criterion via `diffIndepCriterion_groupRing`, (H2) via `dlnInfinitesimalAction M`, the smooth
`k`-rational point via `isSmoothAt_normalFormIdeal` + `residueFieldAtPrimeNormalFormEquiv`, and the
A0/orbit↔kernel bridges. The base ideal `(dlnInfinitesimalAction M).basePtIdeal = normalFormIdeal M`
and `(dlnOrbitDef M).δ = deformationδ M M` definitionally, so the abstract `varietyDim = finrank
(range δ)` IS this statement. `[CharZero k]` supplies `[PerfectField k]` + `[Infinite k]` as Mathlib
instances. Holds over any characteristic-zero field, `ℝ` included. -/
theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
    [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    varietyDim (canonicalCoord d '' orbitRankLocus M)
      = (finrank k (LinearMap.range (deformationδ M M)) : ℕ∞) := by
  letI : Fintype (RepCoord d) := Fintype.ofFinite _
  haveI hρ : Finite (dlnOrbitDef M).ρ := inferInstanceAs (Finite (RepCoord d))
  -- freeze the (H2) discharge + its base ideal (`H.basePtIdeal = normalFormIdeal M` defeq), so the
  -- bracketed instance arguments are keyed SYNTACTICALLY on `H.basePtIdeal` — no instance search
  -- across a defeq (the whnf-timeout trigger; Codex-diagnosed). The (H1) transport `L` is left
  -- implicit, inferred from the type of `dlnOrbitDef_differentialFactors M` (the `pairMC` lift).
  set H : (dlnOrbitDef M).InfinitesimalAction (orbitIdeal M) := dlnInfinitesimalAction M with hH
  have hPrime : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
  have hmMax : (H.basePtIdeal).IsMaximal := orbitPointIdeal_isMaximal M 1
  have hmSm : Algebra.IsSmoothAt k (H.basePtIdeal) := isSmoothAt_normalFormIdeal (k := k) M
  have hmFin : FiniteDimensional k (H.basePtIdeal).Cotangent :=
    finiteDimensional_cotangent_normalFormIdeal M
  have hrat : Ideal.ResidueField (H.basePtIdeal) ≃ₐ[k] k := residueFieldAtPrimeNormalFormEquiv M
  -- the orbit↔kernel linkage `orbitIdeal M = ker (dlnOrbitDef M).pullback`
  have hIker : orbitIdeal M
      = RingHom.ker (dlnOrbitDef M).toAffineGVariety.pullback.toRingHom := by
    show orbitIdeal M = RingHom.ker (orbitPullback M).toRingHom
    rw [orbitIdeal, ← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker]
  exact @AlgebraicGeometry.Group.Orbit.varietyDim_eq_finrank_range_δ k _ _
    (dlnOrbitDef M) hρ (deltaT M) _
    (dlnOrbitDef_differentialFactors M) (finrank_range_deltaT M) diffIndepCriterion_groupRing
    (orbitIdeal M) H hmFin hPrime hmMax hmSm hrat
    (canonicalCoord d '' orbitRankLocus M)
    (vanishingIdeal_orbitRankLocus_eq_orbitSet M) hIker

/-! ## L7 — the additive cancellation discharging `hVoigt` -/

/-- **L7 — Voigt's lemma `hVoigt`, discharged.** The geometric codimension of the orbit closure equals
the expected (tangent-space) codimension:
`codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`. From the two additive
identities — `codimRep + r = card` (L0 bridge + the squeeze, `r = finrank (range δ⁰)`) and
`orbitLinearCodim + r = card` (rank-nullity `orbitLinearCodim = finrank C¹ − r` + `card = finrank C¹`,
GAP1) — by cancelling the finite `r : ℕ∞`. -/
theorem codimRep_orbitRankLocus_eq_orbitLinearCodim
    [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞) := by
  set r : ℕ := finrank k (LinearMap.range (deformationδ M M)) with hr
  set c1 : ℕ := finrank k (cochain1 (k := k) d d) with hc1
  -- `r ≤ c1` (the orbit tangent image is a subspace of `C¹`)
  have hrc1 : r ≤ c1 := Submodule.finrank_le _
  -- L0 + squeeze: `codimRep + r = card`
  have hL0 : codimRep (canonicalCoord d) (orbitRankLocus M) + (r : ℕ∞)
      = (Nat.card (RepCoord d) : ℕ∞) := by
    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
      (isPrime_vanishingIdeal_orbitRankLocus M)
    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
  -- rank-nullity + GAP1: `orbitLinearCodim + r = card`
  have hRN : (orbitLinearCodim M : ℕ∞) + (r : ℕ∞) = (Nat.card (RepCoord d) : ℕ∞) := by
    rw [← Nat.cast_add, card_repCoord_eq_finrank_cochain1 (k := k), ← hc1]
    have : orbitLinearCodim M + r = c1 := by rw [orbitLinearCodim, ← hr, ← hc1]; omega
    rw [this]
  -- cancel the finite `r`: `r + codimRep = card = r + orbitLinearCodim`
  have heq : (r : ℕ∞) + codimRep (canonicalCoord d) (orbitRankLocus M)
      = (r : ℕ∞) + (orbitLinearCodim M : ℕ∞) := by
    rw [add_comm (r : ℕ∞), add_comm (r : ℕ∞), hL0, hRN]
  exact ((ENat.addLECancellable_coe r).inj.mp heq)

/-! ## The unconditional headlines -/

/-- **`hVoigt` at the canonical flattening, discharged (`ℕ∞` form).** The geometric codimension of the
orbit closure equals `dim Ext¹(M,M)`, now UNCONDITIONAL over any characteristic-zero field: Voigt's
lemma `codimRep_orbitRankLocus_eq_orbitLinearCodim` chained with the engine's
`orbitLinearCodim_eq_finrank_deformationExt1`. -/
theorem codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1_unconditional
    [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    codimRepCanonical (orbitRankLocus M) = (finrank k (deformationExt1 M M) : ℕ∞) :=
  codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1 M
    (codimRep_orbitRankLocus_eq_orbitLinearCodim M)

/-- **The geometric-codimension headline (Lehalleur–Rimányi Cor 3.5), UNCONDITIONAL.** For
`M = ⊕_{(a,b)∈L} M_{ab}` the geometric codimension of the orbit closure `Ō_M` (the rank locus, Thm 3.8
PROVED in-engine, `Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`) equals the paper's
quadratic form `Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}` — no longer modulo
`hVoigt`. `hVoigt` is discharged by `codimRep_orbitRankLocus_eq_orbitLinearCodim` (the squeeze + L7),
so the expedition's deliverable holds with hypothesis `[CharZero k]` only. -/
theorem codimRepCanonical_orbitRankLocus_eq_multSum_unconditional
    [CharZero k] (L : List (Fin (N + 1) × Fin (N + 1))) :
    ((codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v :=
  codimRepCanonical_orbitRankLocus_eq_multSum L
    (codimRep_orbitRankLocus_eq_orbitLinearCodim (intervalDirectSum (k := k) L))

/-! ## Capstone non-vacuity witness — the hypothesis fires on a genuine orbit

The capstone carries `[CharZero k]`. `AlgebraicClosure ℚ` is a characteristic-zero field, so
instantiating the capstone there shows the antecedent is satisfiable on the genuine `(2,2,2)`
`(1,1)`-orbit normal form `M = M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}`
(`L = [(0,0),(0,1),(1,2),(2,2)]`, Le Halleur–Rimányi Ex 4.3). (The stronger `ℝ` witnesses below
exhibit the same capstone over a non-algebraically-closed field, the point of the crux relaxation.)
-/

/-- The algebraic closure of `ℚ`: a `[CharZero]` field — a capstone witness. -/
noncomputable abbrev VoigtWitnessField : Type := AlgebraicClosure ℚ

/-- The `(2,2,2)` `(1,1)`-orbit normal form as an interval direct-sum list,
`M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}` (Le Halleur–Rimányi Ex 4.3). -/
def voigtWitnessList222 : List (Fin 3 × Fin 3) :=
  [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)]

/-- **Capstone non-vacuity (`(2,2,2)` over `AlgebraicClosure ℚ`).** The discharged Voigt lemma
`codimRep_orbitRankLocus_eq_orbitLinearCodim` fires over its actual hypothesis `[CharZero k]` —
instantiated at `k = AlgebraicClosure ℚ` on the genuine `(2,2,2)` `(1,1)`-orbit
`M = ⊕_{(a,b)∈L} M_{ab}`, `L = [(0,0),(0,1),(1,2),(2,2)]`: the geometric codimension of the orbit
closure equals the expected codimension `orbitLinearCodim M`. An in-file witness that the antecedent
is satisfiable. -/
theorem voigtDischarge_witness_222 :
    codimRep (canonicalCoord (foldDim voigtWitnessList222))
        (orbitRankLocus (intervalDirectSum (k := VoigtWitnessField) voigtWitnessList222))
      = (orbitLinearCodim (intervalDirectSum (k := VoigtWitnessField) voigtWitnessList222) : ℕ∞) :=
  codimRep_orbitRankLocus_eq_orbitLinearCodim
    (intervalDirectSum (k := VoigtWitnessField) voigtWitnessList222)

/-! ## The squeeze over `ℝ` — the crux relaxation, witnessed

`ℝ` is `[CharZero]` (hence `[PerfectField]` and `[Infinite]`) but not algebraically closed. The crux
relaxation `[IsAlgClosed k] → [PerfectField k]` on the A6.1 reverse inequality lets the squeeze
`varietyDim Z_M = finrank (range δ⁰)` and Voigt's lemma `codimRep = orbitLinearCodim` fire over `ℝ`,
witnessed here on the genuine `(2,2,2)` `(1,1)`-orbit normal form. These are the deliverables that
were previously unreachable over `ℝ` (the orbit-dimension chain consumed algebraic closedness). -/

/-- **The squeeze fires over `ℝ`.** The variety dimension of the `(2,2,2)` orbit closure over `ℝ`
equals the dimension of its orbit tangent image — the crux relaxation `[IsAlgClosed] →
[PerfectField]` made real, on a non-algebraically-closed field. -/
example :
    varietyDim (canonicalCoord (foldDim voigtWitnessList222) ''
        orbitRankLocus (intervalDirectSum (k := ℝ) voigtWitnessList222))
      = (finrank ℝ (LinearMap.range (deformationδ
          (intervalDirectSum (k := ℝ) voigtWitnessList222)
          (intervalDirectSum (k := ℝ) voigtWitnessList222))) : ℕ∞) :=
  varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
    (intervalDirectSum (k := ℝ) voigtWitnessList222)

/-- **Voigt's lemma fires over `ℝ`.** The geometric codimension of the `(2,2,2)` orbit closure over
`ℝ` equals its expected (tangent-space) codimension `orbitLinearCodim` — discharged with no
algebraic closedness, over a characteristic-zero field. -/
example :
    codimRep (canonicalCoord (foldDim voigtWitnessList222))
        (orbitRankLocus (intervalDirectSum (k := ℝ) voigtWitnessList222))
      = (orbitLinearCodim (intervalDirectSum (k := ℝ) voigtWitnessList222) : ℕ∞) :=
  codimRep_orbitRankLocus_eq_orbitLinearCodim
    (intervalDirectSum (k := ℝ) voigtWitnessList222)

end DLNFibre.Core
