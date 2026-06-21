import DLNFibre.Core.OrbitTangentCotangent
import DLNFibre.Core.OrbitDifferentialRank
import DLNFibre.Core.NullstellensatzCodim

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
Discharging `hVoigt` makes `codimRepCanonical_orbitRankLocus_eq_multSum` **UNCONDITIONAL** (char 0,
algebraically closed) — the expedition's deliverable.

**Typeclass.** `[Field k] [IsAlgClosed k] [CharZero k]`: `IsAlgClosed` from A6.1/L0/L1/M3 (which also
gives `Infinite`), `CharZero` only from A4's separability side. **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix Module MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/

/-- **The squeeze (Voigt's geometric heart).** The variety dimension of the orbit closure `Z_M =
canonicalCoord '' orbitRankLocus M` equals the dimension of the orbit tangent image `range δ⁰`:
`le_antisymm` of A4's submersion bound (`≤`, char 0) and A6.1's reverse inequality (`≥`). -/
theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
    [IsAlgClosed k] [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    varietyDim (canonicalCoord d '' orbitRankLocus M)
      = (finrank k (LinearMap.range (deformationδ M M)) : ℕ∞) := by
  letI : Fintype (RepCoord d) := Fintype.ofFinite _
  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M

/-! ## L7 — the additive cancellation discharging `hVoigt` -/

/-- **L7 — Voigt's lemma `hVoigt`, discharged.** The geometric codimension of the orbit closure equals
the expected (tangent-space) codimension:
`codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`. From the two additive
identities — `codimRep + r = card` (L0 bridge + the squeeze, `r = finrank (range δ⁰)`) and
`orbitLinearCodim + r = card` (rank-nullity `orbitLinearCodim = finrank C¹ − r` + `card = finrank C¹`,
GAP1) — by cancelling the finite `r : ℕ∞`. -/
theorem codimRep_orbitRankLocus_eq_orbitLinearCodim
    [IsAlgClosed k] [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
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
orbit closure equals `dim Ext¹(M,M)`, now UNCONDITIONAL (char 0, algebraically closed): Voigt's lemma
`codimRep_orbitRankLocus_eq_orbitLinearCodim` chained with the engine's
`orbitLinearCodim_eq_finrank_deformationExt1`. -/
theorem codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1_unconditional
    [IsAlgClosed k] [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    codimRepCanonical (orbitRankLocus M) = (finrank k (deformationExt1 M M) : ℕ∞) :=
  codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1 M
    (codimRep_orbitRankLocus_eq_orbitLinearCodim M)

/-- **The geometric-codimension headline (Lehalleur–Rimányi Cor 3.5), UNCONDITIONAL.** For
`M = ⊕_{(a,b)∈L} M_{ab}` the geometric codimension of the orbit closure `Ō_M` (the rank locus, Thm 3.8
PROVED in-engine, `Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`) equals the paper's
quadratic form `Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}` — no longer modulo
`hVoigt`. `hVoigt` is discharged by `codimRep_orbitRankLocus_eq_orbitLinearCodim` (the squeeze + L7),
so the expedition's deliverable holds with hypotheses `[IsAlgClosed k] [CharZero k]` only. -/
theorem codimRepCanonical_orbitRankLocus_eq_multSum_unconditional
    [IsAlgClosed k] [CharZero k] (L : List (Fin (N + 1) × Fin (N + 1))) :
    ((codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v :=
  codimRepCanonical_orbitRankLocus_eq_multSum L
    (codimRep_orbitRankLocus_eq_orbitLinearCodim (intervalDirectSum (k := k) L))

/-! ## Capstone non-vacuity witness — the hypotheses fire on a genuine orbit

The capstone carries `[IsAlgClosed k] [CharZero k]`. The committed `(2,2,2)` examples in
`OrbitLinearCodim`/`OrbitVariety` are over `ℚ`, where neither instance holds, so they do not exhibit
the capstone firing over its actual hypotheses. `AlgebraicClosure ℚ` carries both (`IsAlgClosed` from
`AlgebraicClosure.isAlgClosed`, `CharZero` from `ℚ`'s), so instantiating the capstone there shows the
antecedents are satisfiable on the genuine `(2,2,2)` `(1,1)`-orbit normal form
`M = M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}` (`L = [(0,0),(0,1),(1,2),(2,2)]`, Le Halleur–Rimányi Ex 4.3).
-/

/-- The algebraic closure of `ℚ`: an `[IsAlgClosed] [CharZero]` field — the capstone's witness. -/
noncomputable abbrev VoigtWitnessField : Type := AlgebraicClosure ℚ

/-- The `(2,2,2)` `(1,1)`-orbit normal form as an interval direct-sum list,
`M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}` (Le Halleur–Rimányi Ex 4.3). -/
def voigtWitnessList222 : List (Fin 3 × Fin 3) :=
  [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)]

/-- **Capstone non-vacuity (`(2,2,2)` over `AlgebraicClosure ℚ`).** The discharged Voigt lemma
`codimRep_orbitRankLocus_eq_orbitLinearCodim` fires over its actual hypotheses
`[IsAlgClosed k] [CharZero k]` — instantiated at `k = AlgebraicClosure ℚ` on the genuine `(2,2,2)`
`(1,1)`-orbit `M = ⊕_{(a,b)∈L} M_{ab}`, `L = [(0,0),(0,1),(1,2),(2,2)]`: the geometric codimension of
the orbit closure equals the expected codimension `orbitLinearCodim M`. An in-file witness that the
antecedents are satisfiable (the committed `(2,2,2)` examples are over `ℚ`, where they are not). -/
theorem voigtDischarge_witness_222 :
    codimRep (canonicalCoord (foldDim voigtWitnessList222))
        (orbitRankLocus (intervalDirectSum (k := VoigtWitnessField) voigtWitnessList222))
      = (orbitLinearCodim (intervalDirectSum (k := VoigtWitnessField) voigtWitnessList222) : ℕ∞) :=
  codimRep_orbitRankLocus_eq_orbitLinearCodim
    (intervalDirectSum (k := VoigtWitnessField) voigtWitnessList222)

end DLNFibre.Core
