import DLNFibre.Core.CTheta
import DLNFibre.Core.VoigtDischarge

/-!
# `DLNFibre.Core.CThetaGeometric` — the geometric reading of `C`, now UNCONDITIONAL

The combinatorial codimension form `codimForm` (`Core.CTheta`) was defined as a ℤ-quadratic form
over Kostant partitions; its docstrings noted that identifying it with the **geometric** codimension
of the orbit closure `Ō_M` "rides on the deferred `hVoigt`". `hVoigt` is now PROVED
(`Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim`, `[IsAlgClosed k] [CharZero k]`),
so this module records the geometric reading **without any deferral**:

1. **Per-orbit geometric reading (UNCONDITIONAL).** For a Kostant partition / interval list `L`, the
   geometric codimension of the orbit closure `Ō_M` of `M = ⊕_{(a,b)∈L} M_{ab}` (the rank locus,
   Thm 3.8 proved in `Core.OrbitClosure`), read at the canonical flattening, equals the
   combinatorial form `codimForm N (multiplicityArray L)`:
   `codimRepCanonical (orbitRankLocus (intervalDirectSum L)) = codimForm N (multiplicityArray L)`
   (`codimRepCanonical_orbitRankLocus_eq_codimForm`, ℕ∞/ℤ/ℕ forms). This is the formal statement
   "the combinatorial codimension form IS the geometric codimension of the orbit closure", no longer
   modulo Voigt. Obtained by feeding the discharged `hVoigt` into the conditional headline
   `Core.OrbitCodim.codimRepCanonical_orbitRankLocus_eq_multSum`.

2. **`cCodim` as the minimum of GEOMETRIC codimensions (UNCONDITIONAL).** The combinatorial `C`
   (`Core.CTheta.cCodim`, the min of `codimForm` over Kostant partitions) equals the minimum over
   those partitions of the **geometric** codimension of the corresponding orbit closure
   (`cCodim_eq_inf_geomCodim`). Built from deliverable 1 + the partition↔list correspondence
   `listOfPartition` realising `multiplicityArray (listOfPartition m) = extendℤ m`.

## The remaining step (roadmap, NOT built here)

The full `Σ^r`-**aggregate** geometric reading — "`cCodim d r` = geometric codimension of the whole
rank-`r` product locus `Σ^r`" and "`numTop d r` = number of top-dimensional **geometric** components
of `Σ^r`" — is NOT formalised. `Σ^r` is not defined as a geometric variety anywhere in `Core` (only
prose, in `Core.Setup` and docstrings). Closing the aggregate reading needs, for a future tide:
(i) a geometric definition of `Σ^r` (the rank-`r` product locus); (ii) its orbit stratification
`Σ^r = ⋃_M Ō_M`; (iii) codimension-of-a-union = minimum-over-components, and an analogous
top-component count. The per-orbit reading (deliverables 1, 2) is the input to that step; the
component-count half of `numTop`'s geometric reading remains open.

**Name = content.** Every headline carries `[IsAlgClosed k] [CharZero k]` (the scope of the
discharged `hVoigt`). These are geometric **codimension** statements — not RLCT, not `½·codim`; the
RLCT payoff is a separate, `DLN`-side reading (Cited Aoyagi/Watanabe). **Dependency rule:** `Core`
only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix Module MvPolynomial Finset

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Deliverable 1 — the per-orbit geometric reading, unconditional

Feed the discharged `hVoigt` (`codimRep_orbitRankLocus_eq_orbitLinearCodim` at `canonicalCoord
(foldDim L)`, `M = intervalDirectSum L`) into the conditional headline
`codimRepCanonical_orbitRankLocus_eq_multSum`, then fold the RHS back into `codimForm` via the
`rfl`-bridge `codimForm_multiplicityArray`. -/

/-- **Per-orbit geometric reading (ℤ form), UNCONDITIONAL.** For `M = ⊕_{(a,b)∈L} M_{ab}` the
geometric codimension of the orbit closure `Ō_M` (the rank locus, Thm 3.8 proved in
`Core.OrbitClosure`), read at the canonical flattening, equals the combinatorial Cor 3.5 form
`codimForm N (multiplicityArray L)`:
the combinatorial codimension form IS the geometric orbit-closure codimension, no longer modulo
`hVoigt`. From the discharged Voigt lemma + `codimRepCanonical_orbitRankLocus_eq_multSum` +
`codimForm_multiplicityArray`. -/
theorem codimRepCanonical_orbitRankLocus_eq_codimForm
    [IsAlgClosed k] [CharZero k] (L : List (Fin (N + 1) × Fin (N + 1))) :
    ((codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = codimForm N (multiplicityArray L) := by
  rw [codimForm_multiplicityArray]
  exact codimRepCanonical_orbitRankLocus_eq_multSum L
    (codimRep_orbitRankLocus_eq_orbitLinearCodim (intervalDirectSum (k := k) L))

/-- **Per-orbit geometric reading (ℕ∞ form), UNCONDITIONAL.** The genuine geometric codimension
`codimRepCanonical (orbitRankLocus (⊕L))` equals the expected codimension `orbitLinearCodim`, as an
`ℕ∞`. This is the discharged `hVoigt` at `M = intervalDirectSum L`; the `codimForm` reading is the
ℤ-cast `codimRepCanonical_orbitRankLocus_eq_codimForm`. -/
theorem codimRepCanonical_orbitRankLocus_eq_orbitLinearCodim
    [IsAlgClosed k] [CharZero k] (L : List (Fin (N + 1) × Fin (N + 1))) :
    codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) L))
      = (orbitLinearCodim (intervalDirectSum (k := k) L) : ℕ∞) :=
  codimRep_orbitRankLocus_eq_orbitLinearCodim (intervalDirectSum (k := k) L)

/-! ## Deliverable 2 — `cCodim` as the minimum of GEOMETRIC codimensions

`cCodim d r h` is the minimum of the combinatorial form `codimForm N (extendℤ m)` over the Kostant
partitions `m`. To read each summand geometrically we realise `m` as an interval list
`listOfPartition m` whose multiplicity array is `extendℤ m` (`multiplicityArray_listOfPartition`),
so by deliverable 1 the geometric codimension of the orbit closure of `⊕_{(a,b)} M_{ab}` equals
`codimForm N (extendℤ m)`. The minimum then transports (`Finset.inf'_congr`). -/

/-- The interval list realising a (triangle-supported) array `m`: each upper-triangular index `p`
(`p.1 ≤ p.2`) repeated `m p` times. Its multiplicity array is `extendℤ m`
(`multiplicityArray_listOfPartition`), so `⊕_{(a,b)} M_{ab}` over it is the orbit with
multiplicities `m`. -/
noncomputable def listOfPartition (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    List (Fin (N + 1) × Fin (N + 1)) :=
  ((Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ p.2)).toList).flatMap
    (fun p ↦ List.replicate (m p) p)

/-- The list `flatMap`-of-replicates evaluates a sum to the multiplicity-weighted sum of `g`:
`∑_{L flatMap replicate} g = ∑_{p ∈ L} m p · g p`. The combinatorial core of
`multiplicityArray_listOfPartition`. -/
theorem sum_flatMap_replicate_map {α : Type*} (g : α → ℤ) (m : α → ℕ) (L : List α) :
    (L.flatMap (fun a ↦ (List.replicate (m a) a).map g)).sum
      = (L.map (fun a ↦ (m a : ℤ) * g a)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons, List.map_replicate,
      List.sum_replicate, nsmul_eq_mul]

/-- **The list realises the array.** `multiplicityArray (listOfPartition m) = extendℤ m` for any
array `m`: the count of each upper-triangular index `(a,b)` in the list is `m (a,b)` (in the box,
on the triangle), and `0` off the triangle / box — matching `extendℤ m`. The partition↔list
correspondence behind deliverable 2. -/
theorem multiplicityArray_listOfPartition (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    multiplicityArray (listOfPartition m) = extendℤ m := by
  funext a b
  rw [multiplicityArray, listOfPartition, List.map_flatMap,
    sum_flatMap_replicate_map (fun p ↦ if a = (p.1 : ℤ) ∧ b = (p.2 : ℤ) then (1 : ℤ) else 0) m,
    Finset.sum_map_toList]
  simp only [mul_ite, mul_one, mul_zero]
  unfold extendℤ
  split_ifs with h
  · obtain ⟨ha0, hab, hbN⟩ := h
    rw [Finset.sum_eq_single (⟨a.toNat, by omega⟩, ⟨b.toNat, by omega⟩)]
    · rw [if_pos ⟨by simp; omega, by simp; omega⟩]
    · intro q _ hqne
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hqne (by ext <;> simp)
    · intro hbad
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simp only [Fin.le_def]; omega⟩) hbad
  · apply Finset.sum_eq_zero
    intro p hp
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    rw [Finset.mem_filter, Fin.le_def] at hp
    exact h ⟨by positivity, by exact_mod_cast hp.2,
      by have := p.2.isLt; exact_mod_cast Nat.lt_succ_iff.mp this⟩

/-- **Per-partition geometric reading, UNCONDITIONAL.** For a Kostant array `m`, the combinatorial
form `codimForm N (extendℤ m)` is the genuine geometric codimension of the orbit closure of
`⊕_{(a,b)} M_{ab}^{m}` (over `listOfPartition m`), read at the canonical flattening. The summand of
deliverable 2; deliverable 1 specialised through `multiplicityArray_listOfPartition`. -/
theorem codimForm_extendℤ_eq_geomCodim
    [IsAlgClosed k] [CharZero k] (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    codimForm N (extendℤ m)
      = ((codimRepCanonical
          (orbitRankLocus (intervalDirectSum (k := k) (listOfPartition m)))).toNat : ℤ) := by
  rw [codimRepCanonical_orbitRankLocus_eq_codimForm (k := k) (listOfPartition m),
    multiplicityArray_listOfPartition]

/-- **`C` is the minimum of GEOMETRIC codimensions, UNCONDITIONAL.** The combinatorial codimension
`cCodim d r` equals the minimum over the Kostant partitions `m` of `d` (corner `r`) of the genuine
**geometric** codimension of the orbit closure of `⊕_{(a,b)} M_{ab}^{m}` (the rank locus, Thm 3.8
proved in `Core.OrbitClosure`), read at the canonical flattening. The combinatorial `C` is the
smallest orbit-closure
codimension among the rank-`r` orbits — no longer modulo `hVoigt`. From `cCodim`'s definition +
`codimForm_extendℤ_eq_geomCodim` by `Finset.inf'_congr`. -/
theorem cCodim_eq_inf_geomCodim
    [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    cCodim d r h
      = (kostantPartitions d r).inf' h (fun m ↦
          ((codimRepCanonical
            (orbitRankLocus (intervalDirectSum (k := k) (listOfPartition m)))).toNat : ℤ)) :=
  Finset.inf'_congr h rfl (fun m _ ↦ codimForm_extendℤ_eq_geomCodim (k := k) m)

end DLNFibre.Core
