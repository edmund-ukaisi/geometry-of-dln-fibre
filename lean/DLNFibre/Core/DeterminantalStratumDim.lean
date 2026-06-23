import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.SigmaStratification

/-!
# `DLNFibre.Core.DeterminantalStratumDim` — the determinantal-stratum dimension (AG rung 1)

The variety dimension of the variety of `m × n` matrices of rank `≤ r`:

> `dim Mat^{rk ≤ r}_{m × n} = r · (n + m − r)`.

**The route — `N = 1` specialisation of the landed `voigt-discharge` engine (no new orbit map).**
For the equioriented type-A quiver with a single arrow (`N = 1`, dimension vector `d = ![n, m]`), a
`Tuple` is a *single* matrix `M : Mat_{m × n}` (`d 0 = n`, `d (last) = d 1 = m`), the group `G_d =
GL_m × GL_n` acts by `(P, Q) · M = P M Q⁻¹`, and the closed product-rank-`≤ r` locus
`productRankLocusLE ![n,m] r = {M | M.rank ≤ r}` **is** the classical rank-`≤ r` determinantal
variety. So the brick reduces to specialisations of LANDED results — the orbit-image dimension route
did NOT need a new `G_out`-on-`Mat` orbit map.

The four reused / new pieces:
1. **Primality** (irreducible): for `N = 1`, `productRankLocusLE ![n,m] r = orbitRankLocus M₀` for a
   rank-`r` realizer `M₀` (the only non-trivial rank constraint is the corner `(0,1)`; the diagonal
   patterns are always full), so its vanishing ideal is prime (LANDED
   `isPrime_vanishingIdeal_orbitRankLocus`).
2. **The codim value** (LANDED `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`, unconditional
   in char 0 + alg-closed): `codimRepCanonical (productRankLocusLE ![n,m] r) = cCodim ![n,m] r`.
3. **The combinatorial brick** (new, elementary `Finset`): for `N = 1` the Kostant-partition set is
   a singleton (`m_{00} = n−r`, `m_{01} = r`, `m_{11} = m−r`), so `cCodim ![n,m] r = (n−r)(m−r)`.
4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
   so `dim = m·n − (n−r)(m−r) = r(n + m − r)`.

**Witness:** `m = n = 2`, `r = 1` → `1 · (2 + 2 − 1) = 3` (the `example` at the foot of the file).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Module

universe u

variable {k : Type u} [Field k]

/-! ## The dimension vector and the single-matrix `Tuple` for `N = 1` -/

/-- The single-arrow dimension vector `d = ![n, m]` (`Fin 2 → ℕ`): source `d 0 = n`, target
`d 1 = d (last 1) = m`. A `Tuple (k := k) ![n,m]` is a single matrix `Mat_{m × n}`. -/
abbrev dStratum (n m : ℕ) : Fin 2 → ℕ := ![n, m]

/-- The unique Kostant partition of `![n,m]` with corner `r` (`r ≤ n`, `r ≤ m`): `m₀₀ = n − r` (the
`(0,0)` interval), `m₀₁ = r` (the corner `(0,1)`), `m₁₁ = m − r` (the `(1,1)` interval), `0` off the
upper triangle. -/
def stratumPartition (n m r : ℕ) : Fin 2 × Fin 2 → ℕ :=
  fun p ↦ if p = (0, 0) then n - r else if p = (0, 1) then r else if p = (1, 1) then m - r else 0

/-! ## Brick 3 — the combinatorial codimension at `N = 1` -/

/-- **The Kostant-partition set at `N = 1` is the singleton `{stratumPartition n m r}`** (for
`r ≤ n`, `r ≤ m`): vertex `0` forces `m₀₀ + m₀₁ = n`, vertex `1` forces `m₀₁ + m₁₁ = m`, the corner
forces `m₀₁ = r`, support forces `m₁₀ = 0`. -/
theorem kostantPartitions_stratum_eq (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    kostantPartitions (dStratum n m) r = {stratumPartition n m r} := by
  classical
  -- the `kostantAt` filtered sums, made explicit over `Fin 2 × Fin 2`.
  -- vertex 0 reads `(0,0) + (0,1)`; vertex 1 reads `(0,1) + (1,1)`.
  have hsum0 : ∀ f : Fin 2 × Fin 2 → ℕ,
      (∑ p ∈ Finset.univ.filter (fun p : Fin 2 × Fin 2 ↦ p.1 ≤ 0 ∧ (0 : Fin 2) ≤ p.2), f p)
        = f (0, 0) + f (0, 1) := by
    intro f
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    norm_num
  have hsum1 : ∀ f : Fin 2 × Fin 2 → ℕ,
      (∑ p ∈ Finset.univ.filter (fun p : Fin 2 × Fin 2 ↦ p.1 ≤ 1 ∧ (1 : Fin 2) ≤ p.2), f p)
        = f (0, 1) + f (1, 1) := by
    intro f
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    norm_num
  -- the two Kostant-vertex equations, for an arbitrary `f`, in literal-vertex form.
  have hkos0 : ∀ f : Fin 2 × Fin 2 → ℕ,
      kostantAt (dStratum n m) f 0 ↔ dStratum n m 0 = f (0, 0) + f (0, 1) := by
    intro f; rw [kostantAt, hsum0]
  have hkos1 : ∀ f : Fin 2 × Fin 2 → ℕ,
      kostantAt (dStratum n m) f 1 ↔ dStratum n m 1 = f (0, 1) + f (1, 1) := by
    intro f; rw [kostantAt, hsum1]
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · -- membership: `stratumPartition n m r` is a Kostant partition with corner `r`
    rw [mem_kostantPartitions]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- bound `m_p ≤ d p.1`
      intro p; fin_cases p <;> simp [stratumPartition, dStratum] <;> omega
    · -- support off the triangle
      intro p hp; fin_cases p <;> simp_all [stratumPartition] <;> omega
    · -- Kostant at each vertex
      intro k
      fin_cases k
      · rw [show (⟨0, by omega⟩ : Fin (1 + 1)) = 0 from rfl, hkos0]
        simp only [stratumPartition, dStratum]; norm_num; omega
      · rw [show (⟨1, by omega⟩ : Fin (1 + 1)) = 1 from rfl, hkos1]
        simp only [stratumPartition, dStratum]; norm_num; omega
    · -- corner
      simp [stratumPartition]
  · -- uniqueness
    intro f hf
    rw [mem_kostantPartitions] at hf
    obtain ⟨hbd, hsupp, hkos, hcorner⟩ := hf
    have e0 := (hkos0 f).mp (hkos 0)
    have e1 := (hkos1 f).mp (hkos 1)
    simp only [dStratum, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
    -- support: `f (1,0) = 0`
    have h10 : f (1, 0) = 0 := hsupp (1, 0) (by decide)
    -- assemble: `f = stratumPartition n m r`
    funext p
    fin_cases p <;>
      simp only [stratumPartition] <;>
      norm_num [show ((0 : Fin 2), Fin.last 1) = ((0 : Fin 2), (1 : Fin 2)) from rfl]
        at hcorner ⊢ <;>
      omega

/-- **Brick 3: `cCodim ![n,m] r = (n − r)(m − r)`.** `cCodim` is the `inf'` of `codimForm` over the
singleton Kostant set, and `codimForm 1 (extendℤ (stratumPartition n m r)) = m₀₀ · m₁₁ =
(n − r)(m − r)` (the single `(0,0)·(1,1)` term of the `N = 1` quadratic form). -/
theorem cCodim_stratum_eq (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m)
    (h : (kostantPartitions (dStratum n m) r).Nonempty) :
    cCodim (dStratum n m) r h = ((n - r) * (m - r) : ℕ) := by
  have hset := kostantPartitions_stratum_eq n m r hn hm
  -- `cCodim` is the `inf'` of `codimForm` over the singleton Kostant set.
  have hval : cCodim (dStratum n m) r h = codimForm 1 (extendℤ (stratumPartition n m r)) := by
    unfold cCodim
    refine le_antisymm ?_ ?_
    · exact Finset.inf'_le _ (by rw [hset]; exact Finset.mem_singleton_self _)
    · rw [Finset.le_inf'_iff]
      intro b hb
      rw [hset, Finset.mem_singleton] at hb
      rw [hb]
  rw [hval]
  -- evaluate `codimForm 1 (extendℤ (stratumPartition n m r))`: the single `(0,0)·(1,1)` term.
  rw [codimForm]
  -- `Icc 1 1 = {1}`, etc. — the quadruple sum collapses to one term `m(0)(0) · m(1)(1)`.
  norm_num [Finset.Icc_self, Finset.sum_singleton]
  -- the two `extendℤ` values: `(0,0) ↦ n−r`, `(1,1) ↦ m−r`
  rw [show extendℤ (stratumPartition n m r) 0 0 = ((n - r : ℕ) : ℤ) from by
        rw [extendℤ]; norm_num [stratumPartition],
    show extendℤ (stratumPartition n m r) 1 1 = ((m - r : ℕ) : ℤ) from by
        rw [extendℤ]; norm_num [stratumPartition]]

/-! ## Brick 1 — primality of the determinantal variety at `N = 1` -/

/-- The Kostant-partition set of `![n,m]` with corner `r` is nonempty (`r ≤ n`, `r ≤ m`): the
singleton `stratumPartition n m r`. -/
theorem kostantPartitions_stratum_nonempty (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    (kostantPartitions (dStratum n m) r).Nonempty := by
  rw [kostantPartitions_stratum_eq n m r hn hm]
  exact Finset.singleton_nonempty _

/-- **The determinantal variety is the rank locus of a realizer (N = 1).** There is a tuple
`M₀ : Tuple ![n,m]` (a single rank-`r` matrix) whose `orbitRankLocus` is exactly
`productRankLocusLE ![n,m] r` — the only binding rank constraint at `N = 1` is the corner. Carries
primality of the variety. -/
theorem exists_orbitRankLocus_eq_productRankLocusLE_stratum (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    ∃ M₀ : Tuple (k := k) (dStratum n m),
      orbitRankLocus M₀ = productRankLocusLE (k := k) (dStratum n m) r := by
  -- the realizer of the unique Kostant partition is a single rank-`r` matrix.
  have hmem : stratumPartition n m r ∈ kostantPartitions (dStratum n m) r := by
    rw [kostantPartitions_stratum_eq n m r hn hm]; exact Finset.mem_singleton_self _
  refine ⟨realizerD (k := k) hmem, ?_⟩
  set M₀ := realizerD (k := k) hmem with hM₀
  -- the realizer's corner is `r` (its full product has rank `r`)
  have hcorner : (mult (dStratum n m) M₀).rank = r := rank_mult_realizerD hmem
  -- `⊇` is the per-orbit inclusion (corner ≤ r); `⊆` is the diagonal-vacuity at `N = 1`.
  apply le_antisymm
  · exact orbitRankLocus_subset_productRankLocusLE (dStratum n m) (hcorner.le)
  · intro A hA
    rw [mem_productRankLocusLE] at hA
    -- the only binding constraint at `N = 1` is the corner `(0,1)`; the diagonals are vacuous.
    have h01 : ∀ h : (0 : Fin 2) ≤ 1,
        rankPattern (dStratum n m) A 0 1 h ≤ rankPattern (dStratum n m) M₀ 0 1 h := by
      intro h
      have hAc : rankPattern (dStratum n m) A 0 1 h = (mult (dStratum n m) A).rank :=
        corner_rankPattern_eq_rank (dStratum n m) A
      have hMc : rankPattern (dStratum n m) M₀ 0 1 h = (mult (dStratum n m) M₀).rank :=
        corner_rankPattern_eq_rank (dStratum n m) M₀
      rw [hAc, hMc, hcorner]; exact hA
    -- show `∀ i j (h : i ≤ j), rankPattern A i j h ≤ rankPattern M₀ i j h`
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp only [rankPattern_self]; exact le_refl _   -- (0,0): `d 0 ≤ d 0`
    · exact h01 (by decide)                            -- (0,1): the corner
    · exact absurd hij (by decide)                     -- (1,0): excluded by `i ≤ j`
    · simp only [rankPattern_self]; exact le_refl _   -- (1,1): `d 1 ≤ d 1`

/-- **Brick 1: the determinantal variety is irreducible (N = 1).** The vanishing ideal of (the
flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
orbit closure (LANDED `isPrime_vanishingIdeal_orbitRankLocus`). -/
theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
    (hn : r ≤ n) (hm : r ≤ m) :
    (vanishingIdeal k
        (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) :
      Ideal (MvPolynomial (RepCoord (dStratum n m)) k)).IsPrime := by
  obtain ⟨M₀, hM₀⟩ := exists_orbitRankLocus_eq_productRankLocusLE_stratum (k := k) n m r hn hm
  rw [← hM₀]
  exact isPrime_vanishingIdeal_orbitRankLocus M₀

/-! ## The ambient dimension `card (RepCoord ![n,m]) = m · n` -/

/-- `Nat.card (RepCoord ![n,m]) = m · n` (one coordinate per matrix entry of the single `m × n`
matrix). The single arrow `i = 0 : Fin 1` has `i.succ = 1`, `i.castSucc = 0`, so the fibre is
`Fin (![n,m] 1) × Fin (![n,m] 0) = Fin m × Fin n`. -/
theorem card_repCoord_stratum (n m : ℕ) :
    Nat.card (RepCoord (dStratum n m)) = m * n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp [dStratum, Fintype.card_prod, Fintype.card_fin]

/-! ## The headline — the determinantal-stratum dimension -/

/-- **The determinantal-stratum dimension (AG rung 1).** For `r ≤ n` and `r ≤ m`, over an
algebraically closed field of characteristic `0`, the variety dimension of the rank-`≤ r`
determinantal variety `Mat^{rk ≤ r}_{m × n}` (encoded as the `N = 1` product-rank locus
`productRankLocusLE ![n,m] r`) is

> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.

Proof: the catenary bridge `codim + dim = card = m·n` (primality, Brick 1) with the LANDED codim
`codim = cCodim ![n,m] r` (Brick 2) and its value `(n − r)(m − r)` (Brick 3), then
`m·n − (n − r)(m − r) = r(n + m − r)`. -/
theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
    (hn : r ≤ n) (hm : r ≤ m) :
    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
      = (r * (n + m - r) : ℕ) := by
  set Z := productRankLocusLE (k := k) (dStratum n m) r with hZ
  -- nonemptiness of the Kostant set + its codim value
  have hne := kostantPartitions_stratum_nonempty n m r hn hm
  -- catenary bridge: `codim + dim = card`
  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
    (isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm)
  -- the LANDED codim value `codim = cCodim = (n−r)(m−r)`
  have hcodim : codimRep (canonicalCoord (dStratum n m)) Z = (((n - r) * (m - r) : ℕ) : ℕ∞) := by
    have h1 : codimRepCanonical Z = ((cCodim (dStratum n m) r hne).toNat : ℕ∞) :=
      codimRepCanonical_productRankLocusLE_eq_cCodim_enat (dStratum n m) r hne
    rw [cCodim_stratum_eq n m r hn hm hne] at h1
    simpa [codimRepCanonical, hZ, Int.toNat_natCast] using h1
  -- the ambient dimension `card = m·n`
  have hcard : (Nat.card (RepCoord (dStratum n m)) : ℕ∞) = ((m * n : ℕ) : ℕ∞) := by
    rw [card_repCoord_stratum]
  rw [hcodim, hcard] at hbridge
  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
  -- arithmetic: `(n−r)(m−r) + r(n+m−r) = m·n` (over `ℕ`, with `r ≤ n`, `r ≤ m`)
  have harith : (n - r) * (m - r) + r * (n + m - r) = m * n := by
    obtain ⟨a, rfl⟩ := Nat.le.dest hn
    obtain ⟨b, rfl⟩ := Nat.le.dest hm
    simp only [Nat.add_sub_cancel_left]
    have : r + a + (r + b) - r = r + a + b := by omega
    rw [this]; ring
  -- so the two `ℕ∞` sums agree; cancel the finite left summand `(n−r)(m−r)`
  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
      = (((n - r) * (m - r) : ℕ) : ℕ∞) + ((r * (n + m - r) : ℕ) : ℕ∞) := by
    rw [hbridge, ← Nat.cast_add, harith]
  exact ((ENat.addLECancellable_coe ((n - r) * (m - r))).inj.mp heq)

/-! ## Non-vacuity witness — `2 × 2`, `r = 1` → `3` -/

/-- **Witness (`2 × 2`, `r = 1` → `3`).** The rank-`≤ 1` locus of `2 × 2` matrices has variety
dimension `1 · (2 + 2 − 1) = 3`. -/
example [IsAlgClosed k] [CharZero k] :
    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
      = (3 : ℕ) := by
  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end DLNFibre.Core
