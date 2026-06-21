import DLNFibre.Core.SigmaComponents

/-!
# `DLNFibre.Core.ThetaComponentCount` — the count `θ = numTop = #top-dim components` (Phase θ)

The COUNT half of the `θ` deliverable, building on G3 (components = maximal `Ō_M`,
`Core.SigmaComponents`), the combinatorial engine (`Core.CTheta`: `cCodim`, `numTop`,
`kostantPartitions`, `codimForm`) and the per-orbit geometric reading (`Core.CThetaGeometric`:
`cCodim_eq_inf_geomCodim`, `listOfPartition`). The headline:

> **`numTop d r = #{top-dimensional irreducible components of Σ̄^r}`** — the combinatorial
> minimiser-count `θ` equals the number of irreducible components of `Σ̄^r` of minimal codimension
> (the top-dimensional ones).

**The subtlety (thread 04).** A minimal-PRIME `Ō_M` (a component) need not have minimal CODIM;
components are the inclusion-maximal orbit closures. The **top-dimensional** components are the
min-codim ones among them. So the count is `numTop ↔ {components that are ALSO min-codim}`, not
↔ all components. `numTop d r` itself counts the **minimisers** of `codimForm` (one for `(2,2,2)`,
`r=0`), NOT the maximal partitions (three) — so it is exactly the top-dimensional component count.

**The bijection.** `m ↦ vanishingIdeal (Ō_{realizerD m})`, where `realizerD m` is the interval
direct sum `⊕_{(a,b)} M_{ab}^{m_{ab}}` realised over `d` (`foldDim (listOfPartition m) = d` for a
Kostant `m`). On the minimisers (`codimForm = cCodim`) this is a bijection onto the top-dimensional
minimal primes of `sigmaIdeal d r`. **Injectivity is unconditional** (the `diff/cumul` inversion:
distinct partitions ⟹ distinct rank patterns ⟹ distinct orbit closures ⟹ distinct vanishing ideals);
**`MapsTo` and `SurjOn` are gated** on two named corner-selection hypotheses (`hLowerBound`,
`hRecover` — `SurjOn` is exactly `hRecover`, the unbuilt Gabriel→Kostant recovery), discharged from
the pen-and-paper (★) certificate. So the unconditional built content is the realizer infrastructure
+ injectivity; the count headline is gated.

**Typeclass.** `[IsAlgClosed k] [CharZero k]` — inherited from the Voigt codim (the geometric reading
`codimRepCanonical = codimForm`) + the Nullstellensatz primality. **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal Finset

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The realizer of a Kostant partition over `d`

`listOfPartition m` (from `Core.CThetaGeometric`) has `multiplicityArray = extendℤ m`. Its interval
direct sum lives over `foldDim (listOfPartition m)`; for a Kostant partition `m` of `d` the dimension
equation forces `foldDim (listOfPartition m) = d`, so it transports to a tuple over `d`. -/

/-- The cumulative sum `cumul (extendℤ m) k k` is the Kostant filtered sum at vertex `k`:
`∑_{0≤a≤k, k≤b≤N} m_{ab} = ∑_{p : p.1 ≤ k ∧ k ≤ p.2} m p`. The diagonal cumul = Kostant sum bridge. -/
theorem cumul_extendℤ_diag (m : Fin (N + 1) × Fin (N + 1) → ℕ) (k : Fin (N + 1)) :
    cumul (N : ℤ) (extendℤ m) (k : ℤ) (k : ℤ)
      = (∑ p ∈ Finset.univ.filter (fun p : Fin (N + 1) × Fin (N + 1) ↦ p.1 ≤ k ∧ k ≤ p.2),
          m p : ℤ) := by
  rw [cumul_apply, ← Finset.sum_product']
  -- reindex the `Fin×Fin` filter to the ℤ-box `Icc 0 k ×ˢ Icc k N` via casts / `toNat`
  symm
  refine Finset.sum_bij'
    (fun (p : Fin (N + 1) × Fin (N + 1)) _ ↦ ((p.1 : ℤ), (p.2 : ℤ)))
    (fun (q : ℤ × ℤ) (hq : q ∈ Finset.Icc 0 (k : ℤ) ×ˢ Finset.Icc (k : ℤ) (N : ℤ)) ↦
      ((⟨q.1.toNat, by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
          have := k.isLt; omega⟩ : Fin (N + 1)),
       (⟨q.2.toNat, by
          rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
          omega⟩ : Fin (N + 1))))
    ?_ ?_ ?_ ?_ ?_
  · -- forward maps into the box
    rintro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, h1, h2⟩ := hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨by positivity, by exact_mod_cast Fin.le_def.mp h1⟩,
      ⟨by exact_mod_cast Fin.le_def.mp h2, by exact_mod_cast Nat.lt_succ_iff.mp p.2.isLt⟩⟩
  · -- inverse maps into the filter
    rintro q hq
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Fin.le_def]; simp only; omega
    · rw [Fin.le_def]; simp only; omega
  · -- left inverse
    rintro p hp; ext <;> simp
  · -- right inverse
    rintro q hq
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    refine Prod.ext ?_ ?_ <;> simp only <;> omega
  · -- value match: `extendℤ m` on the box is `m`
    rintro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, h1, h2⟩ := hp
    simp only
    rw [extendℤ, dif_pos ⟨by positivity, by exact_mod_cast (h1.trans h2),
      by exact_mod_cast Nat.lt_succ_iff.mp p.2.isLt⟩]
    norm_num

/-- **`foldDim (listOfPartition m) = d` for a Kostant partition.** The diagonal rank pattern of the
realizer is `cumul (extendℤ m) k k = ∑_{i≤k≤j} m_{ij} = d k` (the Kostant equation), and the diagonal
rank pattern is `foldDim`. So the realizer's dimension vector is `d`. -/
theorem foldDim_listOfPartition_eq {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    foldDim (listOfPartition m) = d := by
  have hk := (mem_kostantPartitions.mp hm).2.2.1
  funext t
  -- `foldDim t = r_{tt}(⊕L) = cumul (mult.Array L) t t = cumul (extendℤ m) t t = ∑ filter = d t`
  have hZ : (foldDim (listOfPartition m) t : ℤ) = (d t : ℤ) := by
    have hself : (foldDim (listOfPartition m) t : ℤ)
        = (rankPattern (foldDim (listOfPartition m))
            (intervalDirectSum (k := ℚ) (listOfPartition m)) t t le_rfl : ℤ) := by
      rw [rankPattern_self]
    rw [hself, rankPattern_intervalDirectSum_eq_cumul, multiplicityArray_listOfPartition,
      cumul_extendℤ_diag, ← Nat.cast_sum, ← hk t]
  exact_mod_cast hZ

/-- The **realizer over `d`** of a Kostant partition `m`: the interval direct sum
`⊕_{(a,b)} M_{ab}^{m_{ab}}` (over `listOfPartition m`), transported onto `d`. -/
noncomputable def realizerD {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    Tuple (k := k) d :=
  foldDim_listOfPartition_eq hm ▸ intervalDirectSum (k := k) (listOfPartition m)

/-- The realizer's rank pattern is `cumul (extendℤ m)` on the upper triangle. From
`rankPattern_intervalDirectSum_eq_cumul` + `multiplicityArray_listOfPartition`, through transport. -/
theorem rankPattern_realizerD {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    (rankPattern d (realizerD (k := k) hm) i j hij : ℤ)
      = cumul (N : ℤ) (extendℤ m) (i : ℤ) (j : ℤ) := by
  rw [realizerD, rankPattern_transport (foldDim_listOfPartition_eq hm)
      (intervalDirectSum (k := k) (listOfPartition m)),
    rankPattern_intervalDirectSum_eq_cumul, multiplicityArray_listOfPartition]

/-- Transporting a tuple along a dimension-vector equality preserves the geometric codimension of its
orbit closure: `subst` identifies the two coordinate rings. The bridge that reads the LANDED
`⊕L`-codimension off the realizer over `d`. -/
theorem codimRepCanonical_orbitRankLocus_transport {d₀ d : Fin (N + 1) → ℕ} (h : d₀ = d)
    (X : Tuple (k := k) d₀) :
    codimRepCanonical (orbitRankLocus (h ▸ X)) = codimRepCanonical (orbitRankLocus X) := by
  subst h; rfl

/-- The realizer's orbit closure codimension equals that of the bare interval direct sum (transport
along `foldDim (listOfPartition m) = d`): the `codimRepCanonical`-preserving identification used to
read off `codimForm`. -/
theorem orbitRankLocus_realizerD_eq {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    codimRepCanonical (orbitRankLocus (realizerD (k := k) hm))
      = codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) (listOfPartition m))) := by
  rw [realizerD, codimRepCanonical_orbitRankLocus_transport]

/-- **The realizer's corner is `r`** (so it lies in the corner-`≤ r` family): the corner rank pattern
is `cumul (extendℤ m) 0 N = m (0, last N) = r`, and the corner is `(mult).rank`. -/
theorem rank_mult_realizerD {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    (mult d (realizerD (k := k) hm)).rank = r := by
  have hcorner : m (0, Fin.last N) = r := (mem_kostantPartitions.mp hm).2.2.2
  -- `(mult).rank = r_{0N} = cumul (extendℤ m) 0 N = m_{0N} = r`
  have hZ : ((mult d (realizerD (k := k) hm)).rank : ℤ) = (r : ℤ) := by
    rw [← corner_rankPattern_eq_rank d (realizerD (k := k) hm),
      rankPattern_realizerD hm 0 (Fin.last N) (Fin.zero_le _)]
    -- `cumul (extendℤ m) 0 N = extendℤ m 0 N = m (0, last N) = r`
    rw [cumul_apply, Fin.val_zero, Fin.val_last]
    norm_num only [Finset.Icc_self, Finset.sum_singleton]
    rw [extendℤ, dif_pos ⟨le_rfl, by positivity, le_rfl⟩]
    have h0 : (⟨(0 : ℤ).toNat, by omega⟩ : Fin (N + 1)) = 0 := by ext; simp
    have hN : (⟨(N : ℤ).toNat, by omega⟩ : Fin (N + 1)) = Fin.last N := by
      ext; simp [Fin.val_last]
    rw [h0, hN, hcorner]
  exact_mod_cast hZ

/-- **The realizer's geometric codim is `codimForm`.** `codimRepCanonical (Ō_{realizerD m})` has
`.toNat = codimForm N (extendℤ m)` — the per-partition geometric reading transported to the
realizer over `d`. -/
theorem codimRepCanonical_orbitRankLocus_realizerD [IsAlgClosed k] [CharZero k]
    {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    ((codimRepCanonical (orbitRankLocus (realizerD (k := k) hm))).toNat : ℤ)
      = codimForm N (extendℤ m) := by
  rw [orbitRankLocus_realizerD_eq hm, codimRepCanonical_orbitRankLocus_eq_codimForm,
    multiplicityArray_listOfPartition]

/-! ## The top-dimensional components and the count headline -/

/-- The **orbit ideal of a Kostant partition** as a *total* map on arrays (so it is a plain function
the count-bijection ranges over): for `m ∈ kostantPartitions d r` it is `vanishingIdeal (Ō_{realizerD
m})`, a member of the corner-`≤ r` family `orbitIdeals d r`; off the Kostant set it is `⊥`
(irrelevant — the bijection's domain is the minimising Kostant partitions). -/
noncomputable def partitionIdeal (d : Fin (N + 1) → ℕ) (r : ℕ)
    (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    Ideal (MvPolynomial (RepCoord d) k) :=
  if hm : m ∈ kostantPartitions d r then
    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
      (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm))
  else ⊥

/-- On a Kostant partition, `partitionIdeal` is the orbit ideal of the realizer over `d`. -/
theorem partitionIdeal_of_mem {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    partitionIdeal (k := k) d r m
      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm)) := by
  rw [partitionIdeal, dif_pos hm]

/-! ## Injectivity bricks — distinct partitions give distinct orbit ideals

`extendℤ m` is a supported array (zero off the box `0 ≤ a ≤ b ≤ N`), so it is `diff`-recovered from
its `cumul`. The realizer's rank pattern is `cumul (extendℤ m)` on the triangle, so equal orbit
closures (equal vanishing ideals) force equal rank patterns there, hence equal `cumul`, hence
(via `diff_cumul`) equal `extendℤ`, hence equal partitions. -/

/-- `extendℤ m` is a supported array: it vanishes for `a < 0` and for `b > N` (built into its
`dite` guard). -/
theorem extendℤ_supported (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    Supported (N : ℤ) (extendℤ m) := by
  refine ⟨fun a b ha ↦ ?_, fun a b hb ↦ ?_⟩ <;>
    · rw [extendℤ, dif_neg]; rintro ⟨h1, h2, h3⟩; omega

/-- On a triangle index `(i, j)` with `i ≤ j`, `extendℤ m (i : ℤ) (j : ℤ) = m (i, j)`. -/
theorem extendℤ_apply_fin {m : Fin (N + 1) × Fin (N + 1) → ℕ} {i j : Fin (N + 1)} (hij : i ≤ j) :
    extendℤ m (i : ℤ) (j : ℤ) = (m (i, j) : ℤ) := by
  have hguard : (0 : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ (N : ℤ) :=
    ⟨by positivity, by exact_mod_cast Fin.le_def.mp hij,
      by exact_mod_cast Nat.lt_succ_iff.mp j.isLt⟩
  rw [extendℤ, dif_pos hguard]
  have hi : (⟨((i : ℤ)).toNat, by omega⟩ : Fin (N + 1)) = i := by ext; simp
  have hj : (⟨((j : ℤ)).toNat, by omega⟩ : Fin (N + 1)) = j := by ext; simp
  rw [hi, hj]

/-- **`extendℤ` is injective on Kostant partitions.** If `extendℤ m₁ = extendℤ m₂` then `m₁ = m₂`:
on the triangle the value is `m_{ij}` (`extendℤ_apply_fin`); off the triangle both partitions
vanish (`mem_kostantPartitions`). -/
theorem extendℤ_injOn_kostant {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m₁ m₂ : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm₁ : m₁ ∈ kostantPartitions d r) (hm₂ : m₂ ∈ kostantPartitions d r)
    (heq : extendℤ m₁ = extendℤ m₂) : m₁ = m₂ := by
  funext p
  by_cases hp : p.1 ≤ p.2
  · have h := congrFun (congrFun heq (p.1 : ℤ)) (p.2 : ℤ)
    rw [show p = (p.1, p.2) from rfl, extendℤ_apply_fin hp, extendℤ_apply_fin hp] at h
    exact_mod_cast h
  · rw [(mem_kostantPartitions.mp hm₁).2.1 p hp, (mem_kostantPartitions.mp hm₂).2.1 p hp]

/-- **The realizer determines its partition.** If the realizers of two minimising Kostant partitions
have the same rank pattern on the triangle, the partitions are equal — the `diff/cumul` inversion:
`extendℤ mᵢ = diff (cumul (extendℤ mᵢ))`, and `cumul (extendℤ mᵢ)` is the realizer's rank pattern on
the triangle, so equal there forces `extendℤ` equal (all four `diff` reference points stay on the
triangle), hence the partitions agree. -/
theorem partition_eq_of_rankPattern_realizerD_eq {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m₁ m₂ : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm₁ : m₁ ∈ kostantPartitions d r) (hm₂ : m₂ ∈ kostantPartitions d r)
    (hrank : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d (realizerD (k := k) hm₁) i j hij
        = rankPattern d (realizerD (k := k) hm₂) i j hij) :
    m₁ = m₂ := by
  refine extendℤ_injOn_kostant hm₁ hm₂ ?_
  -- the cumuls agree on the triangle (each is a realizer rank pattern, equal by `hrank`)
  have hcum : ∀ x y : ℤ, x ≤ y → 0 ≤ x → y ≤ (N : ℤ) →
      cumul (N : ℤ) (extendℤ m₁) x y = cumul (N : ℤ) (extendℤ m₂) x y := by
    intro x y hxy hx hy
    obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), (i : ℤ) = x := ⟨⟨x.toNat, by omega⟩, by simp; omega⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), (j : ℤ) = y := ⟨⟨y.toNat, by omega⟩, by simp; omega⟩
    have hij : i ≤ j := by rw [Fin.le_def]; omega
    subst hi hj
    rw [← rankPattern_realizerD (k := k) hm₁ i j hij, ← rankPattern_realizerD (k := k) hm₂ i j hij,
      hrank i j hij]
  funext a b
  -- on the triangle `a ≤ b` the four `diff` reference points are all triangle/box points;
  -- off it both partitions vanish (off-triangle support)
  rcases le_or_gt a b with hab | hab
  · -- `extendℤ mᵢ a b = diff (cumul (extendℤ mᵢ)) a b`, four reference points agree via `hcum`
    rw [← diff_cumul (N : ℤ) (extendℤ m₁) (extendℤ_supported m₁).1 (extendℤ_supported m₁).2,
      ← diff_cumul (N : ℤ) (extendℤ m₂) (extendℤ_supported m₂).1 (extendℤ_supported m₂).2,
      diff_apply, diff_apply]
    -- the four points `(a,b),(a,b+1),(a-1,b),(a-1,b+1)`: handle in/out of box uniformly via `hcum`
    -- and the support of `cumul` (vanishing for `b+1 > N` etc. cancels symmetrically)
    have key : ∀ x y : ℤ, x ≤ y →
        cumul (N : ℤ) (extendℤ m₁) x y = cumul (N : ℤ) (extendℤ m₂) x y := by
      intro x y hxy
      rcases lt_or_ge x 0 with hx | hx
      · rw [(supported_cumul (N : ℤ) (extendℤ m₁)).1 x y hx,
          (supported_cumul (N : ℤ) (extendℤ m₂)).1 x y hx]
      rcases lt_or_ge (N : ℤ) y with hy | hy
      · rw [(supported_cumul (N : ℤ) (extendℤ m₁)).2 x y hy,
          (supported_cumul (N : ℤ) (extendℤ m₂)).2 x y hy]
      · exact hcum x y hxy hx hy
    rw [key a b hab, key a (b + 1) (by omega), key (a - 1) b (by omega),
      key (a - 1) (b + 1) (by omega)]
  · -- below the diagonal: both `extendℤ` are `0`
    rw [extendℤ, dif_neg, extendℤ, dif_neg] <;> rintro ⟨_, h2, _⟩ <;> omega

/-- The **top-dimensional components** of `Σ̄^r`: the minimal primes of `sigmaIdeal d r` (the
irreducible components, G3) whose height equals the combinatorial constant `cCodim d r h`. That this
constant IS the minimal codimension among the components (so the predicate genuinely selects the
top-dimensional ones) is the content delivered by the gating hypotheses `hLowerBound`/`hRecover` of
`bijOn_partitionIdeal_topComponents_of`, not asserted here: `cCodim` is a fixed combinatorial integer
(the min over corner-`r` *orbits*), independent of the minimal primes, so this is a genuine Spec-side
subset, not an alias of the bijection's image. -/
def topComponents [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    Set (Ideal (MvPolynomial (RepCoord d) k)) :=
  {p | p ∈ (sigmaIdeal (k := k) d r).minimalPrimes ∧ p.height = (cCodim d r h).toNat}

/-- The **minimising Kostant partitions**: those attaining the minimum `codimForm = cCodim`. Their
count is `numTop d r h`, and they index the top-dimensional components. -/
noncomputable def minimisingPartitions (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) : Finset (Fin (N + 1) × Fin (N + 1) → ℕ) :=
  (kostantPartitions d r).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d r h)

/-- `numTop d r h` is the cardinality of `minimisingPartitions` (definitional unfold of `numTop`). -/
theorem numTop_eq_card_minimising (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    numTop d r h = (minimisingPartitions d r h).card := rfl

/-! ## The count-bijection

The bijection rests on two facts about the corner-`≤ r` family, both pen-and-paper certified
(Lehalleur–Rimányi Cor 4.2(b) / the rank-shift Lemma 4.5; expedition thread 05) but NOT yet built in
`Core` — supplied here as the named hypotheses `hLowerBound` and `hRecover`:

* **`hLowerBound`** — the realizer of a *minimising* corner-`r` partition is of **globally minimal**
  codimension over the whole corner-`≤ r` family (not merely the corner-`r` orbits): every
  corner-`≤ r` orbit closure has codimension `≥ cCodim d r`. The content is the **strict
  corner-monotonicity** `cCodim d r < cCodim d s` for `s < r` (a corner-`s` orbit, `s < r`, has
  strictly larger codimension) plus the Gabriel reading `codimRep(Ō_{M'}) = codimForm`. This is what
  the landed `orbitRankLocus_minCodim_mem_minimalPrimes` quantifier `∀ corner-≤r M'` needs.
* **`hRecover`** — every top-dimensional component is the orbit ideal of *some corner-`r`*
  Kostant-partition realizer (membership in the full `kostantPartitions d r`, NOT pre-assumed
  minimising — the minimising property is *derived* here from the top-dimensional height). The content
  is the Gabriel normal form (`exists_orbitRankLocus_mem_rankPattern_eq` / `baseChange_normalForm`)
  recast as a corner-`r` Kostant partition (the `kostantArrayOfRank`/`CMPlus` recovery of
  `Core.OrbitKostant`, bridged to the `extendℤ` encoding), with corner-monotonicity forcing the corner
  to be exactly `r` on a top-dimensional component. Phrasing it as `∈ kostantPartitions d r` (not
  `∈ minimisingPartitions`) keeps it the genuine recovery brick, not a restatement of `SurjOn`. -/

/-- **The count-bijection, gated on the corner-selection facts.** Under `hLowerBound` (every
corner-`≤ r` orbit has codim `≥ cCodim`, so a minimising realizer is globally min-codim) and
`hRecover` (every top component is *some* corner-`r` realizer), the map `m ↦ partitionIdeal m` is a
bijection from the minimising Kostant partitions (counted by `numTop`) onto the top-dimensional
components of `Σ̄^r`. The injectivity is unconditional (`partition_eq_of_rankPattern_realizerD_eq`);
the minimising property in `SurjOn` is *derived* from the top-dimensional height, not assumed. -/
theorem bijOn_partitionIdeal_topComponents_of [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (hLowerBound : ∀ M' : Tuple (k := k) d, (mult d M').rank ≤ r →
      ((cCodim d r h).toNat : ℕ∞) ≤ codimRepCanonical (orbitRankLocus M'))
    (hRecover : ∀ p ∈ topComponents (k := k) d r h,
      ∃ m ∈ kostantPartitions d r, partitionIdeal (k := k) d r m = p) :
    Set.BijOn (partitionIdeal (k := k) d r)
      ↑(minimisingPartitions d r h)
      (topComponents (k := k) d r h) := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo: a minimiser maps to a top-dimensional component
    rintro m hm
    rw [Finset.mem_coe, minimisingPartitions, Finset.mem_filter] at hm
    obtain ⟨hmem, hmin⟩ := hm
    rw [partitionIdeal_of_mem hmem]
    -- the realizer's codim is `codimForm = cCodim`; min over the family ⟹ minimal prime + top-dim
    have hcodim : ((codimRepCanonical (orbitRankLocus (realizerD (k := k) hmem))).toNat : ℤ)
        = cCodim d r h := by rw [codimRepCanonical_orbitRankLocus_realizerD hmem, hmin]
    have hfin : codimRepCanonical (orbitRankLocus (realizerD (k := k) hmem)) ≠ ⊤ := by
      rw [codimRepCanonical_orbitRankLocus_eq_height]
      exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
    -- `codimRep = (cCodim.toNat : ℕ∞)` (finite height)
    have hcodimE : codimRepCanonical (orbitRankLocus (realizerD (k := k) hmem))
        = ((cCodim d r h).toNat : ℕ∞) := by
      rw [← ENat.coe_toNat hfin]
      congr 1
      omega
    refine ⟨?_, ?_⟩
    · -- minimal prime: the global lower bound makes the realizer min-codim over the family
      refine orbitRankLocus_minCodim_mem_minimalPrimes d r (realizerD (k := k) hmem)
        (by rw [rank_mult_realizerD hmem]) (fun M' hM' ↦ ?_)
      rw [hcodimE]; exact hLowerBound M' hM'
    · -- top-dimensional: height = cCodim.toNat
      rw [← codimRepCanonical_orbitRankLocus_eq_height, hcodimE]
  · -- InjOn: distinct minimisers give distinct ideals (unconditional)
    rintro m₁ hm₁ m₂ hm₂ heq
    rw [Finset.mem_coe, minimisingPartitions, Finset.mem_filter] at hm₁ hm₂
    rw [partitionIdeal_of_mem hm₁.1, partitionIdeal_of_mem hm₂.1] at heq
    -- equal vanishing ideals ⟹ equal flattened closures ⟹ equal rank patterns ⟹ equal partitions
    have hle₁ := le_of_eq heq
    have hle₂ := le_of_eq heq.symm
    rw [vanishingIdeal_orbitRankLocus_le_iff] at hle₁ hle₂
    have hsets : canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm₁.1)
        = canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm₂.1) :=
      le_antisymm hle₂ hle₁
    have hloc : orbitRankLocus (realizerD (k := k) hm₁.1)
        = orbitRankLocus (realizerD (k := k) hm₂.1) :=
      (canonicalCoord d).injective.image_injective hsets
    refine partition_eq_of_rankPattern_realizerD_eq (k := k) hm₁.1 hm₂.1 (fun i j hij ↦ ?_)
    -- `M ∈ Ō_M = Ō_M'` gives `rankPattern M ≤ rankPattern M'`, both ways ⟹ equal
    have h1 : realizerD (k := k) hm₁.1 ∈ orbitRankLocus (realizerD (k := k) hm₂.1) := by
      rw [← hloc]; exact self_mem_orbitRankLocus _
    have h2 : realizerD (k := k) hm₂.1 ∈ orbitRankLocus (realizerD (k := k) hm₁.1) := by
      rw [hloc]; exact self_mem_orbitRankLocus _
    exact le_antisymm (h1 i j hij) (h2 i j hij)
  · -- SurjOn: `hRecover` gives a corner-`r` partition; the top-dim height forces it minimising
    rintro p hp
    obtain ⟨m, hm, rfl⟩ := hRecover p hp
    refine ⟨m, ?_, rfl⟩
    rw [Finset.mem_coe, minimisingPartitions, Finset.mem_filter]
    refine ⟨hm, ?_⟩
    -- `codimForm(extendℤ m) = codimRep(Ō_{realizerD m}).toNat = p.height.toNat = cCodim.toNat`,
    -- and both `codimForm` and `cCodim` are `≥ 0`, so they are equal as `ℤ`.
    have hpheight : (partitionIdeal (k := k) d r m).height = ((cCodim d r h).toNat : ℕ∞) := hp.2
    rw [partitionIdeal_of_mem hm, ← codimRepCanonical_orbitRankLocus_eq_height] at hpheight
    have hval : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm))
        = ((cCodim d r h).toNat : ℕ∞) := hpheight
    have hcf : codimForm N (extendℤ m) = ((cCodim d r h).toNat : ℤ) := by
      rw [← codimRepCanonical_orbitRankLocus_realizerD (k := k) hm, hval, ENat.toNat_coe]
    -- `cCodim ≥ 0` (a min of `codimForm`-values, each a `ℕ`-cast), so `cCodim.toNat = cCodim`
    have hcCodim_nonneg : 0 ≤ cCodim d r h := by
      rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
      exact fun m' _ ↦ Int.natCast_nonneg _
    omega

/-- **θ-count headline (gated).** `numTop d r = #{top-dimensional irreducible components of Σ̄^r}`:
the combinatorial minimiser-count equals the number of minimal-codimension irreducible components,
under the corner-selection facts `hLowerBound`/`hRecover` (see `bijOn_partitionIdeal_topComponents_of`).
The two hypotheses are pen-and-paper certified ((★): a corner-`s` orbit with `s < r` has strictly
larger codimension, so the min-codim components sit at corner `r`; expedition thread 05) and reduce to
two unbuilt `Core` lemmas — the corner-monotonicity of `cCodim` and the Gabriel-normal-form recovery
of a corner-`r` Kostant partition — recorded in the module roadmap. The realizer infrastructure and
the bijection's **injectivity** are proved unconditionally; `MapsTo`/`SurjOn` are reduced to
`hLowerBound`/`hRecover`. -/
theorem numTop_eq_ncard_topComponents_of [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (hLowerBound : ∀ M' : Tuple (k := k) d, (mult d M').rank ≤ r →
      ((cCodim d r h).toNat : ℕ∞) ≤ codimRepCanonical (orbitRankLocus M'))
    (hRecover : ∀ p ∈ topComponents (k := k) d r h,
      ∃ m ∈ kostantPartitions d r, partitionIdeal (k := k) d r m = p) :
    numTop d r h = (topComponents (k := k) d r h).ncard := by
  rw [numTop_eq_card_minimising, ← Set.ncard_coe_finset,
    (bijOn_partitionIdeal_topComponents_of (k := k) d r h hLowerBound hRecover).ncard_eq]

section Witness

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 0`, over `AlgebraicClosure ℚ`

The `(2,2,2)` zero-product locus `Σ̄^0` (`[IsAlgClosed] [CharZero]`). The minimiser `mMin`
(`Core.CTheta`, the `(1,1)`-orbit, `codimForm = 3 = cCodim`) is in `minimisingPartitions`, and its
`partitionIdeal` is the orbit ideal of the realizer over `d` — a member of the corner-`0` family
`orbitIdeals d222 0`. The injectivity half of the bijection (unconditional) and the realizer
machinery fire on this concrete partition. The geometric side of the LANDED combinatorial
`numTop_d222_zero = 1`: one minimising partition ⟹ one top-dimensional component. -/

/-- The `(2,2,2)`, `r = 0` minimiser `mMin` lies in `minimisingPartitions` (it attains
`codimForm = cCodim = 3`, `Core.CTheta`): the bijection's domain is nonempty on `(2,2,2)`. -/
theorem mMin_mem_minimisingPartitions :
    mMin ∈ minimisingPartitions d222 0 kostantPartitions_d222_nonempty := by
  rw [minimisingPartitions, Finset.mem_filter]
  refine ⟨mMin_mem, ?_⟩
  rw [cCodim_d222_zero]
  decide +kernel

/-- The realizer of `mMin` over `(2,2,2)` is well-defined and its orbit ideal
(`partitionIdeal d222 0 mMin`) is the corresponding member of the corner-`0` family `orbitIdeals
d222 0` — the count-bijection's map fires on the concrete minimiser. -/
theorem partitionIdeal_mMin_mem_orbitIdeals :
    partitionIdeal (k := AlgebraicClosure ℚ) d222 0 mMin
      ∈ orbitIdeals (k := AlgebraicClosure ℚ) d222 0 := by
  rw [partitionIdeal_of_mem mMin_mem]
  exact ⟨realizerD (k := AlgebraicClosure ℚ) mMin_mem,
    (rank_mult_realizerD mMin_mem).le, rfl⟩

end Witness

end DLNFibre.Core
