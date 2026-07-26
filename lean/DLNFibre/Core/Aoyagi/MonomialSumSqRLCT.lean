import DLNFibre.Core.Aoyagi.MonomialRLCT
import DLNFibre.Core.Analysis.RLCT.SumSq

/-!
# `Core.Aoyagi.MonomialSumSqRLCT` — the monomial × sum-of-squares product RLCT engine

The value read-off for the **over-vanishing** (3,3,4) leaves. Unlike the clean-144 single-survivor
path (a divisibility CHAIN, `monomialSumSq_integrableAtFilter_of_lt`), the over-vanishing loss
pulls back to a monomial-squared times a NONDEGENERATE sum-of-squares in a DISJOINT block of
`jac`-free coordinates:

`loss ∘ g_c ≥ vm(u)² · ∑_{j ∈ Z} u_j²`   (`vm = ∏_d u_d^{a_d}`, `Z` = the 8 reg-seq coords).

The chain engine is DEAD here: it collapses `∑ bₖ²` to `b_{k₀}²·U` (`U ≥ 1` a UNIT, used as an
UPPER bound `U^{-c} ≤ M`), so it captures only `monomialThreshold(b_{k₀}) = ½` (`jac`-0 on `vm`'s
binding axes) — it discards the sum-of-squares vanishing. The honest value is the PRODUCT threshold

`min( monomialThreshold(vm², jac) , |Z| / 2 )`

— the `|Z|/2` (`= r/2`) comes from the nondegenerate `∑_{j∈Z} u_j²` (`RLCT.SumSq`, `rlctAt_sumSq`),
and it is invisible to the chain engine. Because `Z` is disjoint from `supp(vm) = supp(jac)` and
carries `jac = 0`, the weighted box integral FACTORS over the two coordinate blocks (Tonelli through
`MeasurableEquiv.piEquivPiSubtypeProd`): the `Z`-block gives the sum-of-squares threshold `|Z|/2`,
the complement gives the pure-power monomial threshold. The chart `unit`
(`|det Dg| = jacWeight·|unit|`) COUPLES the two blocks and does NOT factor — for the convergence
(`≥`) direction it is bounded by its `sup` on a compact neighbourhood (elder amendment A), so the
factorization is applied only to the unit-free integrand.

**Direction warning (do not re-derive the naive way).** The toric-LP over the term-ideal
`M = ⟨all monomials of all generators⟩ ⊇ I = ⟨gᵢ⟩` is an UPPER bound on the true RLCT, not a lower
bound: SoS-RLCT is monotone INCREASING under ideal inclusion (`I ⊆ M ⟹ ∑_M h² ≥ ∑_I h²` pointwise
`⟹ rlct(I) ≤ rlct(M)` — more generators = larger sum = less singular = larger RLCT; equality iff `I`
is already monomial, the clean leaves). So the honest over-vanishing LOWER bound is THIS
regular-sequence / sum-of-squares engine, never the toric-LP.

## Scope (honest)
- IN: the network-free product-germ integrability at an arbitrary base point `p`
  (`monoSumSq_integrableAtFilter_of_lt`), the ≥-direction the V-lower wire consumes; plus the
  null-zero guard + measurability the domination leg
  (`wLocalAdmissibleExponents_subset_of_eventually_le`) needs.
- OUT: the two-sided `rlctAt … = min` equality (the `≤` half needs the unit `inf > 0`
  marginalization); the DLN instantiation (the over-vanishing pullback identity
  `loss ∘ gFin c = vm²·∑vf²`, the regular-sequence `Ψ` straightening, the cover) — the
  `DLN.Aoyagi` over-vanishing seat.

## Status
SPECIFY skeleton: the germ + its null-zero/measurability/nonneg facts are PROVED sorry-free; the
main weighted integrability engine `monoSumSq_integrableAtFilter_of_lt` is STATEMENT-LOCKED with the
disjoint-block Tonelli finiteness the one tracked hole (`-- map: ov-sos-tonelli`).
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- **The monomial × sum-of-squares product germ.** `(∏_d u_d^{a_d})² · ∑_{j ∈ Z} (u_j)²`: the
over-vanishing loss lower bound (monomial `vm = ∏_d u_d^{a_d}` squared, times the nondegenerate
sum-of-squares over the regular-sequence coordinate block `Z`). -/
noncomputable def monoSumSqGerm (a : Fin D → ℕ) (Z : Finset (Fin D)) : (Fin D → ℝ) → ℝ :=
  fun u ↦ (∏ d, (u d) ^ (a d)) ^ 2 * ∑ j ∈ Z, (u j) ^ 2

/-- The product germ is nonnegative. -/
theorem monoSumSqGerm_nonneg (a : Fin D → ℕ) (Z : Finset (Fin D)) (u : Fin D → ℝ) :
    0 ≤ monoSumSqGerm a Z u := by
  unfold monoSumSqGerm
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)

/-- The product germ is measurable (a polynomial in the coordinates). -/
theorem measurable_monoSumSqGerm (a : Fin D → ℕ) (Z : Finset (Fin D)) :
    Measurable (monoSumSqGerm a Z) := by
  unfold monoSumSqGerm
  fun_prop

/-- **The zero set of the product germ is null** (given `Z` nonempty): `monoSumSqGerm a Z u = 0`
forces `∏ u_d^{a_d} = 0` (some binding `u_d = 0`) or `∑_{Z} u_j² = 0` (every `u_j = 0`, `j ∈ Z`) —
either way SOME coordinate vanishes, so the zero set sits inside the finite union of coordinate
hyperplanes `⋃_d {u_d = 0}`, which is null. This is the `LocallyNullZeros` guard the domination leg
(`wLocalAdmissibleExponents_subset_of_eventually_le`) needs. -/
theorem locallyNullZeros_monoSumSqGerm (a : Fin D → ℕ) {Z : Finset (Fin D)} (hZ : Z.Nonempty)
    (p : Fin D → ℝ) : LocallyNullZeros (monoSumSqGerm a Z) p := by
  classical
  obtain ⟨j₀, hj₀⟩ := hZ
  -- each coordinate hyperplane is null.
  have hcoord : ∀ d : Fin D, volume {u : Fin D → ℝ | u d = 0} = 0 := by
    intro d
    have hset : {u : Fin D → ℝ | u d = 0}
        = Set.univ.pi (fun i ↦ if i = d then ({0} : Set ℝ) else Set.univ) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hud i; split_ifs with hi
        · rw [hi]; exact hud
        · trivial
      · intro hall; have := hall d; simpa using this
    rw [hset, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp)
  -- the zero set is contained in `⋃_d {u_d = 0}`.
  have hsub : {u : Fin D → ℝ | monoSumSqGerm a Z u = 0} ⊆ ⋃ d : Fin D, {u | u d = 0} := by
    intro u hu
    simp only [Set.mem_setOf_eq, monoSumSqGerm] at hu
    rcases mul_eq_zero.mp hu with hvm | hsum
    · -- `(∏ u_d^{a_d})² = 0` ⟹ some factor `u_d^{a_d} = 0` ⟹ `u_d = 0`.
      have hprod : (∏ d, (u d) ^ (a d)) = 0 := (pow_eq_zero_iff (two_ne_zero)).mp hvm
      obtain ⟨d, _, hd⟩ := Finset.prod_eq_zero_iff.mp hprod
      have had : a d ≠ 0 := by rintro h0; rw [h0, pow_zero] at hd; exact one_ne_zero hd
      exact Set.mem_iUnion.mpr ⟨d, (pow_eq_zero_iff had).mp hd⟩
    · -- `∑_{Z} u_j² = 0` ⟹ every `u_j = 0` for `j ∈ Z` ⟹ `u_{j₀} = 0`.
      have hall : ∀ j ∈ Z, (u j) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).mp hsum
      exact Set.mem_iUnion.mpr ⟨j₀, (pow_eq_zero_iff (two_ne_zero)).mp (hall j₀ hj₀)⟩
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  refine measure_mono_null (Set.inter_subset_left.trans hsub) ?_
  exact measure_iUnion_null (fun d ↦ hcoord d)

/-- **The over-vanishing product threshold** `min( monomialThreshold(a, jac), |Z|/2 )`. The value
the product germ's weighted RLCT attains: the monomial threshold of `vm` on its binding axes, capped
by the sum-of-squares threshold `|Z|/2` (`= r/2`) of the regular-sequence block. -/
noncomputable def monoSumSqThreshold (a jac : Fin D → ℕ) (Z : Finset (Fin D))
    (hbind : (bindingAxes a).Nonempty) : ℝ :=
  min (monomialThreshold a jac hbind) (Z.card / 2 : ℝ)

/-- **The over-vanishing weighted integrability engine (≥ direction).** For a weight `W` that near
`p` factors as the monomial Jacobian weight `jacWeight jac` times a continuous nonvanishing `unit`,
and for `cc` below BOTH the monomial threshold of `vm` on its binding axes AND the sum-of-squares
threshold `|Z|/2`, the weighted product germ `W · (vm²·∑_{Z} u_j²)^{-cc}` is integrable on a
neighbourhood of `p`. The regular-sequence block `Z` is disjoint from `supp(vm)` and carries
`jac = 0` there (`hZjac`, `hZa`), so — after bounding `unit` by its `sup` near `p` (elder amendment
A: the unit COUPLES the blocks and does not factor) — the unit-free box integral factors (Tonelli,
`MeasurableEquiv.piEquivPiSubtypeProd`) into the `Z`-block sum-of-squares integral (finite for
`2·cc < |Z|`, `RLCT.SumSq`) and the complement pure-power monomial box integral (finite for the
threshold, `MonomialBox`).

The `≥`-direction (convergence) is what the V-lower wire consumes; the two-sided `= min` equality is
OUT (needs the unit `inf > 0` marginalization). -/
theorem monoSumSq_integrableAtFilter_of_lt
    {a jac : Fin D → ℕ} {Z : Finset (Fin D)} {W unit : (Fin D → ℝ) → ℝ} {p : Fin D → ℝ} {cc : ℝ}
    (hbind : (bindingAxes a).Nonempty) (hZne : Z.Nonempty)
    (hZa : ∀ j ∈ Z, a j = 0) (hZjac : ∀ j ∈ Z, jac j = 0)
    (hc0 : 0 ≤ cc)
    (hthr : cc < monomialThreshold a jac hbind) (hsos : 2 * cc < (Z.card : ℝ))
    (hunit : ContinuousAt unit p) (hunit0 : unit p ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 p, W u = jacWeight jac u * unit u) :
    IntegrableAtFilter (fun u ↦ W u * negPow (monoSumSqGerm a Z) cc u) (𝓝 p) := by
  -- map: ov-sos-tonelli — the disjoint-block Tonelli factorization (Z-block sum-of-squares via
  -- RLCT.SumSq × complement pure-power box via MonomialBox), after the unit-sup reduction.
  sorry

end DLNFibre.Core.Aoyagi
