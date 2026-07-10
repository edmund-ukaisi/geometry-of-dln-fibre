import DLNFibre.DLN.RLCT.Validate.MatMulFibre

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFreeBilinear` — B4: the `b = 1` free-bilinear leaf

The **first atom brick** of the Aoyagi §5 `(S,J)` resolution (carrier-skeleton
`genm-sjdecomp`, brick **B4**): the base case that closes every `b = 1` chart of the
`(S,J)` recursion. On a `b = 1` pivot chart the corank block `Q_b` is a single free row,
so the leaf loss is the squared Frobenius norm of a rank-one outer product

    frobSq (γ ⊗ z) = ‖γ‖² · ‖z‖²,     γ : Fin (a+1) → ℝ,  z : Fin (D+1) → ℝ,

and the per-chart box integral of `frobSq(γ ⊗ z)^{−c'}` **factors** into two independent radial
integrals (Tonelli),

    ∫⁻_{[−T,T]^{a+1}} ∫⁻_{[−T,T]^{D+1}} (‖γ‖²·‖z‖²)^{−c'}
      = (∫⁻_{[−T,T]^{a+1}} ‖γ‖^{−2c'}) · (∫⁻_{[−T,T]^{D+1}} ‖z‖^{−2c'}),

each factor finite for `c' < (a+1)/2` resp. `c' < (D+1)/2` by the banked radial-Morse leaf
`sumSqND_box_lt_top`. Hence the product is `< ⊤` for `c' < ½·min(a+1, D+1)` — the leaf's own RLCT
contribution `½·min(a, D)` (crnrt Q3/Q4, cornrev Q1; the `(a,1,D)` free-bilinear leaf).

## Scope / fidelity

This is the leaf's **own** charge, delivered as an honest `∫⁻ … < ⊤` finiteness (the upper /
`rlct ≥ ½·min` leg — the matching `rlct ≤ ½·codim` is the separately-cited Watanabe/Aoyagi
interface). Two downstream obligations named in the B4 contract are **NOT** in this brick,
belonging to the
`DecoratedPeelStep` assembly (B6) / disjoint-sum step (B5b):

* the **coupling** `C'·B₀` inside `‖C'·B₀ + γz‖²` is removed by comparability (`f ≍ ‖B₀‖² + ‖γz‖²`);
* the **direct-sum** with the reduced-chain IH composes this leaf's `½·min(a,D)` additively with the
  pivot/redChain charge (`radial_morse_dominates_lt_top` on disjoint variable blocks) to reach
  `½·minAdm` at the binding cut.

Consumes only `frobSq` (`MatMulFibre`) and the banked radial leaf `sumSqND_box_lt_top`
+ `morseBox` (`S1RadialMorse`). No recursion; size **S**. S2-free (no `monomial_rlct`).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

/-! ## The rank-one Frobenius algebra -/

/-- **The outer-product Frobenius square factorises.** For the rank-one matrix `γ ⊗ z` with entries
`(γ ⊗ z)_{ij} = γᵢ·zⱼ`, `frobSq (γ ⊗ z) = ‖γ‖² · ‖z‖² = (∑ᵢ γᵢ²)·(∑ⱼ zⱼ²)`. -/
theorem frobSq_outer {p q : ℕ} (γ : Fin p → ℝ) (z : Fin q → ℝ) :
    frobSq (fun i j => γ i * z j) = (∑ i, (γ i) ^ 2) * (∑ j, (z j) ^ 2) := by
  unfold frobSq
  rw [Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [mul_pow]

/-- **At corank `b = 1` the product `Γ·Q_b` IS the outer product `γ ⊗ z`.** For a single-column
`Γ : Fin p → Fin 1 → ℝ` and single-row `Q : Fin 1 → Fin q → ℝ`, `(Γ·Q)_{ij} = Γ_{i0}·Q_{0j}`,
the rank-one bilinear the `b = 1` leaf integrates. This is the fidelity link: the `b = 1`
corank block is a free row, so its loss `frobSq(Γ·Q_b)` is exactly the free-bilinear leaf below. -/
theorem rmatMul_corank_one {p q : ℕ} (X : Fin p → Fin 1 → ℝ) (Y : Fin 1 → Fin q → ℝ) :
    rmatMul X Y = fun i j => X i 0 * Y 0 j := by
  funext i j
  simp only [rmatMul, Fin.sum_univ_one]

/-- The `b = 1` corank product's Frobenius square factors as `‖γ‖²·‖z‖²` with `γ = Γ·,0`,
`z = Q_0,·` (`rmatMul_corank_one` + `frobSq_outer`). -/
theorem frobSq_rmatMul_corank_one {p q : ℕ} (X : Fin p → Fin 1 → ℝ) (Y : Fin 1 → Fin q → ℝ) :
    frobSq (rmatMul X Y) = (∑ i, (X i 0) ^ 2) * (∑ j, (Y 0 j) ^ 2) := by
  rw [rmatMul_corank_one]; exact frobSq_outer _ _

/-! ## The Tonelli factoring of the leaf integral -/

/-- **The free-bilinear leaf integral factors.** The iterated box integral of the rank-one
outer-product loss `frobSq(γ ⊗ z)^{−c'}` equals the product of the two independent radial box
integrals — the `∫‖γ‖^{−2c'}·∫‖z‖^{−2c'}` factoring the certificate names. The `z`-block finiteness
(`c' < (D+1)/2`, so its integral `≠ ⊤`) is used to pull it out of the `γ`-integral as a constant. -/
theorem freeBilinear_box_factor (a D : ℕ) (T : ℝ) (hT : 0 < T) (c' : ℝ)
    (hcD : c' < (↑D + 1 : ℝ) / 2) :
    (∫⁻ γ in morseBox (a + 1) T, ∫⁻ z in morseBox (D + 1) T,
        ENNReal.ofReal (frobSq (fun (i : Fin (a + 1)) (j : Fin (D + 1)) => γ i * z j) ^ (-c')))
      = (∫⁻ γ in morseBox (a + 1) T, ENNReal.ofReal ((∑ i, (γ i) ^ 2) ^ (-c')))
          * (∫⁻ z in morseBox (D + 1) T, ENNReal.ofReal ((∑ j, (z j) ^ 2) ^ (-c'))) := by
  -- inner integral (fixed γ): the loss splits multiplicatively, pull the γ-only factor out
  have hin : ∀ γ : Fin (a + 1) → ℝ,
      (∫⁻ z in morseBox (D + 1) T,
          ENNReal.ofReal (frobSq (fun (i : Fin (a + 1)) (j : Fin (D + 1)) => γ i * z j) ^ (-c')))
        = ENNReal.ofReal ((∑ i, (γ i) ^ 2) ^ (-c'))
            * ∫⁻ z in morseBox (D + 1) T, ENNReal.ofReal ((∑ j, (z j) ^ 2) ^ (-c')) := by
    intro γ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun z => ?_)
    have hg : (0 : ℝ) ≤ ∑ i, (γ i) ^ 2 := by positivity
    have hz : (0 : ℝ) ≤ ∑ j, (z j) ^ 2 := by positivity
    rw [frobSq_outer, Real.mul_rpow hg hz, ENNReal.ofReal_mul (Real.rpow_nonneg hg _)]
  -- the pulled-out z-block is finite, hence a genuine constant we can factor out of the γ-integral
  have hIz : (∫⁻ z in morseBox (D + 1) T, ENNReal.ofReal ((∑ j, (z j) ^ 2) ^ (-c'))) ≠ ⊤ :=
    (sumSqND_box_lt_top D T hT c' hcD).ne
  calc (∫⁻ γ in morseBox (a + 1) T, ∫⁻ z in morseBox (D + 1) T,
          ENNReal.ofReal (frobSq (fun (i : Fin (a + 1)) (j : Fin (D + 1)) => γ i * z j) ^ (-c')))
      = ∫⁻ γ in morseBox (a + 1) T,
          ENNReal.ofReal ((∑ i, (γ i) ^ 2) ^ (-c'))
            * ∫⁻ z in morseBox (D + 1) T, ENNReal.ofReal ((∑ j, (z j) ^ 2) ^ (-c')) :=
        lintegral_congr hin
    _ = (∫⁻ γ in morseBox (a + 1) T, ENNReal.ofReal ((∑ i, (γ i) ^ 2) ^ (-c')))
          * (∫⁻ z in morseBox (D + 1) T, ENNReal.ofReal ((∑ j, (z j) ^ 2) ^ (-c'))) :=
        lintegral_mul_const' _ _ hIz

/-! ## The B4 leaf finiteness -/

/-- **B4 — the `b = 1` free-bilinear leaf is finite up to `½·min(a, D)`.** The per-chart box
integral of the rank-one outer-product loss `frobSq(γ ⊗ z)^{−c'}` (`γ : Fin (a+1) → ℝ`,
`z : Fin (D+1) → ℝ`) is finite for every `c' < ½·min(a+1, D+1)`, by factoring
(`freeBilinear_box_factor`) into two radial box integrals each finite by `sumSqND_box_lt_top`.
This is the leaf's own RLCT contribution `½·min(a, D)` that closes every `b = 1` chart of the
`(S,J)` recursion (the direct-sum with the reduced-chain charge to reach `½·minAdm` is the B6
assembly step). -/
theorem freeBilinear_box_lt_top (a D : ℕ) (T : ℝ) (hT : 0 < T) (c' : ℝ)
    (hc : c' < (↑(min (a + 1) (D + 1)) : ℝ) / 2) :
    (∫⁻ γ in morseBox (a + 1) T, ∫⁻ z in morseBox (D + 1) T,
        ENNReal.ofReal (frobSq (fun (i : Fin (a + 1)) (j : Fin (D + 1)) => γ i * z j) ^ (-c')))
      < ⊤ := by
  have hca : c' < (↑a + 1 : ℝ) / 2 := by
    refine lt_of_lt_of_le hc ?_
    gcongr
    exact_mod_cast min_le_left (a + 1) (D + 1)
  have hcD : c' < (↑D + 1 : ℝ) / 2 := by
    refine lt_of_lt_of_le hc ?_
    gcongr
    exact_mod_cast min_le_right (a + 1) (D + 1)
  rw [freeBilinear_box_factor a D T hT c' hcD]
  exact ENNReal.mul_lt_top (sumSqND_box_lt_top a T hT c' hca) (sumSqND_box_lt_top D T hT c' hcD)

/-! ## Non-vacuity -/

/-- Non-vacuity witness: `a = 1, D = 2` (dims `2 × 3`), `c' = 1/2 < min(2,3)/2 = 1`. -/
example :
    (∫⁻ γ in morseBox 2 1, ∫⁻ z in morseBox 3 1,
        ENNReal.ofReal (frobSq (fun (i : Fin 2) (j : Fin 3) => γ i * z j) ^ (-(1 / 2 : ℝ))))
      < ⊤ :=
  freeBilinear_box_lt_top 1 2 1 (by norm_num) (1 / 2) (by norm_num)

end DLNFibre.DLN.RLCT
