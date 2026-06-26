import DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestCompositionE1` — the E1 core-algebra of the diffeo bridge

The diffeo bridge `hstep2` (`DeepestGaugeConstruction:3195`) reparametrizes the flat coordinates by the
joint `(T1, Y1)` action Ψ so that `Φcore ∘ Ψ =ᶠ[𝓝 wstar] Φscore`. The **E1 (core) half** of that
composition identity is the matrix-algebra fact that, once Ψ has absorbed the last-layer Schur core
`S1 ↦ S1' = (1 − K)·S1` (the cert's E1 constraint), the reduced two-layer product of the per-layer
cores equals the GLOBAL product Schur complement `Rcore`:

    coreΦ(Ψ x) = frobSq( prod_M (absorbed cores) )       -- deepestCoreF_coreAbsorb_eq_prodSchur
               = frobSq( S0 · S1' )                       -- the 2-layer product = product of factors
               = frobSq( S0 · ((1 − K)·S1) )              -- S1' = (1 − K)·S1 (the absorb)
               = frobSq( S0 · (1 − K) · S1 )              -- associativity
               = frobSq( Rcore )                          -- schur_product_ldu: Rcore = S0·(1−K)·S1
               = Score(x).

This module supplies the **frame-free matrix core** of that chain (the middle four `=`), as
sorry-free `Matrix`-algebra lemmas the eventual Ψ-wiring consumes directly. It does NOT construct Ψ
(blocked on the W⁻¹/⅟P00 cutoff inverse-smoothness + the E2 reg-preservation certs); it states the
energy identity the wiring needs, keyed on the banked LDU output form `Rcore = S0·(1−K)·S1`
(`schur_product_ldu` / `reindex_mul_schur_factor`).

`K = Z1·⅟P·Y0` is the off-pivot correction (the `(1 − K)` middle factor the bridge must absorb — NOT
drop: the box-ratio `∑‖Rcore‖² ≍ ∑‖S0·S1‖²` is FALSE off-germ, see `DeepestSchurComparability`). The
absorb `S1' = (1 − K)·S1` makes the reduced product equal `Rcore` exactly; that is what E1 records.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`): pure `Matrix.mul_assoc` + the banked LDU.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {m0 m1 m2 : Type*}

/-- **E1 matrix identity** (the absorb makes the reduced product equal `Rcore`). Given the banked LDU
output `Rcore = S0·(1 − K)·S1` and the absorbed last-layer core `S1' = (1 − K)·S1` (the cert's E1
constraint), the two-layer reduced product `S0 · S1'` equals `Rcore`. Pure associativity. -/
theorem prod_absorbed_eq_rcore
    [Fintype m1] [DecidableEq m1]
    (S0 : Matrix m0 m1 ℝ) (S1 : Matrix m1 m2 ℝ) (K : Matrix m1 m1 ℝ)
    (Rcore : Matrix m0 m2 ℝ) (S1' : Matrix m1 m2 ℝ)
    (hR : Rcore = S0 * (1 - K) * S1) (habs : S1' = (1 - K) * S1) :
    S0 * S1' = Rcore := by
  rw [hR, habs, ← Matrix.mul_assoc]

/-- **E1 energy identity** (the form the diffeo bridge consumes). With the LDU output
`Rcore = S0·(1 − K)·S1` and the absorb `S1' = (1 − K)·S1`, the squared-Frobenius energy of the
absorbed reduced product `S0 · S1'` equals `frobSq Rcore` (`= Score` in the producer). This is the
`coreΦ(Ψ·) = Score` half of the composition identity, at the energy level, frame-free. -/
theorem frobSq_prod_absorbed_eq_rcore
    [Fintype m0] [Fintype m1] [DecidableEq m1] [Fintype m2]
    (S0 : Matrix m0 m1 ℝ) (S1 : Matrix m1 m2 ℝ) (K : Matrix m1 m1 ℝ)
    (Rcore : Matrix m0 m2 ℝ) (S1' : Matrix m1 m2 ℝ)
    (hR : Rcore = S0 * (1 - K) * S1) (habs : S1' = (1 - K) * S1) :
    frobSq (S0 * S1') = frobSq Rcore := by
  rw [prod_absorbed_eq_rcore S0 S1 K Rcore S1' hR habs]

/-- **E1, keyed directly on the banked LDU** (`schur_product_ldu`). For two gauge-sliced layers with
per-layer blocks `(A0,Y0,Z0,T0)`, `(A1,Y1,Z1,T1)` (invertible pivots `A0, A1` and product pivot
`P = A0·A1 + Y0·Z1`), the absorbed product `S0 · S1'` — where `S0 = T0 − Z0·⅟A0·Y0`,
`S1 = T1 − Z1·⅟A1·Y1`, `K = Z1·⅟P·Y0`, `S1' = (1 − K)·S1` — equals the GLOBAL product Schur complement
`Rcore = (Z0·Y1+T0·T1) − (Z0·A1+T0·Z1)·⅟P·(A0·Y1+Y0·T1)`. The LDU is discharged in-lemma; the consumer
supplies only the `S1'`-absorb. -/
theorem prod_absorbed_eq_schur_ldu
    [Fintype m0] [DecidableEq m0] [Fintype m1] [DecidableEq m1] [Fintype m2] [DecidableEq m2]
    {r : Type*} [Fintype r] [DecidableEq r]
    (A0 A1 : Matrix r r ℝ) (Y0 : Matrix r m1 ℝ) (Y1 : Matrix r m2 ℝ)
    (Z0 : Matrix m0 r ℝ) (Z1 : Matrix m1 r ℝ) (T0 : Matrix m0 m1 ℝ) (T1 : Matrix m1 m2 ℝ)
    [Invertible A0] [Invertible A1] [Invertible (A0 * A1 + Y0 * Z1)]
    (S1' : Matrix m1 m2 ℝ)
    (habs : S1' = (1 - Z1 * ⅟(A0 * A1 + Y0 * Z1) * Y0) * (T1 - Z1 * ⅟A1 * Y1)) :
    (T0 - Z0 * ⅟A0 * Y0) * S1'
      = (Z0 * Y1 + T0 * T1)
          - (Z0 * A1 + T0 * Z1) * ⅟(A0 * A1 + Y0 * Z1) * (A0 * Y1 + Y0 * T1) := by
  -- `schur_product_ldu` gives `Rcore = S0·(1−K)·S1`; `prod_absorbed_eq_rcore` then absorbs into `S1'`.
  exact prod_absorbed_eq_rcore (T0 - Z0 * ⅟A0 * Y0) (T1 - Z1 * ⅟A1 * Y1)
    (Z1 * ⅟(A0 * A1 + Y0 * Z1) * Y0)
    ((Z0 * Y1 + T0 * T1)
        - (Z0 * A1 + T0 * Z1) * ⅟(A0 * A1 + Y0 * Z1) * (A0 * Y1 + Y0 * T1)) S1'
    (schur_product_ldu A0 A1 Y0 Y1 Z0 Z1 T0 T1) habs

/-! ## Non-vacuity witness

The E1 identity is exercised with a genuinely nonzero off-pivot correction `K ≠ 0` (so the absorb
`S1' = (1 − K)·S1 ≠ S1` is a real reparametrization, not the identity) and a rectangular shape. Take
`m0 = Fin 2`, `m1 = m2 = Fin 1`, `S0 = ![1,0]ᵀ`, `S1 = [1]`, `K = [1/2]`: then `S1' = [1/2]`,
`S0·S1' = ![1/2, 0]ᵀ = Rcore`, and `S0·S1 = ![1, 0]ᵀ ≠ Rcore` — the absorb genuinely moves the product
onto `Rcore`. -/
example :
    let S0 : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then (1 : ℝ) else 0
    let S1 : Matrix (Fin 1) (Fin 1) ℝ := 1
    let K : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => (1 : ℝ) / 2
    let Rcore : Matrix (Fin 2) (Fin 1) ℝ := S0 * (1 - K) * S1
    let S1' : Matrix (Fin 1) (Fin 1) ℝ := (1 - K) * S1
    -- the absorb moves the product onto Rcore, AND it is a genuine move (S0·S1 ≠ Rcore)
    (S0 * S1' = Rcore) ∧ (S0 * S1 ≠ Rcore) := by
  refine ⟨prod_absorbed_eq_rcore _ _ _ _ _ rfl rfl, ?_⟩
  intro h
  -- `S0·S1 = S0` (S1 = 1); `Rcore 0 0 = 1/2`; so `(S0·S1) 0 0 = 1 ≠ 1/2`.
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply] at this
  norm_num at this

end DLNFibre.DLN.RLCT
