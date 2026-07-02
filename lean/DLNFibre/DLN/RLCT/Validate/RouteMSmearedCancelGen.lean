import DLNFibre.DLN.RLCT.Validate.RouteMSmearedDecodeGen
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedFrontFactor

/-!
# `RouteMSmearedCancelGen` — the general-`L` `hcancel` reduction to two box determinants

The general-`L` (arbitrary depth `0 < L`, arbitrary widths) discharge of the boundary-smeared chart's
shear cancellation `P₁·Λ₀ = P₂`, reducing it to a determinant nonvanishing condition on the source
box. Combines the DECODE-side columns (`P1uG`/`P2uG`/`Lam0uG` of `RouteMSmearedDecodeGen`) with the
banked general front factoring (`frontShear_cancel_general`, `RouteMSmearedFrontFactor`).

The KEY structural input (proved unconditionally in the smeared regime, `pen-and-paper` waist verdict):
in the boundary-smeared regime there is a **width-`r` waist** — some front layer `q ≤ L−1` with
`M q = r = deepRank M = min over front widths`. So `frontProd = prodAux (L−1)` factors through the
waist as `prodAux q · Y` with inner width `M q = r`; transporting the inner type through `M q = r`
gives a `U·V` factorization with inner type `Fin r`, and the banked `frontShear_cancel_general` then
gives `P₁·Λ₀ = P₂` off two poles:

* `hVρ` — the waist-split top-`r` block invertible (`det (Vρ) ≠ 0`), `Vρ := V[:, deepWidthEquiv ∘ inl]`;
* `hdet` — the Gram `det (P₁ᵀ P₁) ≠ 0` (`P₁` full column rank `r`).

Both are open conditions; on the conditioned box they are discharged by diagonal dominance (downstream).
This module isolates the pure structural reduction:

* `frontProd_factorsThrough_waist` — the width-`r` `U·V` factorization from the waist split;
* `hcancelG_of_waist` — `P1uG u · Lam0uG u = P2uG u` from a waist `q` with the two determinant
  hypotheses (stated on the transported inner factor `V`), on any point `u`.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-- **The width-`r` `U·V` factorization of the front product through a waist.** For a front waist layer
`q ≤ L−1` with `M ⟨q,_⟩ = r`, the front product `frontProd = prodAux (L−1)` factors as `U · V` with
inner type `Fin r`: `U := prodAux q` recast to `Fin (M 0) × Fin r` (via `M ⟨q,_⟩ = r`), and
`V := Y` recast to `Fin r × Fin (M ⟨L−1,_⟩)` (`Y` the banked `prodAux_split_exists` suffix). -/
theorem frontProd_factorsThrough_waist (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (A : Params M) (q : ℕ) (hq : q < L + 1) (hqk : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r) :
    ∃ (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ),
      frontProd M A hL = U * V := by
  obtain ⟨Y, hY⟩ := prodAux_split_exists M A q hq (L - 1) hqk (by omega)
  -- recast the inner `Fin (M ⟨q,_⟩)` type to `Fin r`
  refine ⟨(prodAux M A q hq).submatrix (id : _ → _) (Fin.cast hMq.symm),
    Y.submatrix (Fin.cast hMq.symm) (id : _ → _), ?_⟩
  rw [frontProd, hY]
  funext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- match the `Fin (M ⟨q,_⟩)`-indexed sum (frontProd side) with the `Fin r`-indexed one (recast) via `finCongr`
  refine Fintype.sum_equiv (finCongr hMq)
    (fun a => (prodAux M A q hq) i a * Y a j)
    (fun k => (prodAux M A q hq).submatrix (id : _ → _) (Fin.cast hMq.symm) i k
      * Y.submatrix (Fin.cast hMq.symm) (id : _ → _) k j) (fun a => ?_)
  simp only [Matrix.submatrix_apply, id_eq, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]

/-- **The general-`L` `hcancel` from the waist split.** Given a front waist layer `q ≤ L−1` with
`M ⟨q,_⟩ = r`, the two box determinant conditions discharge the shear cancellation
`P1uG u · Lam0uG u = P2uG u`.

* `hVρ`: for the `U·V` waist factorization (`frontProd = U·V`, inner `Fin r`), the top-`r` selected
  block `V[:, deepWidthEquiv (inl ·)]` (an `r×r` matrix) has nonzero determinant;
* `hdet`: the Gram `det ((P1uG u)ᵀ (P1uG u)) ≠ 0`.

Feeds the banked `frontShear_cancel_general` with `ρ = deepWidthEquiv ∘ inl`, `σ = deepWidthEquiv ∘ inr`
(the atom-shaped `hrsAtom` split); `Lam0uG = (P₁ᵀP₁)⁻¹ P₁ᵀ P₂` is exactly the projection routing. -/
theorem hcancelG_of_waist (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (hVρ : ∀ (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ),
      frontProd M (frontTupleG M u) hL = U * V →
        (V.submatrix (id : _ → _)
          (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))).det ≠ 0)
    (hdet : ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0) :
    P1uG M hL hrs u * Lam0uG M hL hrs u = P2uG M hL hrs u := by
  obtain ⟨U, V, hUV⟩ := frontProd_factorsThrough_waist M hL (frontTupleG M u) q hq hqL hMq
  -- `P1uG`/`P2uG` are the `deepWidthEquiv`-selected columns of `frontProd = U·V`
  exact frontShear_cancel_general (frontProd M (frontTupleG M u) hL) U V hUV
    (fun k => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))
    (fun j => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr j))
    (P1uG M hL hrs u) (P2uG M hL hrs u)
    (fun i k => rfl) (fun i j => rfl) (hVρ U V hUV) hdet

/-! ## The `hUpos` reduction — `UunitG > 0` from the Gram determinant (tall `P₁`) -/

/-- A finite double sum of squares is positive once one entry is nonzero. -/
theorem frobeniusSq_pos_of_entry_ne' {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) {i₀ : ι} {j₀ : κ} (h : X i₀ j₀ ≠ 0) :
    (0 : ℝ) < ∑ i, ∑ j, (X i j) ^ 2 := by
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) ?_
  exact ⟨i₀, Finset.mem_univ _, Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨j₀, Finset.mem_univ _, by positivity⟩⟩

/-- **Full-column-rank left-injectivity.** If the Gram `P₁ᵀ P₁` is invertible (`det ≠ 0`), then
`P₁ · X = 0 ⟹ X = 0` for any `X` — the tall-`P₁` analog of "left-mult by an invertible square matrix
is injective". Proof: `P₁·X = 0 ⟹ (P₁ᵀP₁)·X = P₁ᵀ·(P₁·X) = 0 ⟹ X = (P₁ᵀP₁)⁻¹·(P₁ᵀP₁)·X = 0`. -/
theorem mul_eq_zero_of_gram_det_ne {m0 r' t : ℕ} (P₁ : Matrix (Fin m0) (Fin r') ℝ)
    (X : Matrix (Fin r') (Fin t) ℝ) (hdet : (P₁.transpose * P₁).det ≠ 0)
    (hPX : P₁ * X = 0) : X = 0 := by
  have hunit : IsUnit (P₁.transpose * P₁).det := isUnit_iff_ne_zero.mpr hdet
  have hgram : (P₁.transpose * P₁) * X = 0 := by
    rw [Matrix.mul_assoc, hPX, Matrix.mul_zero]
  calc X = ((P₁.transpose * P₁)⁻¹ * (P₁.transpose * P₁)) * X := by
            rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
    _ = (P₁.transpose * P₁)⁻¹ * ((P₁.transpose * P₁) * X) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hgram, Matrix.mul_zero]

/-- **`HbarUnitG` is a nonzero matrix.** Its pivot entry `(⟨0,hr⟩, ⟨0,hc⟩)` is the constant `1`. -/
theorem HbarUnitG_ne_zero (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : HbarUnitG M hL hrs hr hc u ≠ 0 := by
  intro h0
  have hpiv : HbarUnitG M hL hrs hr hc u ⟨0, hr⟩ ⟨0, hc⟩ = 1 := by
    simp only [HbarUnitG, pivotCoordG, if_true]
  rw [h0] at hpiv
  exact one_ne_zero hpiv.symm

/-- **`UunitG > 0` from the Gram determinant.** The `z`-free unit `U = ‖P₁·H̄_unit‖²` is positive once
`det (P₁ᵀ P₁) ≠ 0` (`P₁` full column rank): `H̄_unit` is a nonzero matrix (pivot entry `1`), and full
column rank makes `P₁·(·)` left-injective, so `P₁·H̄_unit ≠ 0`, hence its Frobenius sum is positive. The
tall-`P₁` analog of the square `Uunit_pos_of_det_ne`. -/
theorem UunitG_pos_of_gram_det_ne (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ)
    (hdet : ((P1uG M hL hrs u).transpose * P1uG M hL hrs u).det ≠ 0) :
    0 < UunitG M hL hrs hr hc u := by
  -- `P₁·H̄_unit ≠ 0` (H̄ nonzero, `P₁` left-injective)
  have hprodne : P1uG M hL hrs u * HbarUnitG M hL hrs hr hc u ≠ 0 := by
    intro h0
    exact HbarUnitG_ne_zero M hL hrs hr hc u
      (mul_eq_zero_of_gram_det_ne (P1uG M hL hrs u) (HbarUnitG M hL hrs hr hc u) hdet h0)
  -- some entry of the product is nonzero, so the sum of squares is positive
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hprodne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  rw [UunitG]
  exact frobeniusSq_pos_of_entry_ne' _ (by simpa using hj)

end DLNFibre.DLN.RLCT
