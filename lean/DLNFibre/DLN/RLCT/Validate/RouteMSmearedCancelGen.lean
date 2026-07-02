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
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ)
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

end DLNFibre.DLN.RLCT
