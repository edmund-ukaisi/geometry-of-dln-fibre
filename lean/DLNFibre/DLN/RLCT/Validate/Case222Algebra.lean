import DLNFibre.DLN.RLCT.Foundations.ParamsFlat222

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Algebra` — the `(2,2,2)` layer-product entry form

The matrix-algebra unblock for the `(2,2,2)` seam loss-identity (`#54`/`#75`): the `L = 2` layer
product `prod H222 A = C⁽¹⁾·C⁽²⁾` has the explicit entrywise form `(prod H222 A) i j = ∑ₖ A₀ᵢₖ·A₁ₖⱼ`
(the genuine `Fin 2`-inner matrix product). `fm-2`'s seam consumes this to expand
`dlnLoss H222 0 A = ‖prod H222 A‖²` into the explicit `myF222 ∘ e222` form, discharging the
`hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`.

The `(2,2,2)` analogue of `Case212.prod212_entry`. The new content vs `(2,1,2)` (which had a `Fin 1`
inner dim collapsing by `Finset.sum_singleton`) is the **`Fin 2` inner sum** + the `prodAux`
dependent-`Fin`-cast: `prodAux`'s `rw [e1, e2]` produces `cast`s on the `Matrix` type between
defeq-but-not-syntactic `Fin (H222 ⟨k,_⟩)` index types that resist `cast_eq`/`Subsingleton.elim`/
`Matrix.one_mul`. The closer is `Finset.sum_congr rfl` (unifies the cast-typed sum index to the
target) + `congr 1` (discharges the second factor) + `convert congrFun (congrFun (Matrix.one_mul _)
i) k using 2` (bridges the residual `1 * cast(cast(A₀))` defeq — fm-2's pattern; the `convert`
discharges what `Matrix.one_mul`/`cast_eq`/`heq` cannot fire on directly). `H222 = fun _ => 2`
reduces the index bounds to `2` by `rfl`, so no `cons_val` needed. -/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **`(2,2,2)` layer-product entry form.** `(prod H222 A) i j = ∑ₖ A₀ᵢₖ · A₁ₖⱼ` — the explicit
`L = 2` matrix product `C⁽¹⁾·C⁽²⁾` (inner dim `Fin (H222 1) = Fin 2`). Discharges the `(2,2,2)`
loss-identity for the seam (`#54`). -/
theorem prod_two_layer (A : Params H222) (i : Fin (H222 0)) (j : Fin (H222 2)) :
    prod H222 A i j = ∑ k : Fin (H222 1), A 0 i k * A 1 k j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k using 2

end DLNFibre.DLN.RLCT
