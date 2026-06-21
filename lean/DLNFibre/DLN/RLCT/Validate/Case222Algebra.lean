import DLNFibre.DLN.RLCT.Foundations.ParamsFlat222
import DLNFibre.DLN.RLCT.Validate.Case222Resolution

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

/-- **Forward coordinate extraction.** `(e222 A)` at the slot of `(s,i,j)` recovers the matrix entry
`A s i j`. The forward companion of `e222_symm_coord` (via the left-inverse
`e222.symm_apply_apply`): `A s i j = (e222.symm (e222 A)) s i j = (e222 A) (slot s i j)`. -/
theorem e222_coord (A : Params H222) (s i j : Fin 2) :
    (e222 A) (fin8EquivFlatIdx222.symm (⟨⟨s, i⟩, j⟩ : FlatIdx H222)) = A s i j := by
  have h := e222_symm_coord (e222 A) s i j
  rw [e222.symm_apply_apply] at h
  exact h.symm

/-- **The `(2,2,2)` loss-identity (`#66` seam `hloss`).** The deep-linear loss at `B = 0` equals
`myF222 ∘ e222` — i.e. `‖prod H222 A‖²` in the explicit flat `a00=0..b11=7` coordinates. Discharges
the `hloss` hypothesis of `rlctAtOn_dlnLoss222_transport`, closing the seam end-to-end. Via
`prod_two_layer` (the `Fin 2`-inner product) + the `Fin.sum_univ_two` entry expansion + the forward
coordinate map (`e222_coord` + the `slot_*` table). -/
theorem dlnLoss222_eq_myF222 :
    dlnLoss H222 (0 : Matrix (Fin (H222 0)) (Fin (H222 (Fin.last 2))) ℝ)
      = fun A => myF222 (e222 A) := by
  funext A
  -- The eight forward coordinate facts `(e222 A) slot = A s i j` (`e222_coord` + the slot table).
  have a00 : A 0 (0 : Fin 2) (0 : Fin 2) = (e222 A) 0 := (e222_coord A 0 0 0).symm
  have a01 : A 0 (0 : Fin 2) (1 : Fin 2) = (e222 A) 1 := (e222_coord A 0 0 1).symm
  have a10 : A 0 (1 : Fin 2) (0 : Fin 2) = (e222 A) 2 := (e222_coord A 0 1 0).symm
  have a11 : A 0 (1 : Fin 2) (1 : Fin 2) = (e222 A) 3 := (e222_coord A 0 1 1).symm
  have b00 : A 1 (0 : Fin 2) (0 : Fin 2) = (e222 A) 4 := (e222_coord A 1 0 0).symm
  have b01 : A 1 (0 : Fin 2) (1 : Fin 2) = (e222 A) 5 := (e222_coord A 1 0 1).symm
  have b10 : A 1 (1 : Fin 2) (0 : Fin 2) = (e222 A) 6 := (e222_coord A 1 1 0).symm
  have b11 : A 1 (1 : Fin 2) (1 : Fin 2) = (e222 A) 7 := (e222_coord A 1 1 1).symm
  -- Expand the loss into the four product-entries, each via `prod_two_layer`.
  unfold dlnLoss myF222
  -- Drop the `- 0` at the matrix level, then expand each entry via `prod_two_layer`.
  simp only [sub_zero]
  simp_rw [prod_two_layer]
  -- Coerce the dependent `Fin (H222 _)` sum index types to the syntactic `Fin 2` (defeq), so
  -- `Fin.sum_univ_two` fires on all three sum levels; then rewrite to the flat coords.
  change ∑ i : Fin 2, ∑ j : Fin 2, (∑ k : Fin 2, A 0 i k * A 1 k j) ^ 2 = _
  simp only [Fin.sum_univ_two, a00, a01, a10, a11, b00, b01, b10, b11]
  ring

end DLNFibre.DLN.RLCT
