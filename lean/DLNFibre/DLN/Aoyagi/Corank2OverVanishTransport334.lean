import DLNFibre.DLN.Aoyagi.Corank2OverVanishCanon334

/-!
# `DLN.Aoyagi.Corank2OverVanishTransport334` — the σ_p1 loss-symmetry (transport crux)

The parametric leverage that lifts the 16 canonical `(p1 = 20)` over-vanishing leaves to all 144:
each dominant `p1` chart is the `σ_p1`-conjugate of the canonical, where `σ_p1 = rowswap i ∘ colswap j`
is a genuine **loss-symmetry** of the `(3,3,4)` network (a row/col permutation of the weights).

This file lands the CRUX: the loss `∑_k (coreGen k)²` is invariant under a coordinate permutation
acting as a row/col symmetry on `A0`/`A1`. Concretely, if `A0 (w∘σ) = A0 w` reindexed by
`(swap 0 i, swap 0 j)` and `A1 (w∘σ) = A1 w` reindexed by `(id, swap 0 i)`, then
`A1 (w∘σ) · A0 (w∘σ) = (A1 w · A0 w)` reindexed by `(id, swap 0 j)` — a single column swap — so the
Frobenius norm (= `∑_k coreGen²`) is preserved. (The `swap 0 i` on `A0`-ROWS cancels the `swap 0 i`
on `A1`-COLUMNS in the product, leaving only the `swap 0 j` column permutation.)

The per-`p1` hypotheses `hA0`/`hA1` are decidable finite checks on `σ_p1`'s action on the `A0`/`A1`
coordinate reads (`Corank2NativeFan334` centres); the σ_p1 defs + their discharge + the full chart
conjugation (via `blockBlowupMap_conj`) + the 144-transport theorem are the remaining assembly.
-/

open Matrix
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.OverVanishCanon334

namespace DLNFibre.DLN.Aoyagi.OverVanishTransport334

/-- **The `coreGen` loss as the Frobenius sum of the `A1·A0` product entries.** Reindexes the flat
`Fin 12` sum to the `4×3` matrix double-sum via `finProdFinEquiv` + `coreGen_eWrap_entry`. -/
theorem sumSq_coreGen_eq_frob (v : Fin 21 → ℝ) :
    (∑ k, (coreGen dvec eWrap k v) ^ 2)
      = ∑ a : Fin 4, ∑ c : Fin 3, ((A1 v * A0 v) a c) ^ 2 := by
  have h : (∑ k, (coreGen dvec eWrap k v) ^ 2)
      = ∑ p : Fin 4 × Fin 3, ((A1 v * A0 v) p.1 p.2) ^ 2 := by
    calc (∑ k, (coreGen dvec eWrap k v) ^ 2)
        = ∑ k, ((A1 v * A0 v) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ^ 2 :=
          Finset.sum_congr rfl (fun k _ => congrArg (· ^ 2) (coreGen_eWrap_entry k v))
      _ = ∑ p : Fin 4 × Fin 3, ((A1 v * A0 v) p.1 p.2) ^ 2 :=
          Equiv.sum_comp finProdFinEquiv.symm (fun p => ((A1 v * A0 v) p.1 p.2) ^ 2)
  rw [h, Fintype.sum_prod_type]

/-- **The σ_p1 loss-symmetry (the transport crux).** If a coordinate permutation `σ` acts on `A0`'s
reads as the `(swap 0 i, swap 0 j)` row/col reindex and on `A1`'s reads as the `(swap 0 i)` column
reindex (the `hA0`/`hA1` hypotheses — decidable per `p1`), then the `coreGen` loss is `σ`-invariant.
The `swap 0 i` on `A0`-rows cancels the `swap 0 i` on `A1`-columns inside the product, leaving a bare
`swap 0 j` column permutation of `A1·A0`, under which `∑_k coreGen²` (the Frobenius sum) is fixed. -/
theorem sumSq_coreGen_symm (w : Fin 21 → ℝ) (σ : Equiv.Perm (Fin 21)) (i j : Fin 3)
    (hA0 : ∀ r c, A0 (fun t => w (σ t)) r c = A0 w (Equiv.swap 0 i r) (Equiv.swap 0 j c))
    (hA1 : ∀ a b, A1 (fun t => w (σ t)) a b = A1 w a (Equiv.swap 0 i b)) :
    (∑ k, (coreGen dvec eWrap k (fun t => w (σ t))) ^ 2)
      = ∑ k, (coreGen dvec eWrap k w) ^ 2 := by
  rw [sumSq_coreGen_eq_frob, sumSq_coreGen_eq_frob]
  -- the product is `A1 w · A0 w` with columns permuted by `swap 0 j`
  have hmult : ∀ a c, (A1 (fun t => w (σ t)) * A0 (fun t => w (σ t))) a c
      = (A1 w * A0 w) a (Equiv.swap 0 j c) := by
    intro a c
    rw [Matrix.mul_apply, Matrix.mul_apply,
      ← Equiv.sum_comp (Equiv.swap (0 : Fin 3) i)
        (fun b => A1 w a b * A0 w b (Equiv.swap 0 j c))]
    exact Finset.sum_congr rfl (fun b _ => by rw [hA1 a b, hA0 b c])
  -- `∑_a ∑_c (M' a c)² = ∑_a ∑_c (M a c)²`: reindex `c` on the RHS through the involution, then `hmult`
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Equiv.sum_comp (Equiv.swap (0 : Fin 3) j) (fun c => ((A1 w * A0 w) a c) ^ 2)]
  exact Finset.sum_congr rfl (fun c _ => congrArg (· ^ 2) (hmult a c))

end DLNFibre.DLN.Aoyagi.OverVanishTransport334
