import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat

/-!
# `DLNFibre.DLN.RLCT.Validate.Case212` — the `(2,1,2)` headline via product-MIN (SPECIFY skeleton)

The second ladder rung. `M = (2,1,2)`, `r = 0`: the core is `C⁽¹⁾` (`2×1`, entries `a₁,a₂`) times
`C⁽²⁾` (`1×2`, entries `b₁,b₂`), product `P_ij = aᵢbⱼ`, and

  `dlnLoss (2,1,2) 0 A = ‖P‖² = Σ_ij (aᵢbⱼ)² = (a₁²+a₂²)(b₁²+b₂²) = G(a)·H(b)`

a **product of two disjoint smooth blocks** (verified `F = G·H`). So the RLCT is `min` (NOT sum —
`product_min_rlct`, the Tonelli split), each block `= 1` (`smoothBlockND_rlct 1`), giving
`min(1,1) = 1 = lambdaCore (2,1,2) = aoyagiLambda (2,1,2) 0` (verified `#eval`).

**This is SPECIFY-phase**: the headline statement + the decomposition into named sorries, structure
validated by `lake build`. The genuine work to fill:
- `dlnLoss_case212`: the entrywise product form (dependent-`Fin` `prod` unfold for `L = 2`);
- `entryME212`: the measure-preserving `Params (2,1,2) ≃ᵐ (Fin 2→ℝ)×(Fin 2→ℝ)` (paramsEquivFlat →
  `Fin 4 ≃ Fin 2 ⊕ Fin 2` layer-partition → `sumPiEquivProdPi`) transporting `dlnLoss` to `G·H`;
- the `EuclideanSpace ℝ (Fin 2)` ↔ `Fin 2 → ℝ` bridge for `smoothBlockND_rlct`;
- the `product_min_rlct` hypothesis discharge (positivity + down-set), cleaner once `#57`
  `product_min_rlct_of_ne` lands on trunk.

NO blow-up, NO transport-properness (product-MIN is a Tonelli split, dodges the R1 chart-cover gap).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal

/-- The deepest point of the `(2,1,2)` `B = 0` fibre: the origin (all entries zero). -/
noncomputable def deepest212 : Params (![2, 1, 2] : Fin 3 → ℕ) := fun _ => 0

/-- The two smooth blocks: `G(a) = a₁²+a₂²` on `Fin 2 → ℝ`. -/
noncomputable def blockG : (Fin 2 → ℝ) → ℝ := fun a => ∑ i, a i ^ 2

/-- The two smooth blocks: `H(b) = b₁²+b₂²` on `Fin 2 → ℝ`. -/
noncomputable def blockH : (Fin 2 → ℝ) → ℝ := fun b => ∑ i, b i ^ 2

/-- The `prod` entry form for `(2,1,2)`: `P_ij = aᵢ·bⱼ` (the `2×1` times `1×2` product, single inner
index `⟨0,_⟩ : Fin 1`). `prodAux` for `L = 2` telescopes `(1·C⁽¹⁾)·C⁽²⁾`. PROVE note: closes on a
bare-`Loss` import. Under the full Case212 imports the simp normal form differs: `simp` reduces to
`(1 * A 0) i 0 = A 0 i 0 ∨ A 1 0 j = 0`, and the left disjunct's `1 * A 0` carries a `prodAux`
`Fin`-cast that blocks `Matrix.one_mul` (the cast-aware closer is the remaining work). -/
theorem prod212_entry (A : Params (![2, 1, 2] : Fin 3 → ℕ)) (i j : Fin 2) :
    prod (![2, 1, 2] : Fin 3 → ℕ) A i j
      = A 0 i ⟨0, by norm_num⟩ * A 1 ⟨0, by norm_num⟩ j := by
  sorry

/-- **(2,1,2) loss factors as `G·H`** (the entrywise product form). `dlnLoss (2,1,2) 0` at a tuple
`A` equals `(Σᵢ aᵢ²)(Σⱼ bⱼ²)` with `aᵢ = A 0 i ⟨0,·⟩` (the `2×1` first layer) and
`bⱼ = A 1 ⟨0,·⟩ j` (the `1×2` second layer). From `prod212_entry` (`P_ij = aᵢ·bⱼ`) +
`Σ_ij (aᵢbⱼ)² = (Σaᵢ²)(Σbⱼ²)` (`Finset.sum_mul_sum`). The middle index `⟨0, _⟩` is the unique
element of `Fin 1` (`![2,1,2] 1 = 1`); explicit, to avoid the `OfNat (Fin 1)` reduction snag.
The `prod212_entry` → `sum_mul_sum` → `ring` chain is verified (scratch); blocked only on the
`prod212_entry` cast-closer above. -/
theorem dlnLoss_case212 (A : Params (![2, 1, 2] : Fin 3 → ℕ)) :
    dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0 A
      = (∑ i, (A 0 i ⟨0, by norm_num⟩) ^ 2) * (∑ j, (A 1 ⟨0, by norm_num⟩ j) ^ 2) := by
  unfold dlnLoss
  have hentry : ∀ i j, (prod (![2, 1, 2] : Fin 3 → ℕ) A - 0) i j
      = A 0 i ⟨0, by norm_num⟩ * A 1 ⟨0, by norm_num⟩ j := by
    intro i j; rw [sub_zero]; exact prod212_entry A i j
  simp_rw [hentry]
  rw [Finset.sum_mul_sum]
  congr 1; ext i; congr 1; ext j; ring

/-- **The coordinate split.** `Params (2,1,2)` is measure-preservingly `(Fin 2→ℝ)×(Fin 2→ℝ)` (the
`a`-block × the `b`-block), under which `dlnLoss (2,1,2) 0` transports to `blockG p.1 · blockH p.2`.
Built from `paramsEquivFlat` (measure-preserving) → the layer partition `Fin 4 ≃ Fin 2 ⊕ Fin 2` →
`sumPiEquivProdPi`. The deepest point maps to `(0, 0)`. -/
theorem rlctAtOn_case212_eq_product :
    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
      = rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0) := by
  sorry

/-- **Each block has RLCT 1.** `rlctAtOn blockG 0 = 1` (and likewise `blockH`): `blockG = Σᵢ aᵢ²` on
`Fin 2 → ℝ`, which is `smoothBlockND_rlct 1` (`m = 1`, `n = m+1 = 2`, value `(m+1)/2 = 1`) bridged
across the `EuclideanSpace ℝ (Fin 2) ≃ Fin 2 → ℝ` identification. -/
theorem rlctAtOn_blockG_eq_one : rlctAtOn blockG (0 : Fin 2 → ℝ) = 1 := by
  sorry

theorem rlctAtOn_blockH_eq_one : rlctAtOn blockH (0 : Fin 2 → ℝ) = 1 := by
  sorry

/-- **product-MIN for the two blocks.** `rlctAtOn (G·H)(0,0) = min (rlctAtOn G 0)(rlctAtOn H 0)`
via `product_min_rlct` (Tonelli `∫(GH)^{−c} = (∫G^{−c})(∫H^{−c})`, finite ⟺ both ⟺ `c < min`). The 4
positivity/down-set hypotheses are discharged from the smooth-block structure (cleaner via `#57`
`product_min_rlct_of_ne` once on trunk). -/
theorem rlctAtOn_product_blocks :
    rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0)
      = min (rlctAtOn blockG 0) (rlctAtOn blockH 0) := by
  sorry

/-- **The `(2,1,2)` headline** (target: axiom-clean modulo the named sorries above). The local RLCT
of the deep-linear `(2,1,2)` loss at the deepest point of the `B = 0` fibre equals Aoyagi's closed
form `aoyagiLambda (2,1,2) 0 = 1`. Assembled: loss = `G·H` (`rlctAtOn_case212_eq_product`) ⟹ `min`
(`rlctAtOn_product_blocks`) of the two block RLCTs (`= 1` each) `= min(1,1) = 1 = aoyagiLambda`. -/
theorem case212_rlct :
    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
      = ENNReal.ofReal (aoyagiLambda (![2, 1, 2] : Fin 3 → ℕ) 0) := by
  rw [rlctAtOn_case212_eq_product, rlctAtOn_product_blocks,
    rlctAtOn_blockG_eq_one, rlctAtOn_blockH_eq_one]
  -- min(1,1) = 1 = ofReal(aoyagiLambda (2,1,2) 0)
  sorry

end DLNFibre.DLN.RLCT
