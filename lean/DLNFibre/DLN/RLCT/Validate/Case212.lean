import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1ProductMin
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat

/-!
# `DLNFibre.DLN.RLCT.Validate.Case212` — the `(2,1,2)` headline via product-MIN (axiom-clean)

The second ladder rung. `M = (2,1,2)`, `r = 0`: the core is `C⁽¹⁾` (`2×1`, entries `a₁,a₂`) times
`C⁽²⁾` (`1×2`, entries `b₁,b₂`), product `P_ij = aᵢbⱼ`, and

  `dlnLoss (2,1,2) 0 A = ‖P‖² = Σ_ij (aᵢbⱼ)² = (a₁²+a₂²)(b₁²+b₂²) = G(a)·H(b)`

a **product of two disjoint smooth blocks** (`dlnLoss_case212`). So the RLCT is `min` (NOT sum —
`product_min_rlct_of_ne`, the Tonelli split), each block `= 1` (`smoothBlockND_rlct 1`), giving
`min(1,1) = 1 = aoyagiLambda (2,1,2) 0`.

**Fully closed and axiom-free**: `case212_rlct` has `#print axioms = [propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `native_decide`. The pieces, all sorry-free:
- `dlnLoss_case212`: the entrywise product form (dependent-`Fin` `prod` unfold for `L = 2`);
- `eME212`/`eHom212`: the measure-preserving homeomorph `Params (2,1,2) ≃ₜ (Fin 2→ℝ)×(Fin 2→ℝ)` (the
  `a`-block × `b`-block flatten), built from generic coordinate-reindex equivs (`piFinTwo`,
  `arrowCongr'·funUnique`, `funUnique`) — never computing `paramsEquivFlat`'s opaque `equivFin`
  order — transporting `dlnLoss` to `blockG·blockH` via `rlctAtOn_comp_homeomorph`;
- `rlctAtOn_blockG_eq_one`: the `EuclideanSpace ℝ (Fin 2)` ↔ `Fin 2 → ℝ` bridge for
  `smoothBlockND_rlct`;
- `rlctAtOn_product_blocks`: the `product_min_rlct_of_ne` (#57) discharge (`block_ne_ae`).

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
index `⟨0,_⟩ : Fin 1`). `prodAux` for `L = 2` telescopes `(1·C⁽¹⁾)·C⁽²⁾`. Closer: `mul_apply` +
`eq_mpr_eq_cast` exposes the base factor's `prodAux` `Fin`-cast as an explicit `cast`; a `simp only`
of the `Matrix.cons_val`/`Fin` reduction set collapses the `Fin 1` inner sum and discharges the
casts (`cast_eq`), leaving `(1 * A 0) i 0 * A 1 0 j = A 0 i 0 * A 1 0 j`; `congr 1` peels the shared
`A 1` factor and `convert (Matrix.one_mul …)` clears the residual `1 *` whose `HMul` instance still
carries the un-reduced contraction-dim type (so `rw`/`simp only [one_mul]` cannot match it). -/
theorem prod212_entry (A : Params (![2, 1, 2] : Fin 3 → ℕ)) (i j : Fin 2) :
    prod (![2, 1, 2] : Fin 3 → ℕ) A i j
      = A 0 i ⟨0, by norm_num⟩ * A 1 ⟨0, by norm_num⟩ j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    Finset.univ_unique, Fin.default_eq_zero, Fin.zero_eta, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    cast_eq, Fin.castSucc_one, Fin.reduceFinMk, Matrix.cons_val, Fin.succ_one_eq_two,
    Finset.sum_singleton]
  congr 1
  convert congrFun (congrFun (Matrix.one_mul (A 0)) i) 0 using 2

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

/-! ## The coordinate split (the `a`-block × `b`-block flatten)

`Params (2,1,2) = (Fin 2→Fin 1→ℝ) × (Fin 1→Fin 2→ℝ)` (two layers, `2×1` and `1×2`). A FRESH explicit
measure-preserving equiv `eME212` flattens it to `(Fin 2→ℝ) × (Fin 2→ℝ)` — the `a`-block
`aᵢ = A 0 i ⟨0,·⟩` to the first factor, the `b`-block `bⱼ = A 1 ⟨0,·⟩ j` to the second — built from
three generic coordinate-reindex equivs (never computing `paramsEquivFlat`'s opaque `equivFin`
order): `piFinTwo` (split the two layers), `arrowCongr'·funUnique` (collapse the `2×1` layer's inner
`Fin 1`), `funUnique` (collapse the `1×2` layer's outer `Fin 1`). Each is measure-preserving by the
matching Mathlib volume-preserving lemma, so `eME212` is too. -/

/-- The coordinate-split measurable equiv `Params (2,1,2) ≃ᵐ (Fin 2→ℝ) × (Fin 2→ℝ)`: the `2×1`
`a`-block to the first factor (`(eME212 A).1 i = A 0 i ⟨0,·⟩`), the `1×2` `b`-block to the second
(`(eME212 A).2 j = A 1 ⟨0,·⟩ j`). Both forward components are definitional (`rfl`). -/
noncomputable def eME212 : Params (![2, 1, 2] : Fin 3 → ℕ) ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (MeasurableEquiv.piFinTwo (fun s : Fin 2 =>
      (Fin ((![2, 1, 2] : Fin 3 → ℕ) s.castSucc)) →
        (Fin ((![2, 1, 2] : Fin 3 → ℕ) s.succ)) → ℝ)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin 2)) (MeasurableEquiv.funUnique (Fin 1) ℝ))
      (MeasurableEquiv.funUnique (Fin 1) (Fin 2 → ℝ)))

/-- `eME212` is measure-preserving: a `trans` of `piFinTwo` (volume-preserving) and the `prod` of
the two per-layer collapses (`arrowCongr'·funUnique` and `funUnique`, each volume-preserving). -/
theorem measurePreserving_eME212 : MeasurePreserving eME212 volume volume := by
  unfold eME212
  refine (volume_preserving_piFinTwo _).trans ?_
  exact MeasurePreserving.prod
    (volume_preserving_arrowCongr' (Equiv.refl (Fin 2)) (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (measurePreserving_funUnique volume (Fin 1)))
    (measurePreserving_funUnique volume (Fin 1))

/-- `eME212` is continuous: its forward map is `A ↦ (fun i ↦ A 0 i default, fun j ↦ A 1 default j)`,
each output coordinate an evaluation of `A`. -/
theorem continuous_eME212 : Continuous eME212 := by
  have h : (⇑eME212) = (fun A : Params (![2, 1, 2] : Fin 3 → ℕ) =>
      ((fun i => A 0 i (default : Fin 1)), (fun j => A 1 (default : Fin 1) j))) := rfl
  rw [h]; fun_prop

/-- `eME212.symm` is continuous: rebuilding the two layer matrices, each entry a projection of `p`
(`p.1 i` on layer `0`, `p.2 j` on layer `1`). -/
theorem continuous_eME212_symm : Continuous eME212.symm := by
  apply continuous_pi; intro s
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  fin_cases s
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply j).comp continuous_snd

/-- `eME212` as a homeomorphism (the measurable equiv + both continuities), for transporting
`rlctAtOn` via `rlctAtOn_comp_homeomorph`. -/
noncomputable def eHom212 : Params (![2, 1, 2] : Fin 3 → ℕ) ≃ₜ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  { eME212.toEquiv with
    continuous_toFun := continuous_eME212, continuous_invFun := continuous_eME212_symm }

/-- **The coordinate split.** `Params (2,1,2)` is measure-preservingly `(Fin 2→ℝ)×(Fin 2→ℝ)` (the
`a`-block × the `b`-block, via `eHom212`), under which `dlnLoss (2,1,2) 0` transports to
`blockG p.1 · blockH p.2`. The loss-match `dlnLoss = (blockG·blockH) ∘ eHom212` is `dlnLoss_case212`
(entry-product form) + the definitional forward components; `eHom212` is measure-preserving
(`measurePreserving_eME212`); transport via `rlctAtOn_comp_homeomorph` (`S1Fubini`), with
`eHom212 deepest212 = (0,0)`. -/
theorem rlctAtOn_case212_eq_product :
    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
      = rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0) := by
  have hmp : MeasurePreserving eHom212 volume volume := measurePreserving_eME212
  have hemb : MeasurableEmbedding eHom212 := eME212.measurableEmbedding
  have key := rlctAtOn_comp_homeomorph eHom212 hmp hemb
    (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) deepest212
  have he0 : eHom212 deepest212 = (0, 0) := by apply Prod.ext <;> · funext k; rfl
  have hloss : dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0
      = (fun A => (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (eHom212 A)) := by
    funext A; rw [dlnLoss_case212 A]; simp only [blockG, blockH]; rfl
  rw [hloss, key, he0]

/-- **Each block has RLCT 1.** `rlctAtOn blockG 0 = 1` (and likewise `blockH`): `blockG = Σᵢ aᵢ²` on
`Fin 2 → ℝ`, which is `smoothBlockND_rlct 1` (`m = 1`, `n = m+1 = 2`, value `(m+1)/2 = 1`) bridged
across the `EuclideanSpace ℝ (Fin 2) ≃ Fin 2 → ℝ` identification. -/
theorem rlctAtOn_blockG_eq_one : rlctAtOn blockG (0 : Fin 2 → ℝ) = 1 := by
  -- bridge `Fin 2 → ℝ` to `EuclideanSpace ℝ (Fin 2)` via the measure-preserving homeomorph `toLp`
  -- (`PiLp.volume_preserving_toLp`), then `smoothBlockND_rlct 1` gives `(1+1)/2 = 1`.
  set e : (Fin 2 → ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.symm with he
  have hmp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin 2)
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have key := rlctAtOn_comp_homeomorph e hmp hemb
    (fun x : EuclideanSpace ℝ (Fin 2) => ∑ i, x i ^ 2) 0
  have he0 : e 0 = 0 := by simp [he]
  rw [he0, smoothBlockND_rlct 1] at key
  rw [show blockG = (fun w => ∑ i, (e w) i ^ 2) from by funext x; simp [blockG, he]]
  rw [key, show ((1 : ℕ) : ℝ≥0∞) + 1 = 2 by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)]

theorem rlctAtOn_blockH_eq_one : rlctAtOn blockH (0 : Fin 2 → ℝ) = 1 :=
  rlctAtOn_blockG_eq_one

/-- A sum-of-squares block `Σᵢ xᵢ²` vanishes only at the origin, a `volume`-null singleton on
`Fin 2 → ℝ`, so it is nonzero a.e. (the `hGne`/`hHne` input to `product_min_rlct_of_ne`). -/
theorem block_ne_ae : ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), blockG x ≠ 0 := by
  have hz : {x : Fin 2 → ℝ | blockG x = 0} ⊆ {0} := by
    intro x hx
    simp only [Set.mem_setOf_eq, blockG] at hx
    have hi : ∀ i, x i = 0 := fun i => by
      have hnn : ∀ j, (0 : ℝ) ≤ x j ^ 2 := fun j => sq_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 hx i (Finset.mem_univ i)
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    simp only [Set.mem_singleton_iff]; funext i; exact hi i
  exact compl_mem_ae_iff.mpr (measure_mono_null hz (measure_singleton _))

/-- **product-MIN for the two blocks.** `rlctAtOn (G·H)(0,0) = min (rlctAtOn G 0)(rlctAtOn H 0)`
via `product_min_rlct_of_ne` (#57; Tonelli `∫(GH)^{−c} = (∫G^{−c})(∫H^{−c})`, finite ⟺ both ⟺
`c < min`). The a.e.-nonvanishing inputs are `block_ne_ae` (`blockG = blockH` as functions). -/
theorem rlctAtOn_product_blocks :
    rlctAtOn (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => blockG p.1 * blockH p.2) (0, 0)
      = min (rlctAtOn blockG 0) (rlctAtOn blockH 0) := by
  have hGm : Measurable blockG := by unfold blockG; fun_prop
  have hHm : Measurable blockH := by unfold blockH; fun_prop
  exact product_min_rlct_of_ne blockG blockH hGm hHm block_ne_ae block_ne_ae

/-- **The `(2,1,2)` headline** (axiom-clean: `[propext, Classical.choice, Quot.sound]`). The local
RLCT of the deep-linear `(2,1,2)` loss at the deepest point of the `B = 0` fibre equals Aoyagi's
closed form `aoyagiLambda (2,1,2) 0 = 1`. Assembled: loss = `G·H` (`rlctAtOn_case212_eq_product`) ⟹
`min` (`rlctAtOn_product_blocks`) of the block RLCTs (`= 1` each), `min(1,1) = 1 = aoyagiLambda`. -/
theorem case212_rlct :
    rlctAtOn (dlnLoss (![2, 1, 2] : Fin 3 → ℕ) 0) deepest212
      = ENNReal.ofReal (aoyagiLambda (![2, 1, 2] : Fin 3 → ℕ) 0) := by
  rw [rlctAtOn_case212_eq_product, rlctAtOn_product_blocks,
    rlctAtOn_blockG_eq_one, rlctAtOn_blockH_eq_one, min_self]
  -- aoyagiLambda (2,1,2) 0 = 1 (rational, by kernel), so ofReal = 1
  have h1 : aoyagiLambda (![2, 1, 2] : Fin 3 → ℕ) 0 = (1 : ℚ) := by decide +kernel
  rw [h1]; norm_num

end DLNFibre.DLN.RLCT
