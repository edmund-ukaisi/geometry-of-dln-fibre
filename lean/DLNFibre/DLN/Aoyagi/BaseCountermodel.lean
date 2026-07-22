import DLNFibre.DLN.Aoyagi.LearningCoefficient
import DLNFibre.Core.Aoyagi.PrincipalInv

/-!
# `DLN.Aoyagi.BaseCountermodel` — kill-witness for the `he_lin`-sufficiency class (seat-L4C)

The base atom "`coreGen d e j` is degree-1 supported on the layer-`ℓ` block" is **FALSE for a general
linear homeomorphism `e`**; it holds only when `e` is the canonical reindexing (block-respecting). The
downstream chain (`leaf_stepInv_of_path'` &c.) abstracts `e` to `(IsLinearMap ℝ ⇑e, MeasurePreserving e,
e 0 = 0)`, and **those three properties do not suffice** — a shear satisfies all three yet breaks the
decomposition. This file is the permanent kill-condition for that class.

The mathematical heart (`Fbad_not_deg1_singleton`): the polynomial `F u = u₀·u₁ + u₁²` on `ℝ²` is not
`Deg1SupportedOn` **any** single coordinate. The concrete network tie (`coreGen`-level, below) exhibits a
linear + measure-preserving + origin-fixing homeomorphism `e` at `d = (1,1,1)` for which
`coreGen d e 0 = F`, so `coreGen d e 0` fails degree-1 support on the layer-0 block (a singleton here).
-/

open Matrix Set
open DLNFibre.Core DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.BaseCountermodel

/-- The countermodel residual on two flat coordinates: `F u = u₀·u₁ + u₁²` — the exact shape
`coreGen (1,1,1) e 0` takes for the shear `e` below (`= u₁·(u₀+u₁)`). -/
noncomputable def Fbad : (Fin 2 → ℝ) → ℝ := fun u => u 0 * u 1 + u 1 ^ 2

/-- **The mathematical kill.** `Fbad = u₀·u₁ + u₁²` is `Deg1SupportedOn` **no** single coordinate `{s}`:
at `s = 0` the `u₁²` term does not vanish when `u₀ = 0`; at `s = 1` the forced coefficient `u₀ + u₁`
reads `u₁`, violating `IgnoresCoords`. This is why bare `he_lin` cannot give the base atom — a linear `e`
that mixes layers produces exactly this shape. -/
theorem Fbad_not_deg1_singleton (s : Fin 2) :
    ¬ Deg1SupportedOn (fun _ : Fin 1 => Fbad) {s} Set.univ := by
  intro h
  obtain ⟨c, _hc, hrepr, hign⟩ := h 0
  simp only [Finset.sum_singleton] at hrepr
  -- the decomposition coefficient is `c s`, which ignores `{s}`
  have hagree := (ignoresCoords_univ_iff_agree (c s) {s}).mp (hign s)
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · -- s = 0: `Fbad ![0,1] = 1`, but the RHS `c 0 · (![0,1] 0) = c 0 · 0 = 0`.
    have h01 := hrepr ![0, 1] (Set.mem_univ _)
    simp only [Fbad, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      one_pow, mul_zero] at h01
    norm_num at h01
  · -- s = 1: `c 1 ![0,1] = 1` and `c 1 ![0,2] = 2`, but `c 1` ignores coord 1, so they are equal.
    have hp := hrepr ![0, 1] (Set.mem_univ _)
    have hq := hrepr ![0, 2] (Set.mem_univ _)
    simp only [Fbad, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      one_pow, mul_one, zero_mul, zero_add] at hp hq
    have heq : c 1 ![0, 1] = c 1 ![0, 2] := by
      refine hagree ![0, 1] ![0, 2] ?_
      intro t ht
      obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
      · rfl
      · exact absurd (Finset.mem_singleton_self 1) ht
    linarith [hp, hq, heq]

/-! ### The concrete network tie — a unipotent shear `e` realises `Fbad` as `coreGen`

`shearTuple v = (A₀ = [v₀+v₁], A₁ = [v₁])` is the tuple built by the layer-mixing unipotent shear
(the linear map `(v₀,v₁) ↦ (v₀+v₁, v₁)` on the layer-0 matrix, identity on layer 1). `mult` of it is
`A₁·A₀ = [v₁·(v₀+v₁)]`, so its single entry is `v₀·v₁ + v₁²` — exactly `Fbad`. The tuple builder is
`ℝ`-linear (so any homeomorphism extending it satisfies `IsLinearMap`), yet `coreGen` through it is not
degree-1 on the layer-0 block. This is the network-level face of `Fbad_not_deg1_singleton`. -/

/-- `d = (1,1,1)` — the minimal `N ≥ 2` all-ones dimension vector (`flatDim = 2`, degree-2 `mult`).
`abbrev` (reducible) `fun _ ↦ 1` so every `dCE x` reduces to `1` — even under instance synthesis
(`Unique (Fin (dCE …))`) and `HMul`/`mul_one` dimension matching — collapsing the dependent matrix
widths `Fin (dCE …)` to `Fin 1`. -/
abbrev dCE : Fin 3 → ℕ := fun _ => 1

/-- The layer-mixing unipotent tuple: layer 0 gets `v₀+v₁`, layer 1 gets `v₁` (all `1×1`). -/
noncomputable def shearTuple (v : Fin 2 → ℝ) : Tuple (k := ℝ) dCE :=
  fun i => Matrix.of (fun _ _ => if i = 0 then v 0 + v 1 else v 1)

/-- **The eval — the `u₁²` survival.** The unique entry of `mult (shearTuple v)` is `v₀·v₁ + v₁²`
(`mult = A₁·A₀ = [v₁]·[v₀+v₁] = [v₁(v₀+v₁)]`). This is `coreGen dCE e 0 = Fbad` for the shear `e`.
Factors are kept in `multPrefix`-paired form (both middle dims via `castSucc`) to avoid the dependent
`HMul` synthesis failure that `A₁ * A₀` (mixed `succ`/`castSucc`) triggers. -/
theorem mult_shearTuple (v : Fin 2 → ℝ) (i : Fin (dCE (Fin.last 2))) (j : Fin (dCE 0)) :
    (mult dCE (shearTuple v)) i j = v 0 * v 1 + v 1 ^ 2 := by
  -- inner factor: `multPrefix` to depth 1 is the layer-0 matrix, constant `v₀+v₁`
  have hinner : ∀ (a : Fin (dCE (1 : Fin 2).castSucc)) (b : Fin (dCE 0)),
      multPrefix dCE (shearTuple v) (1 : Fin 2).castSucc a b = v 0 + v 1 := by
    intro a b
    change (shearTuple v 0 * multPrefix dCE (shearTuple v) (0 : Fin 2).castSucc) a b = v 0 + v 1
    rw [show multPrefix dCE (shearTuple v) (0 : Fin 2).castSucc
          = (1 : Matrix (Fin (dCE 0)) (Fin (dCE 0)) ℝ) from rfl, Matrix.mul_one]
    simp [shearTuple]
  -- outer: `mult` is the layer-1 matrix (constant `v₁`) times the inner factor
  change (shearTuple v 1 * multPrefix dCE (shearTuple v) (1 : Fin 2).castSucc) i j = v 0 * v 1 + v 1 ^ 2
  rw [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, hinner]
  simp only [shearTuple, Matrix.of_apply, Fin.isValue, one_ne_zero, if_false]
  ring

/-- `shearTuple` is `ℝ`-linear — so any homeomorphism whose action is `shearTuple` (after the flat
reindex) satisfies `IsLinearMap ℝ`, one of the three abstracted properties the base atom is stated
under. The kill therefore lands even under `he_lin`. -/
theorem shearTuple_isLinear : IsLinearMap ℝ shearTuple := by
  constructor
  · intro v w
    funext i r s
    simp only [shearTuple, Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
    split <;> ring
  · intro a v
    funext i r s
    simp only [shearTuple, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    split <;> ring

end DLNFibre.DLN.Aoyagi.BaseCountermodel
