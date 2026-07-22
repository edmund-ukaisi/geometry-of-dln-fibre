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

end DLNFibre.DLN.Aoyagi.BaseCountermodel
