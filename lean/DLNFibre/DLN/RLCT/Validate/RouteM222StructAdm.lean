import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV

/-!
# `RouteM222StructAdm` — the concrete `(2,2,2)` LAYERED anchor for the bridge validate-small

The `(4,4,2,2)` anchor (`RouteM4422Bridge`) is a PURE radial blow-up — it validated the factor-fold
SPINE but NOT the Schur/LDU layer reconstruction. This module pins a genuinely LAYERED small case for
the bridge brick-(a) validation: `M = (2,2,2)`, achiever-style descent path `t = (2,1,1)`.

The widths: `Text = [2,2,1,1]`, `Wext = [2,2,2]`, so the structured decoder's Schur frame at boundary
`s = 1` (chart-slot `k = 0`) has K (1×1), X (1×1), N (1×1), E (1×1) — all NONTRIVIAL blocks, and the
`chainA`/`Cgen` recursion (`C_1 = [[K, KN],[XK, XKN+uE]]`, `A_0 = chainA(N_0)(W_0)(C_1)`) is
non-degenerate. `schurDim = [4, 2]`, `liftDim = [2, 0]`, `N = routeMAmbient = 8`.

* `M222` / `t222` — the layered anchor.
* `structAdm222 : StructAdm M222 t222` — the admissibility bundle (boundary `tDesc 0 = M 0`, the
  per-boundary upper bound, the achiever descent), discharged by in-range `decide` + the out-of-range
  saturation (`Wext`/`Text` are `1` beyond `L`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite arithmetic).
-/

namespace DLNFibre.DLN.RLCT

/-- The `(2,2,2)` dimension vector (`L = 2`). -/
def M222 : Fin 3 → ℕ := ![2, 2, 2]

/-- A LAYERED descent path for `(2,2,2)`: `t = (2,1,1)` (`Text = [2,2,1,1]`), giving the nontrivial
Schur frame `K/X/N/E` (all 1×1) + chainA recursion at boundary 1. -/
def t222 : Fin 3 → ℕ := ![2, 1, 1]

/-- **`StructAdm M222 t222`** — the structured-decoder admissibility for the layered `(2,2,2)` anchor.
In-range boundaries by `decide`; out-of-range (`k ≥ 3`) by the `Wext`/`Text` saturation to `1`. -/
theorem structAdm222 : StructAdm M222 t222 := by
  refine ⟨by decide, ?_, by decide, ?_, ?_⟩
  · intro p
    rcases lt_or_ge p 3 with h | h
    · interval_cases p <;> decide
    · rw [show Wext M222 (p + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)],
          show tDesc M222 t222 (p + 1) = 1 from by simp only [tDesc, Text]; rw [dif_neg (by omega)]]
  · intro k
    rcases lt_or_ge k 3 with h | h
    · interval_cases k <;> decide
    · rw [show Text M222 t222 (k + 2) = 1 from by simp only [Text]; rw [dif_neg (by omega)],
          show Text M222 t222 (k + 1) = 1 from by simp only [Text]; rw [dif_neg (by omega)]]
  · intro k
    rcases lt_or_ge k 3 with h | h
    · interval_cases k <;> decide
    · rw [show Text M222 t222 (k + 2) = 1 from by simp only [Text]; rw [dif_neg (by omega)],
          show Wext M222 (k + 1) = 1 from by rw [Wext]; rw [dif_neg (by omega)]]

/-- `routeMAmbient M222 = 8` (the flat dimension). -/
theorem routeMAmbient_M222 : routeMAmbient M222 = 8 := by decide

/-- `0 < routeMAmbient M222` (the pivot axis exists). -/
theorem hN_M222 : 0 < routeMAmbient M222 := by decide

end DLNFibre.DLN.RLCT
