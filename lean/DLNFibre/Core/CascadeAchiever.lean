import Mathlib.Data.Fintype.Fin

/-!
# `DLNFibre.Core.CascadeAchiever` — the achiever rank pattern `r*` (network-free combinatorics)

The orbit-side rank pattern `r*` of a cascade achiever, defined from the width vector `M` and the exponent
vector `T` ALONE — no `cascadeTuple`, no matrix, no `rankFn`. Pure `Fin`/`ℕ` combinatorics, so it lives in
Core and is imported by BOTH the matrix-side tie (`DLN.RLCT.Validate.CascadeAchiever`, which proves
`rankFn (cascadeTuple M T) = achieverRankPattern M T` on admissible `T`) AND the geometric-codim /
`RouteMBranchRead.realizes_ach` lock (#116-(2), #103) — one shared decl, no duplication.

- `expSurvivor M T` is the running rank `ρ`: `ρ_0 = M_0`, `ρ_{j+1} = T_j` (`Fin.cases`).
- `achieverRankPattern M T i j` is the column-constant completion: `ρ_j` strictly above the diagonal,
  `M_i` on it, `0` below.

The genuine-equality content (that this combinatorial pattern IS the matrix cascade's `rankFn` on admissible
`T`) is the DLN-side theorem; this file is only the independent object it is compared against — keeping the
def in Core is exactly what makes that equality non-vacuous (the RHS pipeline never touches a matrix).
-/

namespace DLNFibre.Core

variable {L : ℕ}

/-- The running rank `ρ` of the achiever, from `(M, T)` alone: `ρ_0 = M_0`, `ρ_{j+1} = T_j`
(`Fin.cases` over `Fin (L+1)`). -/
def expSurvivor (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Fin (L + 1) → ℕ :=
  Fin.cases (M 0) T

@[simp] theorem expSurvivor_zero (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    expSurvivor M T 0 = M 0 := rfl

@[simp] theorem expSurvivor_succ (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (k : Fin L) :
    expSurvivor M T k.succ = T k := by
  simp [expSurvivor]

/-- The orbit-stratum rank pattern `r*` of the achiever, from `(M, T)` ALONE: column-constant value `ρ_j`
strictly above the diagonal, `M_i` on it, `0` below. Independent of `cascadeTuple` — the RHS of the
genuine realizability tie. -/
def achieverRankPattern (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Fin (L + 1) → Fin (L + 1) → ℕ :=
  fun i j => if i < j then expSurvivor M T j else if i = j then M i else 0

end DLNFibre.Core
