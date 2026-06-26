import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

/-!
# `DLNFibre.DLN.RLCT.Foundations.Lambda` — Aoyagi's closed-form learning coefficient

The candidate value `Mval`, the admissible cone `Adm`, the core `lambdaCore = ½·min_T M(T)`,
the closed form `aoyagiLambda`, and the order `aoyagiTheta = a(ℓ−a)+1` (design-spec §4).

`aoyagiLambda` is defined **via the minimisation** `½·min_{T ∈ Adm} M(T)` — total and
Def-3-free (controller standing decision 3; the printed Theorem-2 form and the clean form are
proven equal where Def 3 applies, as the A1 lemmas). The naive "extremise the clean form over
ℓ" is WRONG: `min_ℓ` can go negative (`M=(1,1,1,4)` → −1/2) and `max_ℓ` mis-selects
(`M=(2,2,2)`: Def-3 ℓ=2 → 3/2, `max_ℓ` ℓ=1 → 2); verified in the design spec §4.3. The
minimisation is the faithful total object; the clean form is its *value* at the genuine minimiser.

Spelled with Lean-safe names (`λ` is reserved): `aoyagiLambda` is Aoyagi's `λ`, `aoyagiTheta`
his `θ`.

Ground truth (design-spec §5), enforced by the `#guard_msgs`/`#eval` checks below:
`(2,2,2)→3/2`, `(2,1,2)→1`, `(2,2,2,2)→3/2`, `(3,3,3,3)→3`.
-/

namespace DLNFibre.DLN.RLCT

open Finset

variable {L : ℕ}

/-- `t⁽ʲ⁻¹⁾` with the convention `t⁽⁰⁾ := M⁽¹⁾ = M 0` (which unifies the first term of `M(T)`
with the sum; design-spec §4.1). For `j : Fin L` the predecessor exponent. -/
def tPrev (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (j : Fin L) : ℤ :=
  if j.val = 0 then (M 0 : ℤ) else (T ⟨j.val - 1, by omega⟩ : ℤ)

/-- Aoyagi's candidate RLCT-contribution value (design-spec §4.1, transcribed from Aoyagi p.22):
`M(T) = (M⁽¹⁾−t⁽¹⁾)(M⁽²⁾−t⁽¹⁾) + ∑_{j=2}^L (t⁽ʲ⁻¹⁾−t⁽ʲ⁾)(M⁽ʲ⁺¹⁾−t⁽ʲ⁾)`, written as the single sum
`∑_{j=1}^L (t⁽ʲ⁻¹⁾−t⁽ʲ⁾)(M⁽ʲ⁺¹⁾−t⁽ʲ⁾)` with `t⁽⁰⁾ := M⁽¹⁾`. Over ℤ (the factors are signed). -/
def Mval (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : ℤ :=
  ∑ j : Fin L, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ))

/-- Per-layer upper bound on `t⁽ʲ⁾`: `min(M⁽¹⁾,M⁽²⁾)` for `j = 1`, else `M⁽ʲ⁺¹⁾`
(design-spec §4.1). -/
def admBound (M : Fin (L + 1) → ℕ) (j : Fin L) : ℕ :=
  if j.val = 0 then min (M 0) (M 1) else M j.succ

/-- Admissibility (design-spec §4.1): weak-decrease `t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾`, last exponent `t⁽ᴸ⁾ = 0`, and
each `t⁽ʲ⁾` within its block bound. The genuine admissible cone the blow-up realises. -/
def admPred (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Prop :=
  (∀ j : Fin L, T j ≤ admBound M j) ∧
  (∀ i j : Fin L, i ≤ j → T j ≤ T i) ∧
  (∀ j : Fin L, j.val = L - 1 → T j = 0)

instance (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Decidable (admPred M T) := by
  unfold admPred; infer_instance

/-- The finite admissible cone of exponent vectors `T` (design-spec §4.1). Finite because each
`t⁽ʲ⁾` ranges over `0..admBound`, so `min_T M(T)` exists unconditionally — making `aoyagiLambda`
total. -/
def Adm (M : Fin (L + 1) → ℕ) : Finset (Fin L → ℕ) :=
  (Fintype.piFinset (fun j => Finset.range (admBound M j + 1))).filter (admPred M)

/-- The all-zeros exponent vector is admissible (so `Adm` is nonempty). -/
theorem zero_mem_Adm (M : Fin (L + 1) → ℕ) : (fun _ => 0) ∈ Adm M := by
  rw [Adm, mem_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [mem_range]; omega
  · intro j; exact Nat.zero_le _
  · intro i j _; exact le_refl 0
  · intro j _; rfl

/-- `Adm M` is nonempty (the all-zeros vector witnesses it; design-spec §4.2). -/
theorem Adm_nonempty (M : Fin (L + 1) → ℕ) : (Adm M).Nonempty :=
  ⟨_, zero_mem_Adm M⟩

/-- `λ_core = ½·min_{T ∈ Adm} M(T)` (design-spec §4.2). Total via `Finset.inf'` over the nonempty
finite `Adm M`; the clean closed form `¼(Σqᵢ² − Σmₖ²)` is proven equal as A1, not baked in here. -/
def lambdaCore (M : Fin (L + 1) → ℕ) : ℚ :=
  (1 / 2 : ℚ) * ((Adm M).inf' (Adm_nonempty M) (Mval M) : ℤ)

/-- Aoyagi's learning coefficient `λ = [−r² + r(H⁽¹⁾+H⁽ᴸ⁺¹⁾)]/2 + λ_core` (design-spec §4.2), the
regular-part shift plus the singular-core minimisation over the reduced widths `M⁽ˢ⁾ = H⁽ˢ⁾ − r`.
Total and Def-3-free. (`λ` is reserved in Lean; this is Aoyagi's `λ`.) -/
def aoyagiLambda (H : Fin (L + 1) → ℕ) (r : ℕ) : ℚ :=
  (-(r : ℚ) ^ 2 + r * (H 0 + H (Fin.last L))) / 2 + lambdaCore (fun s => H s - r)

/-- Aoyagi's order `θ = a(ℓ−a)+1` (design-spec §3; Aoyagi Theorem 2). The combinatorial
deliverable, total in the Def-3 data `(ℓ, a)`. The binding of `(ℓ, a)` to `(H, r)` rides with
Def-3 (A2); θ is **not** the naive count of minimisers of `M(T)` (design-spec §3 seam). -/
def aoyagiTheta (ℓ a : ℕ) : ℕ := a * (ℓ - a) + 1

-- Ground-truth cross-check (design-spec §5; all reproduce exactly, enforced at build time).
/-- info: 3 / 2 -/
#guard_msgs in
#eval aoyagiLambda (![2, 2, 2] : Fin 3 → ℕ) 0
/-- info: 1 -/
#guard_msgs in
#eval aoyagiLambda (![2, 1, 2] : Fin 3 → ℕ) 0
/-- info: 3 / 2 -/
#guard_msgs in
#eval aoyagiLambda (![2, 2, 2, 2] : Fin 4 → ℕ) 0
/-- info: 3 -/
#guard_msgs in
#eval aoyagiLambda (![3, 3, 3, 3] : Fin 4 → ℕ) 0
/-- info: 2 -/
#guard_msgs in
#eval aoyagiTheta 2 1

end DLNFibre.DLN.RLCT
