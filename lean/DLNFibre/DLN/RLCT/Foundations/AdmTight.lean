import DLNFibre.DLN.RLCT.Foundations.Lambda

/-!
# `DLN.RLCT.Foundations.AdmTight` — the run-min bound is free on `Adm` (Object E / P6.2)

The "tight" (running-min-bounded) admissible cone the P6.2 realization iso appeared to need turns
out NOT to be a distinct object: every `Adm` profile (`Foundations.Lambda`) **already** satisfies
the running-min bound `t⁽ʲ⁾ ≤ runMin M j = min(M⁰,…,M⁽ʲ⁺¹⁾)` (`Adm_le_runMin`). So filtering `Adm`
by it changes nothing (`adm_runMin_filter_eq`) — the run-min tightening is vacuous, and the elder's
Q4 ruling collapsed the former `admTight` def into `Adm` (two names for one proven-equal set is the
over-naming `name = content` forbids). What survives is the *theorem* `adm_runMin_filter_eq`, which
carries the tight-vs-loose story (the negative certificate); a one-line pointer sits at `Adm`'s
def-site (`Lambda.lean`).
-/

namespace DLNFibre.DLN.RLCT

open Finset

variable {L : ℕ}

/-- **The running-min bound is automatic on the admissible cone**: every `Adm` profile already
satisfies `T⁽ʲ⁾ ≤ runMin M j = min(M⁰,…,M⁽ʲ⁺¹⁾)`. Reason: weak-decrease plus the per-coordinate
`admBound` (`T⁽ʲ⁾ ≤ admBound M j ≤ M⁽ʲ⁺¹⁾`, and `T⁰ ≤ min(M⁰,M¹)`) force `T⁽ʲ⁾ ≤ M⁽ⁱ⁾` for every
`i ≤ j+1`. Verified exhaustively (0/61014 admissible profiles violate it, L≤4, widths 0..5). -/
theorem Adm_le_runMin (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm M) (j : Fin L) :
    T j ≤ runMin M j := by
  rw [Adm, mem_filter] at hT
  obtain ⟨-, hbound, hdec, -⟩ := hT
  unfold runMin
  apply Finset.le_inf'
  intro i hi
  rw [Finset.mem_Iic] at hi
  have hiv : i.val ≤ j.val + 1 := by rw [Fin.le_def, Fin.val_succ] at hi; exact hi
  rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
  · -- `i = 0`: `T j ≤ T⁰ ≤ min(M⁰,M¹) ≤ M⁰ = M i`
    have hi_eq : i = (0 : Fin (L + 1)) := Fin.ext (by rw [Fin.val_zero]; exact hi0)
    set z : Fin L := ⟨0, by have := j.isLt; omega⟩ with hz
    have hb0 := hbound z
    unfold admBound at hb0
    rw [if_pos rfl] at hb0
    rw [hi_eq]
    calc T j ≤ T z := hdec z j (by rw [Fin.le_def]; exact Nat.zero_le _)
      _ ≤ min (M 0) (M 1) := hb0
      _ ≤ M 0 := min_le_left _ _
  · -- `i ≥ 1`: `T j ≤ T⁽ⁱ⁻¹⁾ ≤ admBound ≤ M⁽ⁱ⁾`
    set i' : Fin L := ⟨i.val - 1, by have := j.isLt; omega⟩ with hi'
    have hi'succ : i'.succ = i :=
      Fin.ext (by rw [Fin.val_succ]; show (i.val - 1) + 1 = i.val; omega)
    calc T j ≤ T i' := hdec i' j (by rw [Fin.le_def]; show i.val - 1 ≤ j.val; omega)
      _ ≤ admBound M i' := hbound i'
      _ ≤ M i'.succ := admBound_le_Msucc M i'
      _ = M i := by rw [hi'succ]

/-- **The run-min tightening is vacuous on `Adm`** (formerly `adm_eq_admTight`; the `admTight` def
collapsed to `Adm` per the elder's Q4 ruling — `admTight` was a *theorem* about `Adm`, not a
distinct object): filtering `Adm` by the running-min bound is the identity. This theorem *is* the
tight-vs-loose story.

**Negative certificate (why the `M⁽ʲ⁺¹⁾`/run-min cap matters even though it is free here).** `Adm`
is NOT loose: `admBound M j ≤ M⁽ʲ⁺¹⁾` already caps each `t⁽ʲ⁾`, and weak-decrease reconstructs the
running min (`Adm_le_runMin`), so no spurious binding profile arises. The genuinely-loose object is
the **over-loose** lattice — cap `min(M⁰,M¹)` at *every* coordinate, dropping the `M⁽ʲ⁺¹⁾` cap.
There `t⁽ʲ⁾` can exceed `M⁽ʲ⁺¹⁾`, the factor `(M⁽ʲ⁺¹⁾ − t⁽ʲ⁾)` goes negative, and `minAdm` collapses
≤ 0 (`M=[4,4,1,1]→0`, `[5,5,1,1]→−1`), destroying the `C(ℓ,a)` count of the P6.2 realization iso.
The `M⁽ʲ⁺¹⁾`/run-min cap is load-bearing vs that object; Lambda's `admBound` supplies it, so `Adm`
is safe (pnp thread-42 negative cert). -/
theorem adm_runMin_filter_eq (M : Fin (L + 1) → ℕ) :
    (Adm M).filter (fun T => ∀ j, T j ≤ runMin M j) = Adm M :=
  Finset.filter_true_of_mem (fun _ hT j => Adm_le_runMin M hT j)

end DLNFibre.DLN.RLCT
