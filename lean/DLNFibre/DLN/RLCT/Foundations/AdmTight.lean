import DLNFibre.DLN.RLCT.Foundations.Lambda

/-!
# `DLN.RLCT.Foundations.AdmTight` — the run-min admissible cone equals `Adm` (Object E / P6.2)

The rank-bounded admissible lattice named for the P6.2 realization iso: `Adm`
(`Foundations.Lambda`) with each `t⁽ʲ⁾` additionally bounded by the **running minimum**
`runMin M j = min(M⁰,…,M⁽ʲ⁺¹⁾)`. The headline result is that this run-min bound is **already
implied** on `Adm`, so `admTight = Adm` **as a set** (`adm_eq_admTight`) — a stronger seam than the
value-only minimum-equality the elder asked for.

Why the run-min cap matters even though it is free here: it is the load-bearing constraint that
separates `Adm` from the **over-loose** lattice (`admBound = min(M⁰,M¹)` at *every* coordinate,
dropping the `M⁽ʲ⁺¹⁾` cap). On that over-loose lattice `t⁽ʲ⁾` can exceed `M⁽ʲ⁺¹⁾`, the factor
`(M⁽ʲ⁺¹⁾ − t⁽ʲ⁾)` goes negative, and `minAdm` collapses ≤ 0 (e.g. `M=[4,4,1,1]→0`, `[5,5,1,1]→−1`)
— destroying the `C(ℓ,a)` element count of the P6.2 realization iso. Lambda's `admBound` supplies
the cap (via `admBound M j ≤ M⁽ʲ⁺¹⁾`), which is why `Adm` is safe and the over-loose one is not
(the negative certificate, pnp thread-42). So `Adm` never admits the spurious binding profiles; the
run-min tightening changes nothing on it.

**The def-site lemmas (named once, cited forever):**
* `admTight_subset_adm` — the inclusion (`Finset.filter_subset`).
* `Adm_le_runMin` — the run-min bound is automatic on `Adm` (weak-decrease + `admBound` reconstruct
  the running min by induction).
* `adm_eq_admTight` — **THE SEAM (set identity)**: `admTight M = Adm M`. Makes `minAdm_tight_eq`
  immediate and keeps every banked loose-`minAdm` fact (`minAdm_le_terminalExponents`,
  `o5_core_realized`, the `RecursionAdapter` chain) consumable against the tight-named domain.
* `minAdm_tight_eq` — the tight/loose `Mval`-minimum equality, a corollary of the set identity.
-/

namespace DLNFibre.DLN.RLCT

open Finset

variable {L : ℕ}

/-- The **tight admissible cone**: `Adm` profiles additionally bounded by the running minimum
`runMin M j` at each coordinate. Equivalently `{t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾ = 0 : ∀ j, t⁽ʲ⁾ ≤ runMin M j}`.
The added bound is free on `Adm` (`adm_eq_admTight`); it names the load-bearing run-min cap. -/
def admTight (M : Fin (L + 1) → ℕ) : Finset (Fin L → ℕ) :=
  (Adm M).filter (fun T => ∀ j, T j ≤ runMin M j)

/-- The tight cone is included in the loose one (definitional — it is a filter of `Adm`). -/
theorem admTight_subset_adm (M : Fin (L + 1) → ℕ) : admTight M ⊆ Adm M :=
  Finset.filter_subset _ _

/-- The all-zeros profile is tight-admissible, so `admTight` is nonempty. -/
theorem admTight_nonempty (M : Fin (L + 1) → ℕ) : (admTight M).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [admTight, mem_filter]
  exact ⟨zero_mem_Adm M, fun j => Nat.zero_le _⟩

/-- **The running-min bound is automatic on the admissible cone**: every `Adm` profile already
satisfies `T⁽ʲ⁾ ≤ runMin M j = min(M⁰,…,M⁽ʲ⁺¹⁾)`. Reason: weak-decrease plus the per-coordinate
`admBound` (`T⁽ʲ⁾ ≤ admBound M j ≤ M⁽ʲ⁺¹⁾`, and `T⁰ ≤ min(M⁰,M¹)`) force `T⁽ʲ⁾ ≤ M⁽ⁱ⁾` for every
`i ≤ j+1`. Verified exhaustively (0/61014 admissible profiles violate it, L≤4, widths 0..5). This
is why `admTight M = Adm M` (`adm_eq_admTight`). -/
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

/-- **THE SEAM (set identity)**: `admTight M = Adm M`. The run-min bound of `admTight` is implied
by admissibility (`Adm_le_runMin`), so the filter is total on `Adm`. Stronger than the value-only
minimum-equality: the two lattices are the *same set*. -/
theorem adm_eq_admTight (M : Fin (L + 1) → ℕ) : admTight M = Adm M := by
  refine Finset.Subset.antisymm (admTight_subset_adm M) (fun T hT => ?_)
  rw [admTight, mem_filter]
  exact ⟨hT, fun j => Adm_le_runMin M hT j⟩

/-- The tight cone's `Mval`-minimum equals the loose `Adm` minimum (hence `minAdm`) — a corollary
of the set identity `adm_eq_admTight`. -/
theorem minAdm_tight_eq (M : Fin (L + 1) → ℕ) :
    (admTight M).inf' (admTight_nonempty M) (Mval M)
      = (Adm M).inf' (Adm_nonempty M) (Mval M) :=
  Finset.inf'_congr (admTight_nonempty M) (adm_eq_admTight M) (fun _ _ => rfl)

end DLNFibre.DLN.RLCT
