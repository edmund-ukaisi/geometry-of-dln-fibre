import DLNFibre.DLN.RLCT.Foundations.Lambda

/-!
# `DLN.RLCT.Foundations.AdmTight` — the TIGHT (running-min) admissible cone (Object E / P6.2 Tier-3)

The correct rank-bounded admissible lattice for the P6.2 realization iso: like `Adm`
(`Foundations.Lambda`) but with each `t⁽ʲ⁾` bounded by the **running minimum** `runMin M j =
min{M⁽¹⁾,…,M⁽ʲ⁺¹⁾}` rather than the loose `admBound = min(M⁰,M¹)`. The loose `Adm` admits degenerate
profiles (`t⁽ʲ⁾ > M⁽ʲ⁺¹⁾`) that spuriously tie the minimum and over-count; `admTight` removes them
(P6.2 finding, elder-ratified). Defined as `Adm` filtered by the running-min bound, so the inclusion
is definitional.

Def-site + inclusion + nonemptiness + the clamp-membership are PROVED; `minAdm_tight_eq` is proved
modulo the one engine lemma `Mval_clamp_le` (TRACKED-OPEN, admissible-cone clamp monotonicity).

**The two def-site lemmas (named once, cited forever — elder pin):**
* `admTight_subset_adm` — the inclusion (`Finset.filter_subset`).
* `minAdm_tight_eq` — **THE SEAM LEMMA**: the tight lattice's `Mval`-minimum equals the loose
  `Adm` minimum (hence `minAdm`). This keeps every banked loose-`minAdm` fact
  (`minAdm_le_terminalExponents`, `o5_core_realized`, the `RecursionAdapter` chain) consumable
  against tight-side objects without re-proving. Proof: the loose min lower-bounds the tight min
  (`inf'_mono`, subset), and clamping any `Adm` profile down to `runMin` never raises `Mval`
  (`Mval_clamp_le`) and lands in `admTight`, so the tight min ≤ the loose min.
-/

namespace DLNFibre.DLN.RLCT

open Finset

variable {L : ℕ}

/-- The **tight admissible cone**: `Adm` profiles additionally bounded by the running minimum
`runMin M j` at each coordinate. Equivalently `{t⁽¹⁾ ≥ … ≥ t⁽ᴸ⁾ = 0 : ∀ j, t⁽ʲ⁾ ≤ runMin M j}`
(the loose `admBound` bound is implied since `runMin ≤ admBound`). -/
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
makes the `runMin`-tightening `admTight` **vacuous** (`admTight M = Adm M`); see `Mval_clamp_le`. -/
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

/-- **Clamp does not raise `Mval`** (on the admissible cone): clamping an `Adm` profile down to the
running-min bound coordinatewise never increases `Mval`. In fact the clamp is the **identity** on
`Adm` — every admissible profile already satisfies `T⁽ʲ⁾ ≤ runMin M j` (`Adm_le_runMin`), so
`min (T j) (runMin M j) = T j` and `Mval` is unchanged. (The `T ∈ Adm M` hypothesis is necessary:
unconditionally the inequality is FALSE, e.g. `M=(0,2)`, `T=(1)` gives `Mval T = −1 < 0`.) -/
theorem Mval_clamp_le (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm M) :
    Mval M (fun j => min (T j) (runMin M j)) ≤ Mval M T :=
  le_of_eq (congrArg (Mval M) (funext fun j => min_eq_left (Adm_le_runMin M hT j)))

/-- The clamp of a profile lands in `admTight` (running-min bound + weak-decrease + last `= 0`). -/
theorem clamp_mem_admTight (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm M) :
    (fun j => min (T j) (runMin M j)) ∈ admTight M := by
  rw [Adm, mem_filter] at hT
  obtain ⟨-, -, hdec, hlast⟩ := hT
  rw [admTight, mem_filter]
  refine ⟨?_, fun j => min_le_right _ _⟩
  rw [Adm, mem_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]; intro j; rw [mem_range]
    exact Nat.lt_succ_of_le (le_trans (min_le_right _ _) (runMin_le_admBound M j))
  · intro j; exact le_trans (min_le_right _ _) (runMin_le_admBound M j)
  · intro i j hij; exact min_le_min (hdec i j hij) (runMin_anti M hij)
  · intro j hj; simp only [hlast j hj, Nat.zero_min]

/-- **THE SEAM LEMMA**: the tight cone's `Mval`-minimum equals the loose `Adm` minimum. -/
theorem minAdm_tight_eq (M : Fin (L + 1) → ℕ) :
    (admTight M).inf' (admTight_nonempty M) (Mval M)
      = (Adm M).inf' (Adm_nonempty M) (Mval M) := by
  apply le_antisymm
  · -- tight ≤ loose: clamp the loose minimiser into the tight cone, Mval not raised
    obtain ⟨T, hT, hTeq⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
    rw [hTeq]
    calc (admTight M).inf' (admTight_nonempty M) (Mval M)
        ≤ Mval M (fun j => min (T j) (runMin M j)) :=
          Finset.inf'_le _ (clamp_mem_admTight M hT)
      _ ≤ Mval M T := Mval_clamp_le M hT
  · -- loose ≤ tight: fewer profiles ⟹ larger inf (every tight profile is in `Adm`)
    apply Finset.le_inf'
    intro b hb
    exact Finset.inf'_le _ (admTight_subset_adm M hb)

end DLNFibre.DLN.RLCT
