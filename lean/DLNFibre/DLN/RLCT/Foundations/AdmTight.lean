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

/-- **Clamp does not raise `Mval`** (on the admissible cone): clamping an `Adm` profile down to
the running-min bound coordinatewise never increases `Mval`. TRACKED-OPEN — the seam lemma's
engine (the coupled `Mval`-summand analysis under a simultaneous coordinate clamp). The
`T ∈ Adm M` hypothesis is NECESSARY: unconditionally the inequality is FALSE (e.g. `M=(0,2)`,
`T=(1)`: `Mval T = −1` but `Mval (clamp) = 0`); it holds exactly on the weak-decreasing/last-zero
cone — verified 2540/2540 over `Adm` (L≤3, widths 0..4, T 0..4), 11199/81375 fails without
admissibility. `minAdm_tight_eq` is proved modulo this one lemma. -/
theorem Mval_clamp_le (M : Fin (L + 1) → ℕ) {T : Fin L → ℕ} (hT : T ∈ Adm M) :
    Mval M (fun j => min (T j) (runMin M j)) ≤ Mval M T := by
  sorry

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
