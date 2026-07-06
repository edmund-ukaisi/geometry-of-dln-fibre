import DLNFibre.Core.Analysis.RLCT.SumSq
import DLNFibre.Core.Analysis.RLCT.RegularPoint
import DLNFibre.Core.Analysis.RLCT.GlobalBridge

/-!
# `RLCT.GlobalWitness` — A: the global-RLCT validation witness `rlctGlobal (sumSq C) = C/2`

The **cite-free validation** that the polymorphic global RLCT `RLCT.Global.rlctGlobal` computes the
right value on the canonical germ: for the sum-of-squares kernel `Q = ∑ i, (y i)^2` on `ℝ^C`
(`C ≥ 1`),

`RLCT.Global.rlctGlobal (sumSq C) = C / 2`.

This exercises the global machinery *non-vacuously* — the value comes out equal to the local
`rlctAt (sumSq C) 0 = C/2` (`RLCT.rlctAt_sumSq`), matching the paper's Prop 8.3(iii) shape
(`rlct(F) = inf` over the zero locus; here the only zero is the origin, so global = local at `0`).

## Route

The global admissible set of `sumSq C` is `Set.Ico 0 (C/2)`:

* **at `0`** — `mem_localAdmissibleExponents_sumSq` (`RLCT.SumSq`) says local admissibility at `0`
  is `0 ≤ c ∧ 2c < C`, i.e. `c < C/2`, so global admissibility forces `c ∈ Ico 0 (C/2)` (a globally
  admissible `c` is locally admissible at every point, in particular at `0`);
* **at `x ≠ 0`** — `sumSq C x ≠ 0` (a sum of squares vanishes only at `0`), and `sumSq C` is
  continuous and nonnegative, so the **regular-point lemma**
  `mem_localAdmissibleExponents_of_ne_zero` (A1, `RLCT.RegularPoint`) makes *every* `c ≥ 0` locally
  admissible at `x` — no constraint.

So the pole at `0` alone governs the global set; `rlctGlobal = sSup (Ico 0 (C/2)) = C/2`
(`csSup_Ico`). The bridge B1 (`global_localAdmissibleExponents_eq`) identifies the polymorphic
global-side local admissible set with the zeta-side one, so `mem_localAdmissibleExponents_sumSq`
(stated on the zeta-side) applies.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology

namespace RLCT

variable {C : ℕ}

/-- `sumSq C` is continuous (a finite sum of the continuous squared coordinates). -/
lemma continuous_sumSq : Continuous (sumSq C) := by
  unfold sumSq
  exact continuous_finset_sum _ (fun i _ ↦ (continuous_apply i).pow 2)

/-- The sum-of-squares kernel vanishes only at the origin: `∑ (y i)^2 = 0 ↔ y = 0` (each summand is
nonnegative, so the sum is `0` iff every coordinate is `0`). -/
lemma sumSq_eq_zero_iff {y : Fin C → ℝ} : sumSq C y = 0 ↔ y = 0 := by
  rw [sumSq, Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by positivity)]
  constructor
  · intro h; funext i; have := h i (Finset.mem_univ i); simpa [pow_eq_zero_iff] using this
  · rintro rfl i _; simp

/-- **A — the global-RLCT validation witness.** The global admissible set of the sum-of-squares
kernel is `Set.Ico 0 (C/2)` (`C ≥ 1`): the origin's pole (`c < C/2`) is the sole constraint; every
other point is regular (A1) and imposes none. -/
theorem globalAdmissibleExponents_sumSq (hC : 1 ≤ C) :
    RLCT.Global.globalAdmissibleExponents (sumSq C) = Set.Ico 0 ((C : ℝ) / 2) := by
  ext c
  rw [RLCT.Global.mem_globalAdmissibleExponents, Set.mem_Ico]
  constructor
  · -- Globally admissible ⟹ locally admissible at `0` ⟹ `0 ≤ c ∧ 2c < C` ⟹ `c ∈ Ico 0 (C/2)`.
    rintro ⟨hc0, hall⟩
    have hloc : c ∈ RLCT.localAdmissibleExponents (sumSq C) 0 := by
      rw [← global_localAdmissibleExponents_eq]
      exact ⟨hc0, hall 0⟩
    obtain ⟨hc0', hlt⟩ := (mem_localAdmissibleExponents_sumSq hC).1 hloc
    exact ⟨hc0', by linarith⟩
  · -- `c ∈ Ico 0 (C/2)` ⟹ globally admissible: at `0` from the pole bound, elsewhere from A1.
    rintro ⟨hc0, hlt⟩
    refine ⟨hc0, fun x ↦ ?_⟩
    by_cases hx : x = 0
    · -- At the origin: `2c < C`, so `c` is locally admissible there.
      subst hx
      have : c ∈ RLCT.localAdmissibleExponents (sumSq C) 0 :=
        (mem_localAdmissibleExponents_sumSq hC).2 ⟨hc0, by linarith⟩
      rw [← global_localAdmissibleExponents_eq] at this
      exact this.2
    · -- At a regular point `x ≠ 0`: `sumSq C x ≠ 0`, so every `c ≥ 0` is locally admissible (A1).
      have hne : sumSq C x ≠ 0 := fun h ↦ hx (sumSq_eq_zero_iff.1 h)
      have : c ∈ RLCT.localAdmissibleExponents (sumSq C) x :=
        mem_localAdmissibleExponents_of_ne_zero continuous_sumSq hne hc0
      rw [← global_localAdmissibleExponents_eq] at this
      exact this.2

/-- **The sum-of-squares global RLCT: `rlctGlobal (sumSq C) = C/2`** (`C ≥ 1`), cite-free. Validates
the polymorphic `RLCT.Global.rlctGlobal` against the canonical germ — the value agrees with the
local `rlctAt (sumSq C) 0 = C/2`, instantiating the Prop 8.3(iii) inf-over-zeros shape (single zero
at `0`). -/
theorem rlctGlobal_sumSq (hC : 1 ≤ C) : RLCT.Global.rlctGlobal (sumSq C) = (C : ℝ) / 2 := by
  have hCpos : (0 : ℝ) < (C : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    linarith
  rw [RLCT.Global.rlctGlobal_def, globalAdmissibleExponents_sumSq hC, csSup_Ico hCpos]

end RLCT
