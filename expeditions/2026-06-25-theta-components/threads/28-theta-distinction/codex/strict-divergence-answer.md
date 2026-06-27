Pick **fixed gap + induction on `a - 2`**. It is cleaner than product/descFactorial routes because Pascal supplies exactly the recurrence, and the only lower bound needed for the new summand is
`g ≤ Nat.choose ((b+2)+g) ((b+2)+1)`, proved by `Nat.choose_symm` + `Nat.choose_le_choose` + `Nat.choose_one_right`. I would also prove the `a = 2` base by a tiny Pascal induction on `g`, avoiding `Nat.choose_two_right` and all `/ 2` arithmetic.

Confident v4.29 lemma names used: `Nat.choose_succ_left`, `Nat.choose_succ_succ'`, `Nat.choose_symm`, `Nat.choose_le_choose`, `Nat.choose_one_right`, `Nat.choose_succ_self_right`, `Nat.exists_eq_add_of_le`, `min_le_iff`, `min_le_left`, `min_le_right`.

```lean
import Mathlib

lemma choose_two_gap_gt (g : ℕ) (hg : 2 ≤ g) :
    2 * g + 1 < Nat.choose (2 + g) 2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hg
  induction t with
  | zero =>
      norm_num [Nat.choose_succ_succ, Nat.choose]
  | succ t ih =>
      rw [show 2 + (2 + (t + 1)) = (2 + (2 + t)) + 1 by omega,
          Nat.choose_succ_left (2 + (2 + t)) 2 (by norm_num)]
      norm_num [Nat.choose_one_right] at *
      omega

lemma choose_add_gap_gt_aux (b g : ℕ) (hg : 2 ≤ g) :
    (b + 2) * g + 1 < Nat.choose ((b + 2) + g) (b + 2) := by
  induction b with
  | zero =>
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using choose_two_gap_gt g hg
  | succ b ih =>
      have hlow :
          g ≤ Nat.choose ((b + 2) + g) ((b + 2) + 1) := by
        have hsymm :
            Nat.choose ((b + 2) + g) ((b + 2) + 1)
              = Nat.choose ((b + 2) + g) (g - 1) := by
          have hle : (b + 2) + 1 ≤ (b + 2) + g := by omega
          calc
            Nat.choose ((b + 2) + g) ((b + 2) + 1)
                = Nat.choose ((b + 2) + g)
                    (((b + 2) + g) - ((b + 2) + 1)) :=
                  (Nat.choose_symm hle).symm
            _ = Nat.choose ((b + 2) + g) (g - 1) := by
                  congr 1
                  omega
        have hedge : Nat.choose g (g - 1) = g := by
          have h1 : 1 ≤ g := by omega
          calc
            Nat.choose g (g - 1) = Nat.choose g 1 := Nat.choose_symm h1
            _ = g := Nat.choose_one_right g
        have hmono :
            Nat.choose g (g - 1) ≤ Nat.choose ((b + 2) + g) (g - 1) :=
          Nat.choose_le_choose (g - 1) (by omega)
        calc
          g = Nat.choose g (g - 1) := hedge.symm
          _ ≤ Nat.choose ((b + 2) + g) (g - 1) := hmono
          _ = Nat.choose ((b + 2) + g) ((b + 2) + 1) := hsymm.symm

      have harith :
          ((b + 2) + 1) * g + 1 = (b + 2) * g + 1 + g := by
        ring

      rw [show b.succ + 2 = (b + 2) + 1 by omega,
          show ((b + 2) + 1) + g = ((b + 2) + g) + 1 by omega,
          Nat.choose_succ_succ',
          harith]
      omega

theorem choose_gt_mul_sub_add_one {ell a : ℕ}
    (ha : 2 ≤ a) (hg : 2 ≤ ell - a) :
    a * (ell - a) + 1 < Nat.choose ell a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  let g := ell - (2 + b)
  have hg' : 2 ≤ g := by simpa [g] using hg
  have hell : ell = (2 + b) + g := by
    dsimp [g]
    omega
  rw [hell]
  simpa [g, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using choose_add_gap_gt_aux b g hg'
```

The iff structure I would use:

```lean
theorem choose_eq_mul_sub_add_one_iff {ell a : ℕ} (haell : a ≤ ell) :
    Nat.choose ell a = a * (ell - a) + 1 ↔ min a (ell - a) ≤ 1 := by
  constructor
  · intro heq
    by_contra hmin
    have h2 : 2 ≤ min a (ell - a) := by omega
    have ha2 : 2 ≤ a := h2.trans (min_le_left _ _)
    have hg2 : 2 ≤ ell - a := h2.trans (min_le_right _ _)
    have hgt := choose_gt_mul_sub_add_one (ell := ell) (a := a) ha2 hg2
    rw [heq] at hgt
    exact (lt_irrefl _ hgt)

  · intro hmin
    have hcases : a ≤ 1 ∨ ell - a ≤ 1 := by
      simpa [min_le_iff] using hmin
    rcases hcases with ha1 | hg1
    · interval_cases a
      · simp
      · rw [Nat.choose_one_right]
        omega
    · have hgap : ell - a = 0 ∨ ell - a = 1 := by omega
      rcases hgap with h0 | h1
      · have : a = ell := by omega
        subst a
        simp
      · have hell : ell = a + 1 := by omega
        rw [hell]
        simp [Nat.choose_succ_self_right]
```

Most likely failure point: `omega` will not invent the nonlinear rewrite
`((b+2)+1) * g + 1 = (b+2) * g + 1 + g`. Pre-empt it with the explicit `harith` proved by `ring`, then let `omega` use only `ih` and `hlow`. This route avoids the nastier `/ 2` failure point entirely.