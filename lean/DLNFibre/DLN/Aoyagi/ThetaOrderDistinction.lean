import DLNFibre.Core.CThetaThetaBridge

/-!
# `DLNFibre.DLN.Aoyagi.ThetaOrderDistinction` — the two θ-invariants are different

Three integers attached to a DLN fibre `mult⁻¹(B)` have all been written `θ`
(`docs/expositions/theta-invariants-distinction.md`). This module formalises the **distinction**
between the two that are most easily conflated:

* the **geometric component count** `θ = C(m, |δ|)` — Lehalleur–Rimányi's `θ`, the number of
  top-dimensional irreducible components of the fibre. In the harness this is
  `Core.cTheta` (closed form) `= Core.numTop` (the Kostant-side count), an honest *count of
  components of a variety*;
* the **analytic pole order** `a(ℓ−a)+1` — Aoyagi's `θ` (Theorem 2 / equal-width Example), the
  order of the largest pole of the loss's zeta function (the real-log-canonical *multiplicity*).

These are **not equal in general**. This file does **not** prove an equality of the two — that is
false. It lands two capstones:

1. **The mismatch** (`numTop_d22222_ne_aoyagiPoleOrder`, with the abstract core
   `choose_four_two_ne_aoyagiPoleOrder`). At the witness `d = (2,2,2,2,2)`, `r = 0` (so `m = 4`,
   `|δ| = 2`, and Aoyagi's `ℓ = 4`, `a = 2`), the **live** geometric component count
   `numTop ![2,2,2,2,2] 0 = cTheta = C(4,2) = 6` is `≠` Aoyagi's pole order
   `aoyagiPoleOrder 4 2 = 5`. Tying the `6` to the actual `Core.numTop`/`Core.cTheta` of the
   dimension vector makes it impossible for downstream code to read either as a pole order.
2. **The agreement regime** (`choose_eq_aoyagiPoleOrder_iff`). For `a ≤ ℓ`,
   `Nat.choose ℓ a = aoyagiPoleOrder ℓ a ↔ min a (ℓ − a) ≤ 1`: the two invariants coincide exactly
   on the four edge cases `a ∈ {0, 1, ℓ−1, ℓ}` and diverge (`choose` strictly larger) once
   `min a (ℓ − a) ≥ 2` (`choose_gt_aoyagiPoleOrder`).

**Naming discipline.** `aoyagiPoleOrder` is named for what it is — an analytic **pole order**, NOT a
component count. The component count is the harness's `cTheta`/`numTop`. Keeping the names apart is
the point of the file.

`aoyagiPoleOrder` is stated cleanly on `(ℓ, a) : ℕ`. The correspondence to the paper-side active
data is `ℓ = DLN.Aoyagi.ClosedForm.ell d r` and `a = (DLN.Aoyagi.ClosedForm.residueA d r).natAbs`;
for the `(2,2,2,2,2)`, `r = 0` witness these are `ℓ = 4`, `a = 2` (`docs/expositions/`).
-/

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.Core

/-- **Aoyagi's analytic pole order** `aoyagiPoleOrder ℓ a := a·(ℓ − a) + 1` (Aoyagi 2023, Theorem 2
and the equal-width Example). This is the *order of the largest pole* of the loss's zeta function —
the real-log-canonical multiplicity — and is emphatically **not** a count of irreducible components.
The component count is `Core.cTheta` / `Core.numTop`; see `choose_eq_aoyagiPoleOrder_iff` for
exactly when the two integers agree. -/
def aoyagiPoleOrder (ell a : ℕ) : ℕ := a * (ell - a) + 1

/-! ## Capstone 2 — the agreement regime

`Nat.choose ℓ a = aoyagiPoleOrder ℓ a ↔ min a (ℓ − a) ≤ 1` for `a ≤ ℓ`. The genuine content is the
strict divergence `aoyagiPoleOrder ℓ a < Nat.choose ℓ a` whenever `min a (ℓ − a) ≥ 2`; the
agreement on the four edge cases is computational. -/

/-- **Base of the divergence (gap form).** For `2 ≤ g`, `2·g + 1 < C(2 + g, 2)`. Pascal induction on
the gap `g` (peeling `C(n+1, 2) = C(n, 1) + C(n, 2)`); `C(2+g, 2) = (g+2)(g+1)/2 > 2g + 1` since
`g² > g` for `g ≥ 2`. -/
theorem two_mul_add_one_lt_choose_two (g : ℕ) (hg : 2 ≤ g) :
    2 * g + 1 < Nat.choose (2 + g) 2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hg
  induction t with
  | zero => decide
  | succ t ih =>
      have hstep : Nat.choose (2 + (2 + (t + 1))) 2
          = Nat.choose (2 + (2 + t)) 1 + Nat.choose (2 + (2 + t)) 2 := by
        rw [show 2 + (2 + (t + 1)) = (2 + (2 + t)) + 1 by omega, Nat.choose_succ_succ']
      rw [hstep, Nat.choose_one_right]
      omega

/-- **The strict divergence (gap-and-base form).** For `2 ≤ g`, `(b + 2)·g + 1 < C((b + 2) + g,
b + 2)`. Induction on the base `b`: Pascal `C(n+1, k+1) = C(n, k) + C(n, k+1)` adds the column term
`C((b+2)+g, (b+2)+1) ≥ g` (the new active divisor), and the residual is `omega`. -/
theorem aoyagiPoleOrder_add_lt_choose_aux (b g : ℕ) (hg : 2 ≤ g) :
    (b + 2) * g + 1 < Nat.choose ((b + 2) + g) (b + 2) := by
  induction b with
  | zero =>
      have h := two_mul_add_one_lt_choose_two g hg
      simpa [Nat.add_comm] using h
  | succ b ih =>
      -- the new column term `C((b+2)+g, (b+2)+1) ≥ g`, via `choose_symm` + monotonicity.
      have hlow : g ≤ Nat.choose ((b + 2) + g) ((b + 2) + 1) := by
        have hle : (b + 2) + 1 ≤ (b + 2) + g := by omega
        have hsymm : Nat.choose ((b + 2) + g) ((b + 2) + 1)
            = Nat.choose ((b + 2) + g) (g - 1) := by
          rw [← Nat.choose_symm hle]
          congr 1
          omega
        have hedge : Nat.choose g (g - 1) = g := by
          rw [Nat.choose_symm (by omega : 1 ≤ g), Nat.choose_one_right]
        have hmono : Nat.choose g (g - 1) ≤ Nat.choose ((b + 2) + g) (g - 1) :=
          Nat.choose_le_choose (g - 1) (by omega)
        rw [hsymm]; omega
      -- Pascal at the corner: `C((b+3)+g, b+3) = C((b+2)+g, b+2) + C((b+2)+g, (b+2)+1)`.
      have hpascal : Nat.choose ((b + 1 + 2) + g) (b + 1 + 2)
          = Nat.choose ((b + 2) + g) (b + 2) + Nat.choose ((b + 2) + g) ((b + 2) + 1) := by
        rw [show (b + 1 + 2) + g = ((b + 2) + g) + 1 by omega,
          show b + 1 + 2 = (b + 2) + 1 by omega, Nat.choose_succ_succ']
      have harith : (b + 1 + 2) * g + 1 = (b + 2) * g + 1 + g := by ring
      rw [hpascal, harith]
      omega

/-- **Strict divergence outside the edge regime.** For `2 ≤ a` and `2 ≤ ℓ − a` (equivalently
`a ≤ ℓ` and `min a (ℓ − a) ≥ 2`, so `ℓ ≥ 4`), the geometric component count strictly exceeds the
analytic pole order: `aoyagiPoleOrder ℓ a < Nat.choose ℓ a`. -/
theorem choose_gt_aoyagiPoleOrder {ell a : ℕ} (ha : 2 ≤ a) (hg : 2 ≤ ell - a) :
    aoyagiPoleOrder ell a < Nat.choose ell a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  -- write `ell = (b + 2) + g` with `g = ell - (2 + b) ≥ 2`.
  set g := ell - (2 + b) with hgdef
  have hg' : 2 ≤ g := by omega
  have hell : ell = (b + 2) + g := by omega
  have h := aoyagiPoleOrder_add_lt_choose_aux b g hg'
  -- normalise the goal's `(2 + b)` and `ell - (2 + b)` to `(b + 2)` and `g`.
  have hmul : aoyagiPoleOrder ell (2 + b) = (b + 2) * g + 1 := by
    rw [aoyagiPoleOrder, show 2 + b = b + 2 from by ring, show ell - (b + 2) = g from by omega]
  have hch : Nat.choose ell (2 + b) = Nat.choose ((b + 2) + g) (b + 2) := by
    rw [hell, show 2 + b = b + 2 by ring]
  rw [hmul, hch]; exact h

/-- **Capstone 2 — the agreement regime.** For `a ≤ ℓ`, the geometric component count
`Nat.choose ℓ a` equals Aoyagi's analytic pole order `aoyagiPoleOrder ℓ a` **iff**
`min a (ℓ − a) ≤ 1`. The four edge cases `a ∈ {0, 1, ℓ−1, ℓ}` (both sides `1, ℓ, ℓ, 1`) are the
agreement; outside them the binomial strictly dominates (`choose_gt_aoyagiPoleOrder`). -/
theorem choose_eq_aoyagiPoleOrder_iff {ell a : ℕ} (haell : a ≤ ell) :
    Nat.choose ell a = aoyagiPoleOrder ell a ↔ min a (ell - a) ≤ 1 := by
  constructor
  · intro heq
    by_contra hmin
    have ha2 : 2 ≤ a := le_trans (by omega) (min_le_left a (ell - a))
    have hg2 : 2 ≤ ell - a := le_trans (by omega) (min_le_right a (ell - a))
    have := choose_gt_aoyagiPoleOrder ha2 hg2
    omega
  · intro hmin
    -- `min a (ℓ−a) ≤ 1` splits as `a ≤ 1 ∨ ℓ − a ≤ 1`.
    have hcases : a ≤ 1 ∨ ell - a ≤ 1 := by omega
    rcases hcases with ha1 | hg1
    · -- `a = 0` (both `1`) or `a = 1` (both `ℓ`).
      interval_cases a
      · simp [aoyagiPoleOrder]
      · rw [Nat.choose_one_right, aoyagiPoleOrder]; omega
    · -- `ℓ − a = 0` i.e. `a = ℓ` (both `1`), or `ℓ − a = 1` i.e. `a = ℓ − 1` (both `ℓ`).
      rcases (by omega : ell - a = 0 ∨ ell - a = 1) with h0 | h1
      · have : a = ell := by omega
        subst this; simp [aoyagiPoleOrder]
      · have hell : ell = a + 1 := by omega
        subst hell
        rw [Nat.choose_succ_self_right, aoyagiPoleOrder, Nat.add_sub_cancel_left]; omega

/-! ## Capstone 1 — the concrete mismatch at `(2,2,2,2,2)`, `r = 0`

The smallest network where the two θ-invariants separate. With `d = (2,2,2,2,2)`, `r = 0`, the
LR engine gives `m = 4`, `|δ| = 2` so the geometric count is `C(4, 2) = 6`, while Aoyagi's order is
`aoyagiPoleOrder 4 2 = 2·2 + 1 = 5`. The geometric count is tied to the **live**
`numTop`/`cTheta`. -/

/-- **The abstract mismatch.** The geometric component count `C(4, 2) = 6` of the witness fibre is
`≠` Aoyagi's analytic pole order `aoyagiPoleOrder 4 2 = 5`. (This is the `min a (ℓ−a) = 2` instance
of `choose_eq_aoyagiPoleOrder_iff`, recorded concretely.) -/
theorem choose_four_two_ne_aoyagiPoleOrder : Nat.choose 4 2 ≠ aoyagiPoleOrder 4 2 := by decide

/-- The witness dimension vector `(2,2,2,2,2)` (depth `4`, constant width `2`). -/
abbrev d22222 : Fin 5 → ℕ := ![2, 2, 2, 2, 2]

/-- `(2,2,2,2,2)` is weakly increasing. -/
theorem d22222_monotone : Monotone d22222 := by decide

/-- The QIP feasible set for `d22222` is nonempty (`e = (2,0,0,0)`, `∑ = d 0 = 2`). -/
theorem qipFeasible_d22222_nonempty : (qipFeasible d22222).Nonempty :=
  ⟨![2, 0, 0, 0], by decide +kernel⟩

/-- The Kostant partitions of `d22222` with corner `0` are nonempty (via the QIP feasible set). -/
theorem kostantPartitions_d22222_nonempty : (kostantPartitions d22222 0).Nonempty :=
  (kostant_nonempty_iff_qipFeasible_nonempty d22222 d22222_monotone).mpr
    qipFeasible_d22222_nonempty

/-- **`(2,2,2,2,2)`: the closed-form geometric count `cTheta = C(4, 2) = 6`.** -/
theorem cTheta_d22222 : cTheta d22222 = 6 := by decide +kernel

/-- **`(2,2,2,2,2)`: the live Kostant-side geometric count `numTop = 6`**, via
`numTop_zero_eq_cTheta`. This is the honest count of top-dimensional irreducible components of the
fibre. -/
theorem numTop_d22222_zero : numTop d22222 0 kostantPartitions_d22222_nonempty = 6 := by
  rw [numTop_zero_eq_cTheta d22222 d22222_monotone, cTheta_d22222]

/-- **Capstone 1 — the live mismatch.** The geometric component count `numTop ![2,2,2,2,2] 0 = 6`
of the fibre is `≠` Aoyagi's analytic pole order `aoyagiPoleOrder 4 2 = 5`. The component count is
read off the variety; the pole order is read off the zeta function after resolution — there is no
identity between them, and this is the smallest DLN witness. -/
theorem numTop_d22222_ne_aoyagiPoleOrder :
    numTop d22222 0 kostantPartitions_d22222_nonempty ≠ aoyagiPoleOrder 4 2 := by
  rw [numTop_d22222_zero]; decide

end DLNFibre.DLN.Aoyagi
