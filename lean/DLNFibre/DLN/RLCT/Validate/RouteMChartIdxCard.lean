import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet

/-!
# `RouteMChartIdxCard` — Phase B item-1 bricks: the LDU role-card accounting (`t² = |Low|+t+|Up|`)

The bounded, reusable cardinality bricks for the determinant-ready coordinatization (item 1 of the
det-route re-scope, `threads/36-…/codex/item1-{prompt,answer}`): the per-boundary LDU role count. The
`K_s` block's `t²` free coordinates are parametrized by the LDU roles `low` (`|LowIdx t| = t(t−1)/2`),
`diag` (`t`), `up` (`|UpIdx t| = t(t−1)/2`), summing to `t²`. These are the role-card building blocks of
the `ChartIdx` cardinality theorem `Fintype.card (ChartIdx M t) = flatDim M` (the cert's
`ninputs = flatDim`, verified algebraically to telescope: per boundary `K+X+N+E = t_{s-1}·M_s`,
`W = c_s·M_{s+1}`, the `t_s` middle sums cancel, `t_0 = M_0` closes it, `+1` radial `−1` fixed residual).

* `card_lowIdx_eq_upIdx` — `|LowIdx t| = |UpIdx t|` (the transpose symmetry).
* `card_diag` — `|{p : Fin t × Fin t // p.1 = p.2}| = t` (the LDU `diag` role count).
* `lduRole_card` — `|LowIdx t| + t + |UpIdx t| = t²` (the `K_s` block's role count = `t²`), via the
  off-diagonal split `|LowIdx| + |UpIdx| = |offDiag| = t² − t`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite cardinality; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **`|LowIdx t| = |UpIdx t|`** — the strictly-lower and strictly-upper index sets are equinumerous
(the transpose `p ↦ (p.2, p.1)`). -/
theorem card_lowIdx_eq_upIdx (t : ℕ) : Fintype.card (LowIdx t) = Fintype.card (UpIdx t) :=
  Fintype.card_congr ⟨fun p => ⟨(p.1.2, p.1.1), p.2⟩, fun p => ⟨(p.1.2, p.1.1), p.2⟩,
    fun _ => rfl, fun _ => rfl⟩

/-- **The LDU `diag` role count** `|{p : Fin t × Fin t // p.1 = p.2}| = t` (the diagonal). -/
theorem card_diag (t : ℕ) : Fintype.card {p : Fin t × Fin t // p.1 = p.2} = t := by
  have e : {p : Fin t × Fin t // p.1 = p.2} ≃ Fin t :=
    { toFun := fun p => p.1.1
      invFun := fun i => ⟨(i, i), rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl p.property)
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- **The `K_s` block role count** `|LowIdx t| + t + |UpIdx t| = t²` — the LDU `low`/`diag`/`up` roles
account for exactly the `t²` free coordinates of the `t × t` core block `K_s`. Via the off-diagonal
split: `|LowIdx| + |UpIdx| = |{p // p.1 ≠ p.2}| = |offDiag| = t² − t`, plus the diagonal `t`. -/
theorem lduRole_card (t : ℕ) :
    Fintype.card (LowIdx t) + t + Fintype.card (UpIdx t) = t * t := by
  classical
  have hsum : Fintype.card (LowIdx t) + Fintype.card (UpIdx t)
      = Fintype.card {p : Fin t × Fin t // p.1 ≠ p.2} := by
    rw [← Fintype.card_sum]
    apply Fintype.card_congr
    refine Equiv.ofBijective
      (fun e => e.elim (fun p => ⟨p.1, ne_of_gt p.2⟩) (fun p => ⟨p.1, ne_of_lt p.2⟩)) ?_
    refine ⟨?_, ?_⟩
    · rintro (⟨p, hp⟩ | ⟨p, hp⟩) (⟨q, hq⟩ | ⟨q, hq⟩) heq <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at heq
      · exact congrArg Sum.inl (Subtype.ext heq)
      · exfalso; rw [heq, Fin.lt_def] at hp; rw [Fin.lt_def] at hq; omega
      · exfalso; rw [heq, Fin.lt_def] at hp; rw [Fin.lt_def] at hq; omega
      · exact congrArg Sum.inr (Subtype.ext heq)
    · rintro ⟨p, hp⟩
      rcases lt_or_gt_of_ne hp with h | h
      · exact ⟨Sum.inr ⟨p, h⟩, rfl⟩
      · exact ⟨Sum.inl ⟨p, h⟩, rfl⟩
  have hoff : Fintype.card {p : Fin t × Fin t // p.1 ≠ p.2} = t * t - t := by
    rw [Fintype.card_subtype]
    have heq : (Finset.univ.filter (fun p : Fin t × Fin t => p.1 ≠ p.2))
        = (Finset.univ : Finset (Fin t)).offDiag := by ext p; simp [Finset.mem_offDiag]
    rw [heq, Finset.offDiag_card]; simp [Fintype.card_fin]
  have hle : t ≤ t * t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; rfl
    · exact Nat.le_mul_of_pos_left t h
  omega

end DLNFibre.DLN.RLCT
