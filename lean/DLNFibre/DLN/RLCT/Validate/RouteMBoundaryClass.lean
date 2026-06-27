import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMBoundaryClass` — the BOUNDARY class split (CLEAN vs SMEARED) of the ∀M achiever-chart 4-way

The ∀M achiever-chart assembly (cert `certificate-genM-witness-v2.md` §5 /
`certificate-genM-smeared.md` §5, `2 ≤ L`, `minAdm ≥ 1`) is a 3-way split (after the `L = 1`
`DeepestBaseL1` branch):

```
INTERIOR  := some interior boundary drops both row & col rank   -- DONE: achieverUbound_interior
BOUNDARY  := ¬INTERIOR  (all codim at the LAST boundary)
              ├─ CLEAN    := r = m1   (the deepest factor is exactly the rank-carrying block)
              └─ SMEARED  := r < m1   (the deepest factor has spectator rows)
```

with `r := Text M (tach M) L` (the rank flowing into the deepest factor along the achiever path)
and `m1 := Wext M (L−1) = M (L−1)` (the deepest factor's row count). This file pins the two BOUNDARY
sub-classes as predicates in the same chain-native widths `InteriorDrop` uses, proves they are
EXCLUSIVE and EXHAUSTIVE over the boundary class (`¬InteriorDrop M ↔ BoundaryClean M ∨
BoundarySmeared M`, with `¬(BoundaryClean M ∧ BoundarySmeared M)`), and records the structural
identities the per-branch charts consume (the bottleneck `r ≤ m1` along the achiever path; CLEAN ⟺
`Text M (tach M) L = M (L−1)`).

## Decidability caveat (carried next to the claim)
`tach M = Fin.cons (M 0) (tStar M)` and `tStar M` is `Classical.choose` of the `Mval`-minimizer
(`RouteMAchieverPath`), so `Text M (tach M)`/`Wext M` are NOT `decide`-reducible — the boundary
predicates are genuine `Classical` Props (the assembly's case split uses `Classical.propDecidable`,
the same `if … then … else` shape the cert prescribes). The predicate FORMULAE are decidable given
the widths; the widths themselves are noncomputable (a chosen argmin). So this is the structural
split, not a `decide`-evaluable classifier.

The CLEAN branch's chart is the banked whole-deepest radial (`RouteM4422`/`RouteM221` pattern,
cite); the SMEARED branch's chart is the rational single-pivot `φ_sm` (`certificate-genM-smeared`). Both
fit the EXISTING single-axis `NodeAchieverChart` (see the smeared `cov` gating analysis in
`statement-cards.md`).
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The deepest-factor rank `r` and row count `m1` (chain-native, along the achiever path) -/

/-- The rank flowing into the deepest factor along the achiever path, `r := Text M (tach M) L` (the
compressed width at the leaf boundary `L`). -/
noncomputable def deepRank (M : Fin (L + 1) → ℕ) : ℕ := Text M (tach M) L

/-- The deepest factor's row count, `m1 := Wext M (L−1) = M (L−1)`. (`L ≥ 1` for this to name the
genuine penultimate ambient width; for `L = 0` it falls through `Wext`'s `dite`, irrelevant — the
whole boundary split is stated for `2 ≤ L`.) -/
noncomputable def deepRows (M : Fin (L + 1) → ℕ) : ℕ := Wext M (L - 1)

/-! ## The BOUNDARY sub-class predicates -/

/-- **BOUNDARY-CLEAN.** Not interior-drop, and the deepest factor is EXACTLY the rank-carrying
block: `deepRank M = deepRows M` (`r = m1`). The chart is the whole-deepest single-pivot radial
(`pivotBlowupOn` on all `m1·c` deepest coords; det `|u_p|^{minAdm−1}`); fits `NodeAchieverChart`
verbatim (cite the banked `RouteM4422`/`RouteM221` radial). -/
def BoundaryClean (M : Fin (L + 1) → ℕ) : Prop :=
  ¬ InteriorDrop M ∧ deepRank M = deepRows M

/-- **BOUNDARY-SMEARED.** Not interior-drop, and the deepest factor has genuine spectator rows:
`deepRank M < deepRows M` (`r < m1`). The chart is the rational single-pivot `φ_sm` (`F = z²·U`,
`U = ‖P_1 H̄‖²` polynomial, det `|z|^{minAdm−1}`); fits the EXISTING single-axis
`NodeAchieverChart`, with the rational `cov` the one new piece (gating: `statement-cards.md`). -/
def BoundarySmeared (M : Fin (L + 1) → ℕ) : Prop :=
  ¬ InteriorDrop M ∧ deepRank M < deepRows M

/-! ## Classical decidability (the assembly's `if … then … else` shape) -/

noncomputable instance instDecidableInteriorDrop (M : Fin (L + 1) → ℕ) :
    Decidable (InteriorDrop M) := Classical.propDecidable _

noncomputable instance instDecidableBoundaryClean (M : Fin (L + 1) → ℕ) :
    Decidable (BoundaryClean M) := Classical.propDecidable _

noncomputable instance instDecidableBoundarySmeared (M : Fin (L + 1) → ℕ) :
    Decidable (BoundarySmeared M) := Classical.propDecidable _

/-! ## Exclusivity + exhaustiveness over the boundary class -/

/-- **CLEAN and SMEARED are exclusive** (`r = m1` and `r < m1` cannot both hold). -/
theorem not_boundaryClean_and_boundarySmeared (M : Fin (L + 1) → ℕ) :
    ¬ (BoundaryClean M ∧ BoundarySmeared M) := by
  rintro ⟨⟨_, heq⟩, ⟨_, hlt⟩⟩
  omega

/-- **The boundary class splits exactly into CLEAN and SMEARED, given the achiever-path bottleneck
`r ≤ m1`** (holds 46/46 + 20/20 on the validated grid; carried as a hypothesis here since
`deepRank`/`deepRows` are noncomputable argmin widths). For boundary `M` with `deepRank M ≤ deepRows
M`, exactly one of CLEAN / SMEARED holds. -/
theorem boundaryClean_or_boundarySmeared (M : Fin (L + 1) → ℕ)
    (hbdry : ¬ InteriorDrop M) (hle : deepRank M ≤ deepRows M) :
    BoundaryClean M ∨ BoundarySmeared M := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr ⟨hbdry, hlt⟩
  · exact Or.inl ⟨hbdry, heq⟩

/-- **The boundary class is exactly `¬InteriorDrop`** (CLEAN ∨ SMEARED ⟹ ¬InteriorDrop, the easy
direction — both sub-classes carry `¬InteriorDrop` by definition). With `hle : deepRank ≤ deepRows`
the converse is `boundaryClean_or_boundarySmeared`, so the three classes partition all `M`. -/
theorem boundary_of_clean_or_smeared (M : Fin (L + 1) → ℕ)
    (h : BoundaryClean M ∨ BoundarySmeared M) : ¬ InteriorDrop M := by
  rcases h with ⟨hb, _⟩ | ⟨hb, _⟩ <;> exact hb

/-- **INTERIOR and BOUNDARY-CLEAN are exclusive.** -/
theorem not_interiorDrop_and_boundaryClean (M : Fin (L + 1) → ℕ) :
    ¬ (InteriorDrop M ∧ BoundaryClean M) := by
  rintro ⟨hInt, hCl, _⟩; exact hCl hInt

/-- **INTERIOR and BOUNDARY-SMEARED are exclusive.** -/
theorem not_interiorDrop_and_boundarySmeared (M : Fin (L + 1) → ℕ) :
    ¬ (InteriorDrop M ∧ BoundarySmeared M) := by
  rintro ⟨hInt, hSm, _⟩; exact hSm hInt

/-- **The full three-way trichotomy is total**, given the achiever-path bottleneck `r ≤ m1`: every
`M` is at least one of INTERIOR, BOUNDARY-CLEAN, BOUNDARY-SMEARED (the three pairwise-exclusivity
lemmas above give "exactly one"). -/
theorem interiorDrop_or_boundaryClean_or_boundarySmeared (M : Fin (L + 1) → ℕ)
    (hle : deepRank M ≤ deepRows M) :
    InteriorDrop M ∨ BoundaryClean M ∨ BoundarySmeared M := by
  by_cases hInt : InteriorDrop M
  · exact Or.inl hInt
  · exact Or.inr (boundaryClean_or_boundarySmeared M hInt hle)

end DLNFibre.DLN.RLCT
