import DLNFibre.DLN.RLCT.Validate.BindingRecursion

/-!
# `BindingMinSpine` — the binding R1 core identity via the MIN-recursion (the cover route, fm3)

The MIN-form of the binding R1 recursion spine. The COVER route (a5f5ceb1's GE producer) presents the
per-node RLCT as a `⨅`-min over pivot branches — a **clean point-min at the value level** (the
adjudicator confirmed: no box-threading in the spine; the box-recursion is internal to the producer).
So the per-node behaviour is a SINGLE min fact

> `rlctOf M = min (ofReal (mkOf M / 2)) (ofReal (nRegOf M / 2) + rlctOf (redOf M))`

where the first branch `mkOf M / 2` is the node's own Morse contribution (the cover's leaf/no-descent
cell) and the second `nRegOf M / 2 + rlctOf (redOf M)` is the descent into the reduced child. This file
proves the OUTER recursion `binding_recursion_of_min_step`: by strong induction on the width-sum, the min
collapses at the child value to `rlctOf M = ofReal (lambdaCore M)` (`= ½·minAdm`).

**Abstract / route-independent.** Like `binding_recursion_of_step`, the per-node min fact `hstep_min` +
the leaf base `hbase` + the value-side min arithmetic `harith_min`/`harith_base` are HYPOTHESES — the
cover atom (a5f5ceb1) discharges them. This isolates the recursion/min-collapse DESIGN. The value side is
the genuine point-min `lamOf M = min (mkOf M / 2) (nRegOf M / 2 + lamOf (redOf M))`; the spine closes it
to `ofReal (lamOf M)` via `ENNReal.ofReal_min` + `ENNReal.ofReal_add` (nonneg branches) + the recursion.

`degenChild` guards termination (the second/descent branch recurses only when `¬ degenChild`, the child
`redOf M` strictly decreasing `ΣM`; at a `degenChild` node the min has already collapsed to the first
branch `mkOf M / 2`, no recursion). Identical termination shape to the additive spine.
-/

open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The binding R1 MIN-recursion skeleton (abstract).** Given the per-node MIN fact `hstep_min` (the
cover's point-min: the node is the smaller of its own Morse value `mkOf M / 2` and the descent
`nRegOf M / 2 + rlctOf (redOf M)`) at a non-degenerate node, the leaf base `hbase` (`rlctOf M =
mkOf M / 2` at a `degenChild` node — the min has collapsed to the first branch), and the value-side
point-min arithmetic `harith_min`/`harith_base`, the binding R1 core identity holds:
`rlctOf M = ofReal (lamOf M)`. Proved by strong recursion on `∑ i, M i` (`redOf` strictly decreases it on
the descent branch).

The min collapse at the step branch: recurse → `rlctOf (redOf M) = ofReal (lamOf (redOf M))`; then
`min (ofReal (mkOf M / 2)) (ofReal (nRegOf M / 2) + ofReal (lamOf (redOf M)))
   = min (ofReal (mkOf M / 2)) (ofReal (nRegOf M / 2 + lamOf (redOf M)))`  (`ofReal_add`, nonneg)
   `= ofReal (min (mkOf M / 2) (nRegOf M / 2 + lamOf (redOf M)))`  (`ofReal_min`)
   `= ofReal (lamOf M)`  (`harith_min`). -/
theorem binding_recursion_of_min_step
    (redOf : (Fin (L + 1) → ℕ) → (Fin (L + 1) → ℕ))
    (mkOf nRegOf lamOf : (Fin (L + 1) → ℕ) → ℚ)
    (rlctOf : (Fin (L + 1) → ℕ) → ℝ≥0∞)
    (degenChild : (Fin (L + 1) → ℕ) → Prop)
    -- the per-node NON-degenerate MIN step (the cover point-min)
    (hstep_min : ∀ M : Fin (L + 1) → ℕ, ¬ degenChild M →
        rlctOf M = min (ENNReal.ofReal (mkOf M / 2))
          (ENNReal.ofReal (nRegOf M / 2) + rlctOf (redOf M)))
    -- the degenerate-child base: the min has collapsed to the first (Morse) branch
    (hbase : ∀ M : Fin (L + 1) → ℕ, degenChild M →
        rlctOf M = ENNReal.ofReal (mkOf M / 2))
    -- the value-side point-min telescope
    (harith_min : ∀ M : Fin (L + 1) → ℕ, ¬ degenChild M →
        lamOf M = min (mkOf M / 2) (nRegOf M / 2 + lamOf (redOf M)))
    (harith_base : ∀ M : Fin (L + 1) → ℕ, degenChild M → lamOf M = mkOf M / 2)
    -- termination: the child strictly decreases ΣM on the descent branch
    (hdrop : ∀ M : Fin (L + 1) → ℕ, ¬ degenChild M → ∑ i, redOf M i < ∑ i, M i)
    -- nonneg of the value functionals (so the `ofReal` split/min is faithful)
    (hmk : ∀ M : Fin (L + 1) → ℕ, 0 ≤ mkOf M)
    (hnReg : ∀ M : Fin (L + 1) → ℕ, 0 ≤ nRegOf M)
    (hlam : ∀ M : Fin (L + 1) → ℕ, 0 ≤ lamOf M)
    (M : Fin (L + 1) → ℕ) :
    rlctOf M = ENNReal.ofReal (lamOf M) := by
  induction hn : (∑ i, M i) using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    subst hn
    by_cases hdeg : degenChild M
    · -- base case: the min collapsed to the Morse branch, `rlctOf M = mkOf M / 2 = lamOf M`.
      rw [hbase M hdeg]
      congr 1
      exact_mod_cast (harith_base M hdeg).symm
    · -- step case: recurse on the child, then collapse the min at the child value.
      have hchild : rlctOf (redOf M) = ENNReal.ofReal (lamOf (redOf M)) :=
        ih (∑ i, redOf M i) (hdrop M hdeg) (redOf M) rfl
      -- nonnegativity of the `ofReal` arguments in the cast form `hstep_min` produces.
      have hnr : (0 : ℝ) ≤ (nRegOf M : ℝ) / 2 :=
        div_nonneg (by exact_mod_cast hnReg M) (by norm_num)
      have hlr : (0 : ℝ) ≤ (lamOf (redOf M) : ℝ) := by exact_mod_cast hlam (redOf M)
      -- the ℝ-level value min identity from the combinatorial telescope (cast `harith_min`).
      have hval : min ((mkOf M : ℝ) / 2) ((nRegOf M : ℝ) / 2 + (lamOf (redOf M) : ℝ))
          = (lamOf M : ℝ) := by
        have h := harith_min M hdeg
        rw [h]; push_cast; ring_nf
      rw [hstep_min M hdeg, hchild, ← ENNReal.ofReal_add hnr hlr, ← ENNReal.ofReal_min, hval]

end DLNFibre.DLN.RLCT
