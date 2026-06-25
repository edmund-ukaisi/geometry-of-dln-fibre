import DLNFibre.DLN.RLCT.Validate.RouteMNodeDescentBuild
import DLNFibre.DLN.RLCT.Validate.RouteMLeaf

/-!
# `BindingRecursion` — the G-b recursion SKELETON (O2/O3, abstract; fm3 #145)

The de-risk skeleton for the binding R1 core identity (Codex xhigh route verdict, 2026-06-23): the
RECURSION route to `rlctAtOn (dlnLoss M 0) 0 = ofReal (lambdaCore M)` (`= ½·minAdm`), iterating the
per-node descent step `O1` and bottoming out at the degenerate-child node via lemma `#70`.

**This file isolates the recursion/telescope DESIGN from the producer plumbing** (Codex's de-risk: prove
the abstract `binding_recursion_of_step` from assumed per-node hypotheses; the remaining hard work is then
the producer `O1`, the per-node MP transport `dlnLoss = flatCore ∘ chart` — formaliser-weeks, isolated).

The per-node behaviour enters as TWO hypotheses (the leaf-base resolution, fm3 + Codex):
- `hstep` (O1, the NON-degenerate-child step): `rlctAtOn (dlnLoss M 0) 0 = ofReal (nReg M / 2) +
  rlctAtOn (dlnLoss (redOf M) 0) 0`. Sound only when the child `redOf M` is non-degenerate (the
  `RouteMNodeDescent` datum's `Gne` field is the guard — `G ≡ 0` at a degenerate child violates it).
- `hbase` (the `#70` degenerate-boundary base): when the child `redOf M` IS degenerate (some width 0,
  `dlnLoss (redOf M) ≡ 0`, geometric `rlctAtOn = ⊤`), DON'T recurse — `rlctAtOn (dlnLoss M 0) 0 =
  ofReal (nReg M / 2)` directly (the whole node is Morse, lemma `#70`).

The COMBINATORIAL arithmetic (`lambdaCore M = nReg M / 2 + lambdaCore (redOf M)`, with `lambdaCore` of a
degenerate state `= 0`) makes the value telescope `lambdaCore M = ∑ nReg_k / 2` close; the GEOMETRIC
recursion bottoms at `#70` one level above the degenerate leaf. `nReg M = minAdm M − minAdm (redOf M)`
(verified nonneg-integer; `(2,2,2)`: `3/2 = 2/2 + 1/2`, `(1,1,2)`: `1/2 = 1/2 + 0` via `#70`).

**STATUS: PROVED** — the abstract recursion is sorry-free (strong induction on the width-sum). The
per-node `hstep`/`hbase` and the arithmetic `harith` are HYPOTHESES (the producer obligations, supplied
later by the per-node MP transport + the combinatorial `nReg`/`minAdm` facts). This isolates ALL remaining
hard work to the producer — the recursion/telescope DESIGN is closed and validated here.
-/

open scoped ENNReal
open MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The G-b recursion skeleton (O2/O3, abstract).** Given the per-node descent `hstep` (O1, valid where
the child `redOf M` is non-degenerate), the `#70` base `hbase` (at the degenerate-child terminal), and the
combinatorial telescope `harith` (`lambdaCore M = nReg M / 2 + lambdaCore (redOf M)`, with the degenerate
state contributing `0`), the binding R1 core identity holds: `rlctAtOn (dlnLoss M 0) 0 = ofReal
(lambdaCore M)`. Proved by strong recursion on `chainWidthSum` (`redOf` strictly decreases `ΣM`).

`redOf M` is the Schur-reduced widths (`schurState M`); `nReg M = minAdm M − minAdm (redOf M)`;
`degenChild M` flags the degenerate-child terminal (some width of `redOf M` is `0`). The hypotheses are
the producer obligations this skeleton CONSUMES — supplying them is the per-node MP-transport plumbing,
isolated OUT of the recursion design by this statement. -/
theorem binding_recursion_of_step
    (redOf : (Fin (L + 1) → ℕ) → (Fin (L + 1) → ℕ))
    (nRegOf lamOf : (Fin (L + 1) → ℕ) → ℚ)
    (rlctOf : (Fin (L + 1) → ℕ) → ℝ≥0∞)
    (degenChild : (Fin (L + 1) → ℕ) → Prop)
    -- the per-node NON-degenerate-child step (O1): rlctOf M = nRegOf M / 2 + rlctOf (child M)
    (hstep : ∀ M : Fin (L + 1) → ℕ, ¬ degenChild M →
        rlctOf M = ENNReal.ofReal (nRegOf M / 2) + rlctOf (redOf M))
    -- the #70 degenerate-child base: rlctOf M = nRegOf M / 2 (no recursion)
    (hbase : ∀ M : Fin (L + 1) → ℕ, degenChild M →
        rlctOf M = ENNReal.ofReal (nRegOf M / 2))
    -- the combinatorial telescope: lamOf M = nRegOf M / 2 + lamOf (child M), degenerate child lamOf = 0
    (harith_step : ∀ M : Fin (L + 1) → ℕ, ¬ degenChild M →
        lamOf M = nRegOf M / 2 + lamOf (redOf M))
    (harith_base : ∀ M : Fin (L + 1) → ℕ, degenChild M → lamOf M = nRegOf M / 2)
    -- termination: the child strictly decreases ΣM
    (hdrop : ∀ M : Fin (L + 1) → ℕ, ¬ degenChild M → ∑ i, redOf M i < ∑ i, M i)
    -- nonneg of nRegOf and lamOf (so the ofReal split is additive)
    (hnReg : ∀ M : Fin (L + 1) → ℕ, 0 ≤ nRegOf M)
    (hlam : ∀ M : Fin (L + 1) → ℕ, 0 ≤ lamOf M)
    (M : Fin (L + 1) → ℕ) :
    rlctOf M = ENNReal.ofReal (lamOf M) := by
  -- Strong induction on the width-sum `∑ i, M i` (`redOf` strictly decreases it on the step branch).
  induction hn : (∑ i, M i) using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    subst hn
    by_cases hdeg : degenChild M
    · -- base case (#70): rlctOf M = nRegOf M / 2 = lamOf M.
      rw [hbase M hdeg]
      congr 1
      exact_mod_cast (harith_base M hdeg).symm
    · -- step case (O1): rlctOf M = nRegOf M/2 + rlctOf (redOf M); recurse on the child.
      have hchild : rlctOf (redOf M) = ENNReal.ofReal (lamOf (redOf M)) :=
        ih (∑ i, redOf M i) (hdrop M hdeg) (redOf M) rfl
      -- nonnegativity of the two `ofReal` arguments, in the EXACT cast form `hstep` produces
      -- (`ofReal (↑(nRegOf M) / 2)`, the ℚ→ℝ cast pushed INSIDE the division).
      have hnr : (0 : ℝ) ≤ (nRegOf M : ℝ) / 2 :=
        div_nonneg (by exact_mod_cast hnReg M) (by norm_num)
      have hlr : (0 : ℝ) ≤ (lamOf (redOf M) : ℝ) := by exact_mod_cast hlam (redOf M)
      -- the ℝ-level value identity from the combinatorial telescope.
      have hval : (nRegOf M : ℝ) / 2 + (lamOf (redOf M) : ℝ) = (lamOf M : ℝ) := by
        have h := harith_step M hdeg
        push_cast [h]; ring
      rw [hstep M hdeg, hchild, ← ENNReal.ofReal_add hnr hlr, hval]

end DLNFibre.DLN.RLCT
