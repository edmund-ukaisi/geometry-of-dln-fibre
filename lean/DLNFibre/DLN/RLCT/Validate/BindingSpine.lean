import DLNFibre.DLN.RLCT.Validate.BindingRecursion
import DLNFibre.DLN.RLCT.Validate.BindingArith

/-!
# `BindingSpine` — the binding R1 core identity, reduced to the geometric `hstep` (fm3 #145 meeting-point)

The MEETING-POINT lemma of the binding G-b: it instantiates the PROVEN recursion
`binding_recursion_of_step` (`BindingRecursion.lean`, fm3 #145) with rs-grind's PROVEN combinatorial
arithmetic (`BindingArith.lean`, #143: `bind_harith_step` / `bind_harith_base` / `bind_hdrop` / `bind_hlam`
+ `bind_hnReg` mod `hMono`), so that the binding R1 core identity

> `rlctOf M = ofReal (lambdaCore M)`   ( `= ½·minAdm`, the value cobuild's L2-Skeleton bridge consumes)

reduces to EXACTLY the two geometric obligations fm3 still owns: the per-node `hstep` (the RLCT descent at
a non-leaf node) + `hbase` (the `#70` Morse base at a degenerate-child node), plus the value-side
monotonicity `hMono` (`lambdaCore (schurStateRed M) ≤ lambdaCore M`, rs-grind's #149 — carried here as a
hypothesis until its standalone decl lands on-branch).

**Route note (fm3 soundness catch, 2026-06-23).** `hstep`/`hbase` are taken ABSTRACTLY here (the
`rlctOf`-level per-node equalities) — this lemma is route-INDEPENDENT. The actual producer of `hstep` at a
real blow-up node is the WEIGHTED-COVER route (the blow-up Jacobian explicit in the integrand, `#104`), NOT
the MP-chart bridge `RouteMO1Bridge` (re-scoped as flawed-for-blow-ups). This meeting-point crystallises
that, once `hstep`/`hbase`/`hMono` are supplied, the binding identity is closed — making the remaining gaps
crisp and explicit.
-/

open scoped ENNReal

namespace DLNFibre.DLN.RLCT

variable {L' : ℕ}

/-- A leaf node stays a leaf under `schurStateRed` (a zero width persists: `s ≤ 1` gives `M s − 1 = 0`
when `M s = 0`; `s ≥ 2` keeps `M s`). So `¬ isLeafNode (schurStateRed M) → ¬ isLeafNode M` — the child's
non-leaf-ness (the recursion's `¬ degenChild`) implies `M` is non-leaf, which `bind_hdrop` needs for
`schurState` to be defined. -/
theorem isLeafNode_schurStateRed_of_isLeafNode (M : Fin (L' + 1 + 1) → ℕ)
    (h : isLeafNode M) : isLeafNode (schurStateRed M) := by
  obtain ⟨s, hs⟩ := (isLeafNode_iff_width_zero M).mp h
  refine (isLeafNode_iff_width_zero (schurStateRed M)).mpr ⟨s, ?_⟩
  simp only [schurStateRed]
  split <;> omega

/-- **The binding R1 core identity, modulo the geometric `hstep`/`hbase` + `hMono`.** For a chain of
`≥ 2` layers (`Fin (L' + 1 + 1)`, so non-leaf nodes admit a `schurState` descent — `bind_hdrop`'s shape),
given an abstract per-node RLCT functional `rlctOf` satisfying the descent `hstep` (non-leaf-child node) +
the `#70` base `hbase` (degenerate-child node), and the value-side monotonicity `hMono`, the core RLCT
equals the combinatorial value: `rlctOf M = ofReal (lambdaCore M)`.

Instantiates `binding_recursion_of_step` with `redOf := schurStateRed`, `nRegOf := bindNReg`,
`lamOf := lambdaCore`, `degenChild := fun M => isLeafNode (schurStateRed M)`, discharging the combinatorial
hypotheses by rs-grind's `bind_*` (`#143`). The geometric `hstep`/`hbase` and `hMono` are the ONLY remaining
inputs — this lemma IS the binding-spine reduction. -/
theorem binding_rlct_eq_lambdaCore_of_hstep
    (rlctOf : (Fin (L' + 1 + 1) → ℕ) → ℝ≥0∞)
    (hMono : ∀ M : Fin (L' + 1 + 1) → ℕ, lambdaCore (schurStateRed M) ≤ lambdaCore M)
    (hstep : ∀ M : Fin (L' + 1 + 1) → ℕ, ¬ isLeafNode (schurStateRed M) →
        rlctOf M = ENNReal.ofReal (bindNReg M / 2) + rlctOf (schurStateRed M))
    (hbase : ∀ M : Fin (L' + 1 + 1) → ℕ, isLeafNode (schurStateRed M) →
        rlctOf M = ENNReal.ofReal (bindNReg M / 2))
    (M : Fin (L' + 1 + 1) → ℕ) :
    rlctOf M = ENNReal.ofReal (lambdaCore M) :=
  binding_recursion_of_step
    schurStateRed bindNReg lambdaCore rlctOf (fun M => isLeafNode (schurStateRed M))
    hstep hbase
    (fun M _ => bind_harith_step M)
    (fun M h => bind_harith_base M h)
    (fun M h => bind_hdrop M (fun hM => h (isLeafNode_schurStateRed_of_isLeafNode M hM)))
    (fun M => bind_hnReg M (hMono M))
    (fun M => bind_hlam M)
    M

end DLNFibre.DLN.RLCT
