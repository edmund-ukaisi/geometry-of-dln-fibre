# ι as an INDUCTIVE type (the Lean shape fm3 needs), tied to the RouteMNode recursion.
print(r"""
=== ι as an inductive type (the formaliser-consumable definition) ===

ι is the leaf set of a finite tree built by the RouteMNode recursion. Define it as the recursion's
PATH type, indexed by the node M (the current chain widths) + the recursion fuel (lex measure):

  -- A single node's branch set = the valid pivot/minor choices at node M:
  --   PivotChoice M := { (active, p, minor) : active a nonempty coordinate block of the active factor,
  --                       p ∈ active the argmax pivot, minor a rank-r survivor selector (C5) }
  -- The chart tree, inductively (terminating by lex(L, ΣM, ncDefect)):

  inductive RouteMTree (M : Fin (L+1) → ℕ) : Type
    | leaf  (hbase : isSmoothLeaf M)               -- L=1 / rank-0: F=‖C_1‖² a unit≥1, terminal
    | nodeC1 (c : PivotChoice M) (child : RouteMTree (schurReduce M c))      -- coupled: ΣM drops
    | nodeC2 (c : PivotChoice M) (child : RouteMTree (passThrough M c))      -- full-rank: L drops
    | nodeC4 (s : PinchLayer M) (l : RouteMTree (leftBlock M s))            -- Fubini split: two children
                                (r : RouteMTree (rightBlock M s))
    | nodeC5 (c : MixedChoice M) (compl : RouteMTree (schurReduce M c.complement))   -- mixed: C1∘C2
                                  (surv  : RouteMTree (passThrough M c.survivor))

  -- ι M := the LEAVES of RouteMTree M (a Fintype: finite branching × lex-bounded depth).
  --   ι M := { π : path from root to a leaf of RouteMTree M }
  -- Each leaf π carries (d_π, k_π, h_π): d_π = ambient dim at the leaf; for each node on π, an
  --   exceptional divisor with (k,h) read from that node's pivotBlowupOn (+ NC-completion's k≥2 intersections).

NOTE on C3 (NC-completion): it is NOT a tree node — it is a POST-PASS on the assembled divisor
arrangement of a path (turning the union of per-node exceptional divisors into a normal-crossing
arrangement). It refines a leaf's (d,k,h) (introducing k≥2 intersection divisors) but does not branch ι.
So ι's tree is {C1,C2,C4,C5}; C3 acts on each path's divisor data. (This keeps ι finite & the branching
clean — the NC-completion is a deterministic finishing of each path, not a choice.)
""")
print("=== Sanity: (2,2,2) gives the right leaf structure ===")
print("""
(2,2,2) r=1 core = M=(1,1,1) [reduced widths]: core=(c1c2)², ALREADY normal-crossing.
  RouteMTree (1,1,1): the core is monomial already ⟹ the tree is shallow (identity/leaf-ish);
  ι = the 2 coordinate-axis charts ({c1=0},{c2=0}) → monomialThreshold (d=2,k=(1,1),h=(0,0))=1/2.
  ⨅ = 1/2 = lambdaCore(1,1,1). ✓ (the FULL-loss 24-leaf tree is the H=(2,2,2),r=1 picture BEFORE the
  L2/D1 reduction to the core; resolution_charts is on the CORE M=(1,1,1), which is the simple case.)
The 24-leaf (2,2,2) tree fm3 banked is the H-level (pre-core-reduction) atlas; resolution_charts'
ι is the CORE-level tree. For deeper cores ((3,3,3): M=H-r non-trivial) the tree is the C1/C2/C4/C5
recursion. So ι's nontrivial content is the deeper-core recursion, NOT the (2,2,2) special case.
""")
