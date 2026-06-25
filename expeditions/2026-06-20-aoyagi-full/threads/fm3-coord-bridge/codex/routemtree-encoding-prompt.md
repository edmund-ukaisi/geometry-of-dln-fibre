<task>
Lean 4 + Mathlib v4.29. I'm encoding a recursive resolution tree for an RLCT computation and need the
cleanest, most robust ENCODING (not the math — the Lean structure). The tree recurses on a
lex(L, ΣM, ncDefect) measure over ℕ³ that is NOT structurally decreasing.

THE TREE: over chain widths `M : Fin (L+1) → ℕ`, classify a node into 4 types + leaf:
- leaf: L=1 or rank-0 (terminal smooth block).
- C1: recurse on ONE child at `schurReduce M c : Fin (L+1) → ℕ` (ΣM strictly drops, same L).
- C2: recurse on ONE child at `passThrough M c` with SMALLER L (depth drops, L : Fin (L'+1) with L'<L).
- C4: TWO children at `leftBlock M s` and `rightBlock M s`, each smaller L.
- C5: composite = a C1 child + a C2 child.
The width-reduction ops (schurReduce/passThrough/leftBlock/rightBlock) are defined separately; assume
each comes with a proof that lex(L,ΣM,ncDefect) strictly decreases.

I need TWO things from the tree:
(a) `ι M : Type` = the leaves (root-to-leaf paths), with a `Fintype ι` instance.
(b) per leaf, data `(d, k, h)` (ℕ and Fin d → ℕ) read off the path, to feed `monomialThreshold`.
And ultimately to produce an `IsRouteMCover F U ι d k h` structure (4 Prop fields) consumed by a
downstream bridge.

THE ENCODING QUESTION:
1. Plain `inductive RouteMTree : (Fin (L+1)→ℕ) → Type` with constructors taking children at the reduced
   widths (e.g. `nodeC1 (c) (child : RouteMTree (schurReduce M c))`) — does Lean accept this when
   schurReduce changes the index, AND can I then get `Fintype` of leaves? The CHANGED-L constructors
   (C2/C4 with L'<L) make it an inductive family over BOTH L and M — is that sound / will the leaf
   Fintype derive? Or does the changing L break the single-inductive encoding?
2. ALTERNATIVE: define the tree-build as a `WellFounded.fix` (or `termination_by lex`) function
   `M ↦ RouteMTree M` separately from a plain data inductive — cleaner? How to structure so the
   Fintype-of-leaves + the (d,k,h) extraction are definable.
3. Is there a SIMPLER target that avoids materializing the tree as a type at all: define `ι M`, `d`,
   `k`, `h` DIRECTLY by well-founded recursion (e.g. ι M = a Sigma/sum over the node's children's ι,
   computed by WF recursion on lex), skipping the inductive `RouteMTree`? This might sidestep the
   inductive-family-over-changing-L problem entirely.
4. For the Fintype: finite branching (finitely many PivotChoice per node — a Finset of (active,pivot))
   × lex-bounded depth. What's the cleanest way to get `Fintype (ι M)` — derive it structurally, or
   build ι as a Finset/Fintype by the WF recursion directly?
</task>

<output_contract>
Rank approaches 1/2/3 by robustness at v4.29 for getting BOTH (a) Fintype ι and (b) the (d,k,h)
extraction, given the CHANGING-L recursion. Recommend ONE. Give the concrete Lean skeleton (the type
signatures + the recursion structure + how Fintype derives). Flag the single biggest risk (likely the
inductive-family-over-changing-L, or the WF measure setup). Terse; this is an encoding route-check.
</output_contract>

<grounding_rules>
Reason from Lean 4 / Mathlib v4.29 mechanics. Flag any tactic/typeclass you're unsure works at the pin.
Don't invent Mathlib lemmas. The math (that lex decreases) is given — focus purely on the type-theory
encoding.
</grounding_rules>
