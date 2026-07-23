<task>
Lean 4 formalisation design question — the INVARIANT for a tree-recursion induction. NO repo access; I give all context.

OBJECTS (Lean, over ℝ; `D := flatDim d` a fixed nat; coords are `Fin D → ℝ`):
- `foldResid d e p : Fin (nR p) → (Fin D → ℝ) → ℝ` — a residual FAMILY defined by recursion on a tree path `p : TreePath d`:
  * root: `foldResid root = coreGen` where `coreGen k u = (∏ A_layers)[decode k]` — entries of the matrix product A_{N-1}···A_0; each entry is MULTILINEAR degree-1 per layer (linear in each layer's coords).
  * δ=1 step: `foldResid (p.extend ed) j u = foldResid p (cast j) (fun k => blockBlowupCoordQuot pivot k (shear u))` where `blockBlowupCoordQuot p j w = if j = p then 1 else w j` (a "strict transform": divide out the pivot factor).
  * δ=0 step: `foldResid (p.extend ed) j u = foldResid p (cast j) (stepMap u)` where `stepMap = blockBlowupMap center pivot ∘ shear`; `blockBlowupMap S p w j = if j=p then w p else if j∈S then w p * w j else w j`.
- `couplingClear d p u k = if k ∈ couplingCoords p then 0 else u k` (zeroes a path-determined finset of "ancestor coupling" coords; ∅ at root).
- `sourceClearedResid d p j u := foldResid d (canonFlatten d) p j (couplingClear d p u)`   [the object the invariant is ABOUT].

TARGET (the "read-off", to be PROVEN from the invariant at a case-1(1) edge `ed` off `p`, with `e₂ := canonPivotOf` a specific coord ∈ `ed.center`, `part := supportAt p ∩ ed.center`, `extra := supportAt p \ ed.center`):
  ∀ j, ∃ α β : Fin D → (Fin D → ℝ) → ℝ,
    (∀ i, ContinuousOn (α i) V) ∧ (∀ i, ContinuousOn (β i) V) ∧
    (∀ i, IgnoresCoords (α i) ed.center V) ∧ (∀ i, IgnoresCoords (β i) ed.center V) ∧
    (∀ u ∈ V, sourceClearedResid d p j u = (∑ i∈part, α i u * u i) + u e₂ * (∑ i∈extra, β i u * u i))
  where `IgnoresCoords c S V` = `c` is invariant under changing any coord in `S` (reads no `S`-coord).

THE MATH (pen-and-paper, verified numerically): the invariant is a "b-ledger": each slot
  `sourceClearedResid d p j u = ∑_{i ∈ supportAt p} c_{j,i}(u) · u_i`,  `c_{j,i} = b_{row(i)}(u) · (clean entry)`,
where `b_i = ∏_{exceptional coords born before row i}` (an accumulated monomial in the exceptional/pivot coords; `b_0 = 1`), and the "clean entry" reads coords OUTSIDE the ledger center. At a case-1(1) edge, the extra-block rows (`i ∈ extra`) have `b_i` carrying an EXTRA factor `u_{e₂}` (the "boost"), so `c_{j,i}` for `i ∈ extra` is divisible by `u_{e₂}`; and all `c_{j,i}` read no `ed.center` coord (IgnoresCoords ed.center).

MY DECOMPOSITION CRUX: a bare "support-decomposition of sourceClearedResid on supportAt(p) with continuous coefficients ignoring supportAt(p)" does NOT suffice for the read-off, because the read-off needs (i) coefficients ignoring `ed.center` (NOT supportAt), and (ii) the extra-block coefficients divisible by `u_{e₂}`. So the induction must carry the b-ledger structure, not just a support-decomp.

QUESTION: design the MINIMAL Lean `Prop`-valued invariant `INV(p)` (a predicate on `sourceClearedResid d p`) such that (a) `INV(root)` follows from coreGen's per-layer multilinearity; (b) `INV(p) → INV(p.extend ed)` is provable through BOTH the δ=1 strict-transform and δ=0 pullback transport steps (the blow-up multiplies center coords by the pivot, the strict transform divides it back out); (c) `INV(p)` + the case-1(1) edge data yields the read-off above. In particular: what is the right IgnoresCoords target to carry in the invariant (ed.center changes per edge, so it can't be the carried target)? How should the b-monomial `b_i` factor be rendered so the boost (extra-block divisible by u_{e₂}) falls out at the read-off?
</task>

<output_contract>
1. The recommended INV(p) as a precise Lean-shaped predicate (pseudo-Lean OK), with each conjunct's ROLE named.
2. The KEY design decision on the IgnoresCoords target (what set the carried coefficients ignore, and how that reconciles with the read-off's ed.center requirement).
3. How the b-monomial / boost is rendered (per-coord divisibility ledger vs an explicit b-factor function vs something else), and how the e₂-divisibility of the extra block falls out at the read-off.
4. The 3 induction obligations (root, δ=1, δ=0) each in one sentence: what must be shown.
5. Any TRAP you foresee (a conjunct that won't inductively propagate, or a shape that can't be established at root).
Keep it under ~500 words. Rank any alternatives; give ONE recommendation.
</output_contract>

<grounding_rules>
This is a design consult, not a proof. Flag explicitly where you are INFERRING structure vs stating a standard technique. If a piece of the b-ledger seems under-determined by what I gave, say so and state the assumption you make.
</grounding_rules>
