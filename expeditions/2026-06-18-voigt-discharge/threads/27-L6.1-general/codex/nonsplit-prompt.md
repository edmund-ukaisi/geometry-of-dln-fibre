<task>
Lean 4 + Mathlib v4.29 formalisation. I am building the NON-SPLIT box-move degeneration for type-A
quiver representations. I have a landed engine and want the cleanest construction to avoid a heavy
symbolic dead-end. Diagnose the route, do NOT write full Lean.

SETUP (all already in Lean, working):
- A type-A representation is `Tuple d : ∀ i:Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`
  over a dim vector `d : Fin (N+1) → ℕ`. Edge `i` is a matrix from vertex `i` to vertex `i+1`.
- `intervalModule a e : Tuple (intervalDim a e)` is the interval (lace) module: dim 1 on [a,e], else 0,
  identity edge maps inside [a,e].
- `dirSum A B : Tuple (fun l ↦ d l + d' l)` = block-diagonal `reindex finSumFinEquiv (fromBlocks A 0 0 B)`.
- `intervalDirectSum L` folds `dirSum` over a list of interval endpoints; `foldDim L` its dim vector.
- `submult d A i j : Matrix (Fin (d j)) (Fin (d i)) k` = the sub-product `A_j…A_{i+1}` (identity at i=j),
  with `submult_succ : submult i (p+1) = A_p * submult i p.castSucc`.
- `rankPattern d A i j = (submult d A i j).rank`. `rankPattern_intervalModule : = [a≤i ∧ j≤e]`.
  `rankPattern_dirSum : rankPattern (dirSum A B) = rankPattern A + rankPattern B` (over a field).
- COMPLETE INVARIANT (landed): `orbit_of_rankPattern_eq A B : (∀ i j, rankPattern A i j = rankPattern B i j)
  → ∃ P : BaseChangeGroup d, P • A = B`.  And `rankPattern_eq_iff_orbit` (iff version).
- ENGINE (landed): `mem_zeroLocus_..._of_polynomialFamily U D (Fpoly : Tuple (Polynomial k) d)`:
  given `tupleEval Fpoly 0 = D` and `∀ t≠0, ∃ P, P • U = tupleEval Fpoly t`, concludes
  `canonicalCoord D ∈ zeroLocus(vanishingIdeal(orbitSet U))` (the Zariski closure). Over `[Infinite k]`.

ALREADY DONE (split case `c=b+1`): I realized the split downstairs `M_{[a,b]} ⊕ M_{[b+1,e]}` as a
"cut chain" `splitCut a e b : Tuple (intervalDim a e)` = `intervalModule a e` with the single edge `b`
zeroed. Family `splitFamilyPoly` carries parameter X on edge b (scalar). At t=0 → cut chain; at t≠0 I
used an EXPLICIT diagonal base change (scalar t at vertices > b). Computed `rankPattern_splitCut` by
induction (`submult_splitCut_eq_of_not_cross` / `_eq_zero_of_cross`). It works and lands the full §4
list headline with arbitrary `rest` (via a common-summand lemma + downstairs transport).

THE NON-SPLIT MOVE I now need (`a < c ≤ b < e`, genuine dim-2 overlap on [c,b]):
- Upstairs `U = M_{[a,e]} ⊕ M_{[c,b]}`, downstairs `D = M_{[a,b]} ⊕ M_{[c,e]}`. Same dim vector
  (move preserves dims): `intervalDim a e + intervalDim c b = intervalDim a b + intervalDim c e` (pointwise).
- Rank drop `r(U) - r(D) = 1` on the rectangle `D_rect = [a, c-1] × [b+1, e]`, else 0.
  i.e. `rankPattern U i j = [a≤i∧j≤e] + [c≤i∧j≤b]`, `rankPattern D i j = [a≤i∧j≤b] + [c≤i∧j≤e]`.
- The certified (1,2,1) witness (a=0,c=1,b=1,e=2): edge 1 (vertex1 dim2 → vertex2 dim1) is the
  recombination arrow. Upstairs edge1 = [1,0], downstairs edge1 = [0,1], family edge1 = [t,1].
  At t≠0 the family `[t,1]` has the SAME RANK PATTERN as upstairs (NOT equal to upstairs as a tuple).
  Off the recombination arrow, U = D (they agree).

MY PLAN (mirror the split case but use the rank-pattern route for t≠0, the lighter one):
1. Define the downstairs realized over the UPSTAIRS dim vector `d_up = foldDim [(a,e),(c,b)]` as a
   "recombined chain" `R` (constant tuple, agreeing with U off the recombination edge b, with edge b
   set to the downstairs recombination matrix [0,1]-pattern).
2. Define `Fpoly : Tuple (Polynomial k) d_up` = constant `R` with edge b's first-strand slot carrying X.
3. Prove `rankPattern (tupleEval Fpoly t) i j = rankPattern U i j` for ALL t≠0 (rank-pattern computation
   by induction on the sub-product, analogous to `submult_splitCut`), then `orbit_of_rankPattern_eq`
   gives the t≠0 base change WITHOUT building P(t) entrywise.
4. Prove `rankPattern R = rankPattern (intervalDirectSum [(a,b),(c,e)])` (block additivity), so R is
   G_d-equivalent to the genuine downstairs (transport).
5. Feed engine; glue rest via the common-summand wrapper (already built).

KEY DIFFICULTY: defining the matrices over `d_up = intervalDim a e + intervalDim c b` (values in {0,1,2})
through the `finSumFinEquiv`/`fromBlocks` reindexing of `dirSum`, and the rank-pattern induction with a
2-strand recombination arrow. The vertex dims VARY (0,1,2) along the chain.
</task>

<output_contract>
Answer in <= 5 sections, terse:
1. ROUTE VERDICT: is the rank-pattern route (step 3, prove `rankPattern(Fpoly t)=rankPattern(U)` for
   t≠0 via the complete invariant) sound and the lightest? Or is there a trap (e.g. the family at t≠0
   might NOT have the upstairs rank pattern for some i,j — give the discriminating i,j if so)?
2. THE RECOMBINED CHAIN: the single cleanest way to DEFINE `R` and `Fpoly` over `d_up`. Should I
   (a) define them as explicit `dirSum`-of-edited-interval-modules, (b) edit `intervalDirectSum [(a,e),(c,b)]`
   at edge b only, or (c) something else? Which minimizes `finSumFinEquiv` pain? Be concrete about what
   edge b's matrix is in each of the {2→1, 2→2, 1→1, ...} dim cases that arise as i ranges.
3. THE RANK-PATTERN INDUCTION: the cleanest formulation of the sub-product lemma(s) analogous to
   `submult_splitCut_eq_{of_not_cross, zero_of_cross}`. What is the right case split for the 2-strand
   arrow? Does the sub-product of `Fpoly t` factor as block-diagonal off the recombination, and how does
   the rank stay = upstairs across it (the t≠0 entry keeps the rank full)?
4. PITFALL CHECK: the WORST symbolic-indexing trap likely to eat 3+ build cycles, and how to sidestep it.
5. FALLBACK: if the general construction is genuinely a multi-module effort, what is the LARGEST clean
   sub-case I can bank now (e.g. the non-split move with NO rest, or only the rank-pattern equality, or
   a fixed small N)? Rank by value/effort.
</output_contract>

<grounding_rules>
Flag clearly which claims are (i) standard Lean/Mathlib facts you're confident about vs (ii) your
inference about my specific encoding that I must verify by building. Do not invent Mathlib lemma names;
if you reference one, mark it "verify name". The rank-drop formula and (1,2,1) witness numbers above are
exact (sympy-certified) — treat as ground truth.
</grounding_rules>
