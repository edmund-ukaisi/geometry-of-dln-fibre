<task>
Lean 4 + Mathlib design review. I need the cleanest Lean route for obligation (c): an
order-isomorphism `bindingSet M ≃o bindingSet (sortedWidths M)`, reusing an already-designed
one-adjacent-swap iso.

GIVEN (being proved by another seat, treat as available):
`swapBinding_orderIso (M) (k : Fin L) : Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (swapWidths k M)))`
where `swapWidths k M` swaps the two ADJACENT width entries M_k, M_{k+1} (k.castSucc, k.succ in
Fin (L+1)), and the profile is transported by a value-preserving `swapR`. Proved: `swapWidths_swapWidths`
(involution). `sortedWidths M = M ∘ Tuple.sort M` (Mathlib `Tuple.sort`, ascending).

Mathlib scouted: `Tuple.sort` API present (self_comp_sort, comp_perm_comp_sort_eq_comp_sort,
sort_eq_refl_iff_monotone, monotone_sort) — but NO off-the-shelf "Equiv.Perm (Fin n) = product of
ADJACENT transpositions".

MY WORKING DESIGN (red-team this): well-founded recursion on the INVERSION COUNT of M
(#{(i,j) : i<j ∧ M i > M j}):
- if inversions = 0, M is monotone, sortedWidths M = M (sort_eq_refl_iff_monotone), transport = OrderIso.refl;
- else ∃ adjacent k with M_k > M_{k+1} (an unsorted tuple has an adjacent descent); apply
  swapBinding_orderIso at k → bindingSet M ≃o bindingSet (swapWidths k M); swapWidths k M has ONE
  FEWER inversion; recurse; compose with OrderIso.trans.
- terminate: the composed widths are sorted, = sortedWidths M (both sorted + same multiset ⟹ equal).
</task>

<output_contract>
Concise, four sections:
1. VERDICT on my inversion-count recursion: viable in Lean 4 / Mathlib v4.29? Cleaner alternative?
   (e.g. induction on List.length of an adjacent-transposition factorization; insertionSort structure;
   Coxeter/symmetric-group adjacent-generation if Mathlib has it — name the exact lemma if so.)
2. The KEY sub-lemmas + their Mathlib support: (a) "unsorted ⟹ ∃ adjacent descent"; (b) "swapping an
   adjacent descent strictly decreases inversion count"; (c) "composed-sorted + same-multiset = sortedWidths".
   For each, the Mathlib lemma name if it exists, else "build it" + difficulty.
3. The Fin-index / dependent-type hazards in composing the isos across the recursion (the widths change
   type-family index? no — Fin (L+1) fixed; but swapWidths k M is a NEW width function each step).
4. Is there a SHORTCUT avoiding the adjacent decomposition entirely (e.g. a permutation-covariance of
   bindingSet under a joint width+profile permutation)? If yes, sketch it; if no, say why (the
   value-preserving transport is inherently pairwise-adjacent).
</output_contract>

<grounding_rules>
Distinguish Mathlib lemmas you're confident exist (name them) vs guesses (flag). If you assert a lemma
name, it must be plausible at v4.29. Flag any step where my recursion hides a real difficulty.
</grounding_rules>
