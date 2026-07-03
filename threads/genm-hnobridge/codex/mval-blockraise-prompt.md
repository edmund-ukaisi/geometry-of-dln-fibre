<task>
Lean 4 + Mathlib v4.29. I need the cleanest tactic strategy for a finite-sum
"perturbation" computation. I have a hand-verified proof; I want your independent
read on the SLICKEST Lean packaging of ONE step (the Mval delta), and whether
there's a trap.

CONTEXT (definitions, all fixed):
- `L : ℕ`, `M : Fin (L+1) → ℕ`.
- `tPrev M T j : ℤ := if j.val = 0 then (M 0 : ℤ) else (T ⟨j.val-1, _⟩ : ℤ)`  for `T : Fin L → ℕ`, `j : Fin L`.
- `Mval M T : ℤ := ∑ j : Fin L, (tPrev M T j - (T j : ℤ)) * ((M j.succ : ℤ) - (T j : ℤ))`.
- `tStar M : Fin L → ℕ` is a fixed argmin: `Mval M (tStar M) = (Adm M).inf' _ Mval = minAdm`.
- `Text M t k : ℕ` with `Text (tStar-shifted path) (s) = tStar(s-2)` for s≥2, `Text 1 = Text 0 = M0`.
  Concretely along the achiever path: write `T(k)` for the row-rank at chain boundary k.
  `tStar(j) = T(j+2)`.  Define `r_s := T(s) - T(s+1) ≥ 0`, `c_s := M s - T(s+1) ≥ 0` (s in [1,L]).
  `Mval M (tStar M) = ∑_{s=1}^{L} r_s c_s = minAdm`.

THE STEP I want the cleanest Lean for:
I have integers `q, b` with `1 ≤ q ≤ b-1 ≤ L-2` (so all interior), a ROW-DROP at q
(`r_q ≥ 1`), FLATNESS `r_s = 0` for `s ∈ [q+1, b-1]`, a COL-DROP tail `c_s ≥ 1` for
`s ∈ [q, b-1]`, and `c_b = 0`.
I define a NEW admissible tuple `T' : Fin L → ℕ` by
   `T'(j) = tStar M j + (if (q-1 ≤ j.val ∧ j.val ≤ b-2) then 1 else 0)`.
(I.e. raise `tStar` by 1 on the contiguous index block `[q-1, b-2]`, equivalently raise
`T(s)` by 1 for `s ∈ [q+1, b]`.)
I have SEPARATELY proven `T' ∈ Adm M`.
I need:  `Mval M T' = Mval M (tStar M) + (1 - r_q - c_q)`  (hence `≤ minAdm - 1 < minAdm`,
contradicting `Finset.inf'_le`).

By hand: `Mval M T' - Mval M (tStar M) = ∑_j (f'(j) - f(j))` where
`f(j) = (tPrev(tStar) j - tStar j)(M j.succ - tStar j)`. Only j in `[q-1, b-1]` (Fin L index)
contribute. The three groups:
  - j = q-1 : the only surviving nonzero delta, equals `1 - r_q - c_q`;
  - j ∈ [q, b-2] : delta = `- r_{j+2}` which is 0 by flatness;
  - j = b-1 : delta = `c_b` which is 0.
So total = `1 - r_q - c_q`.

QUESTIONS:
1. Rank the Lean strategies for proving `Mval M T' - Mval M (tStar M) = 1 - r_q - c_q`:
   (a) `Finset.sum_congr`/`Finset.sum_sub_distrib` then split the index set `Fin L` into the
       block `[q-1,b-1]` and its complement (complement terms cancel: `f'(j)=f(j)`), then a
       finite explicit split of the ≤3 groups;
   (b) reindex `Fin L → ℕ` via `Finset.sum_range` / `Fin.sum_univ_eq_sum_range` and work on
       `ℕ`-intervals with `Finset.sum_Ico_consecutive`;
   (c) a telescoping/`Finset.sum_Ico_eq_sub` trick.
   Which is least painful given the `if`-in-the-summand and the `tPrev` `if j.val=0` branch?
2. The `tPrev M T' j` for `j` where `j-1 ∈ block` but `j ∉ block` (the top boundary `j=b-1`)
   reads `T'(j-1) = tStar(j-1)+1`. What is the cleanest way to handle the `tPrev` `if j.val=0`
   guard interacting with the block membership `if`, to avoid a combinatorial explosion of cases?
3. Is there a slicker route: define `g(j) := f'(j) - f(j)` and prove `∑_j g(j) = g(q-1)` by
   showing `g(j) = 0` for `j ≠ q-1` (using flatness + c_b=0 + block-interior cancellation),
   via `Finset.sum_eq_single`? Would that be cleaner than an interval split?
4. Any TRAP you see in the delta arithmetic itself (sign, off-by-one in the block `[q-1,b-2]`
   vs the affected-index set `[q-1,b-1]`, the `Fin L` vs `ℕ` `j.val-1` casts in `tPrev`)?

Keep it concrete and Lean-v4.29-accurate.
</task>

<output_contract>
1. A ranked recommendation (1 short paragraph) of the single best strategy for Q1/Q3, with the
   key Mathlib lemma names (v4.29 spellings).
2. The cleanest handling of Q2 (the tPrev boundary), 3-6 lines.
3. Q4: a bulleted list of concrete traps (only real ones; say "none seen" per item if clean).
4. If you'd sanity-check the delta = 1 - r_q - c_q claim, show the 3-group arithmetic explicitly
   so I can cross-check my hand derivation.
Be terse. No prose padding.
</output_contract>

<grounding_rules>
Flag any lemma name you are not sure exists in Mathlib v4.29 as "verify". Distinguish
"this will work" (you're confident) from "likely / try" (inference).
</grounding_rules>
