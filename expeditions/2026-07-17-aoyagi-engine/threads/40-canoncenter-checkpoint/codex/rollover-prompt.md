<task>
A slot-bookkeeping question from Aoyagi (2023)'s recursive blow-up proof (paper pp.15-22, read from
page images). Derive the answer yourself; do not assume mine.

SETUP. The core object is a product of matrices C^(1)···C^(L), C^(s) of size M^(s) × M^(s+1)
(reduced widths). A resolution recursion diagonalises it layer by layer. State (S, J): the invariant is
   <∏ C^(s)> = < diag(b_1,…,b_{M(S)}) · (E_J O; O D_J) · ∏_{s=S+1}^L C^(s) >,
where M(S) = min{M^(1),…,M^(S)} (a RUNNING minimum), D_J = (d_ij) has rows J+1..M(S), cols J+1..M^(S+1),
and the pivot cleared at step J is the (J+1,J+1) entry. Within a layer, after clearing a pivot the
reduced residual D_{J+1} is RENAMED back to the d-symbols (d‴ → d), i.e. written back into the same
layer-S block's sub-slots. The next-layer matrix is transformed by a UNIPOTENT row-op:
C′^(S+1) = Q^{-1} C^(S+1) (left multiply; Q is built from layer-S's own d-entries).

ROLLOVER (the transpose boundary, pp.21-22): when J+1 > M(S+1) = min{M(S), M^(S+1)}, the layer-S residual
collapses — D‴_J = (1,0,…,0) (a row remnant) or (1,0,…,0)^t (a COLUMN remnant, "t = transpose"). Then
   <∏ C> = < diag(b_1,…,b_{M(S+1)}) · C′^(S+1) · ∏_{s=S+2}^L C^(s) >,   with S incremented to S+1, J reset to 0.
So the working block after rollover is C′^(S+1) (= Q^{-1} C^(S+1)), and processing continues in layer S+1.

STATIC SLOT MODEL (the thing to test). Assign each layer s a FIXED, disjoint block of "flat slots"
(an M^(s) × M^(s+1) grid of coordinate indices, computable from the widths alone). Claim: at every state
(S,J) the recursion's working block occupies exactly the STATIC layer-S slots, sub-block rows J+1..M(S),
cols J+1..M^(S+1) (running-min row bound); and at rollover the working block moves to the STATIC layer-(S+1)
slots, rows 1..M(S+1), cols 1..M^(S+2). Reused (merged) exceptional divisors are referenced by their
birth slot.
</task>

<output_contract>
Answer in ≤ 250 words, committing:
1. STABLE or UNSTABLE: at the rollover step (the one place content crosses layers), do the recursion's
   post-rollover working slots equal the STATIC layer-(S+1) slots (with running-min row truncation)?
2. THE TRANSPOSE: does the row-vs-column remnant (D‴ = (1,0,…,0) vs its transpose) re-orient or re-index
   the NEXT layer's block relative to the static slot grid — i.e., can it land content in slots the static
   model does not predict (a row/col swap, a leak into layer-S slots, a truncation picking non-contiguous
   rows)? Say why.
3. THE Q-TRANSFER: is C′^(S+1) = Q^{-1}C^(S+1) a slot-preserving operation (entry (i,j) stays at slot
   (i,j) of layer S+1)? One sentence.
4. If UNSTABLE, name the exact failure (which widths, which slot).
</output_contract>

<grounding_rules>
- Reason from the matrix bookkeeping only: dims M(S)=running-min, D_J = rows J+1..M(S) × cols J+1..M^(S+1),
  the left-multiply Q^{-1} on C^(S+1), and the transpose collapse. Distinguish VALUES (entries may mix
  earlier-layer content via Q) from SLOTS (which coordinate index stores each entry) — the question is
  about SLOTS.
- Commit to STABLE or UNSTABLE. Do not restate my setup; give the derivation and the verdict.
</grounding_rules>
