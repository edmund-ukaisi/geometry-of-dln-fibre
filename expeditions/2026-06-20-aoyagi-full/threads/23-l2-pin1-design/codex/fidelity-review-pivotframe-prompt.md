You are a decorrelated second-model reviewer auditing a Lean 4 / Mathlib formalisation
for SOUNDNESS and FIDELITY. Reason from the mathematics; do not trust my framing.

CONTEXT: A "pivot-aligned boundary frame fact" lemma. The prior two attempts in this area
were REFUTED (unsound), so be adversarial.

THE THEOREM (informal):
  Given a real matrix A : Fin a × Fin b with A.rank = r, whose TAIL ROWS vanish
  (A i j = 0 whenever (i:ℕ) ≥ r), and r ≤ a, r ≤ b. Then there exist:
    - a column-index embedding J : Fin r ↪ Fin b (a "pivot column set"),
    - a UNIT (invertible) matrix Q : Fin b × Fin b,
  such that, writing
    e := pivotThresholdSplit r b J : Fin b ≃ Fin r ⊕ Fin (b-r)
         -- the LEFT block of e enumerates the r PIVOT columns Set.range J in sorted order,
         --   the RIGHT block the complement (b-r columns),
    rsplit := rThresholdSplit r a : Fin a ≃ Fin r ⊕ Fin (a-r)
         -- LEFT block = first r row-indices {0..r-1}, RIGHT = {r..a-1},
  we have:
    (1) IsUnit Q
    (2) IsUnit ((reindex e e Q).toBlocks₂₂)          -- lower-right block under the PIVOT split is a unit
    (3) reindex rsplit e (A * Q) = fromBlocks 1 0 0 0  -- the (r×r) identity corner, all else 0

CONSTRUCTION USED:
  V := top-r-rows of A (V : Fin r × Fin b, V.rank = r — proved separately by a zero-padding argument).
  J := pivot columns of V (∃ J, IsUnit (V.submatrix id J), i.e. the r×r block of V at columns J is invertible).
  In the SORTED pivot order of e: VJ := the r×r block of V at the pivot columns (a unit),
       VK := the r×(b-r) block of V at the complement columns.
  Q̃ := fromBlocks VJ⁻¹ (−VJ⁻¹·VK) 0 1   (block 2×2 over Fin r ⊕ Fin (b-r))
  Q  := reindex e.symm e.symm Q̃   (so reindex e e Q = Q̃).

CLAIMS TO AUDIT (be a referee — find the hole or confirm none):
  Q1. Is (2) actually delivered? reindex e e Q = Q̃ = fromBlocks VJ⁻¹ (−VJ⁻¹VK) 0 1, so its
      toBlocks₂₂ = 1 (identity), trivially a unit. Is toBlocks₂₂ of a fromBlocks the (2,2) corner? Yes?
  Q3. Is (3) correct? reindex rsplit e A: top blocks come from V's pivot/complement cols (= VJ, VK),
      bottom blocks come from rows ≥ r which VANISH by tail-rows-hypothesis (= 0, 0). So
      reindex rsplit e A = fromBlocks VJ VK 0 0. Then fromBlocks VJ VK 0 0 * fromBlocks VJ⁻¹ (−VJ⁻¹VK) 0 1
      = fromBlocks (VJ·VJ⁻¹) (VJ·(−VJ⁻¹VK)+VK) (0) (0) = fromBlocks 1 0 0 0. Correct?
  Q4. SOUNDNESS TRAP CHECK: Does this secretly RESTRICT B / A — e.g. force the pivot columns to be
      the FIRST r columns, or force B's first r columns independent? The prior unsound fix did exactly
      that. Here: is there ANY hidden assumption that the bottom blocks of reindex rsplit e A vanish
      that depends on J or on the column ordering — or is it PURELY the tail-rows-vanish hypothesis
      (rows ≥ r) combined with the ROW split being threshold (first r on top)? I claim the row-block
      vanishing is independent of J (J only governs columns). Verify or refute.
  Q5. Is the lemma NON-VACUOUS — does a rank-r A with vanishing tail rows and r≤a, r≤b actually exist
      for, say, r=1, a=b=2, A=[[0,1],[0,0]] with pivot column = column 1 (NOT the first column)?
      Work this example: what are V, J, VJ, VK, Q̃, Q, and verify (1),(2),(3) concretely. Confirm the
      B22=1 is in the PIVOT indexing (column 1 is the pivot), not a re-disguised "first-r-columns" claim.

Give a verdict per question: SOUND / HOLE (with the specific gap). Especially hammer Q4 and Q5.
