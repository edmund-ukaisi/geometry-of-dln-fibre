**Section 1: VERDICT**

sound for the `←` direction as skeletoned.

**Section 2: Key Questions**

1. (FACT: Matrix semantics) For `C = A.submatrix er ec` and `B = A.submatrix er id`, `C.col j = fun i ↦ A (er i) (ec j)`, while `Bᵀ.row (ec j) = fun i ↦ B i (ec j) = fun i ↦ A (er i) (ec j)`.  
   (INFERENCE) So the identity `C.col = fun j ↦ Bᵀ.row (ec j)` is genuinely correct. The selected independent rows of `Bᵀ` are exactly the selected columns of `B`, restricted to the already-fixed row set `er`, hence exactly the columns of `C`.

2. (FACT: assuming the stated support lemmas) No circularity is visible in the hard direction. It uses row-span rank, transpose rank, and the square invertibility criterion from column independence; it does not use the determinant-rank criterion being proved.  
   (INFERENCE) The only `cRank` bridge mentioned is in `rank_submatrix_le_rank`, which belongs to the easy direction/support layer, not the construction of the nonzero minor.

3. (FACT: Matrix index flow) The square block is not drifting: `er` is fixed before forming `B`, and `ec` is chosen among rows of `Bᵀ`, i.e. among columns of that same `B`.  
   (INFERENCE) Therefore `C = A.submatrix er ec` is precisely the `(r+1) × (r+1)` block whose columns are the independent vectors obtained from `Bᵀ`; there is no mismatch between the selected columns and the row restriction.

4. (FACT: assuming `exists_injective_linearIndependent_rows` as stated) No extra explicit hypotheses `r+1 ≤ p` or `r+1 ≤ q` are needed. Applying the lemma to `A` with `r+1 ≤ A.rank` produces the injection into `Fin p`; applying it to `Bᵀ` with rank `r+1` produces the injection into `Fin q`.  
   (INFERENCE) If either cardinal bound failed, the corresponding rank inequality would be impossible; the construction discharges the bounds internally through the existence of the injections.

**Section 3: Other Holes**

none. The main fragile point is exactly the column identity in Step 2(4), but the indices line up correctly.