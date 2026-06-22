1. **Induction scheme:** Induct on `N` for the theorem stated as `d : Fin (N+1) → ℕ`; in the successor step use `d : Fin (N+2) → ℕ`, peel `Fin.last (N+1)`, and set the residual vector to `d₀ := d ∘ Fin.castSucc : Fin (N+1) → ℕ`.

2. **Forward map `m ↦ m'`:** define `m' : Fin (N+1) × Fin (N+1) → ℕ` by case-splitting on the residual column:
   ```lean
   -- schematic
   m' (i, j) :=
     Fin.lastCases
       (m (Fin.castSucc i, Fin.castSucc (Fin.last N))
        + m (Fin.castSucc i, Fin.last (N+1)))
       (fun j₀ : Fin N =>
         m (Fin.castSucc i, Fin.castSucc (Fin.castSucc j₀)))
       j
   ```
   The pitfall is the boundary column: residual `Fin.last N` represents original column `N`, and must absorb original column `N+1`. Do not hide this behind a broad `if j = last`; `Fin.lastCases` gives better simp equations. The off-support `if i ≤ j` obligations are routine except for the merged boundary column, where the range bound uses the vertex equation, not componentwise membership alone.

3. **`List` bridge:** keep `transferRHS` over `List`. Use
   ```lean
   let b := List.ofFn (fun i : Fin (N+1) => m' (i, Fin.last N))
   ```
   in the successor step. Add small bridge lemmas relating `(b.map P).prod` to the corresponding `Fin` product. I would not restate `transferRHS` over `Fin` unless the list lemmas become dominant.

4. **Summation lemma:** use `Finset.sum_bij'`. Make the codomain a sigma-shaped finset:
   ```lean
   smallPartitions.sigma (fun m' => admissibleXs m')
   ```
   so the bijection is `m ↔ ⟨m', x⟩`. Then the fibrewise form is obtained from the sigma structure, via `Finset.sum_sigma` if you need the explicit nested sum. I would avoid `sum_fiberwise`: it leaves fibres as big partitions and forces a second bijection to the `x` data.

5. **Hardest Lean step, inference:** proving `m' ∈ kostantPartitions d₀ r'`, especially `kostantAt` at the new last vertex and the merged-column range bound. That step combines `Fin.castSucc` arithmetic, the support `if i ≤ j`, and the boundary merge.