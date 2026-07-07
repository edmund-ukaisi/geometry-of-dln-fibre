1. **Encoding.** Yes, for the terminal monomial carrier, `e : Fin numGen → Fin numExc → ℕ` is the right minimal datum. Shared versus fresh divisors are exactly column identity: for `⟨δx, δy⟩`, rows `[1,1,0]`, `[1,0,1]` give `k = [1,0,0]`; for fresh `δ₁,δ₂`, the `δ₁` and `δ₂` columns have minima `0`. Signs, blow-up order, and centers are not needed to consume the terminal support matrix, though they are needed to prove that the matrix was produced faithfully. Two Lean cautions: require `0 < numGen` or `[NeZero numGen]`; and define the minimum with `Finset.univ.inf'`, not an empty-default `0`, except in quarantined degenerate code.

2. **Factorization Lemma.** Correct, and Lean-provable. State it using `residualSupport`, not literal division by `g`; division fails semantically at `g = 0`. For each `i, ℓ`, prove `sharedDivisorExp e ℓ ≤ e i ℓ`, then
   `|u ℓ| ^ e(i,ℓ) = |u ℓ| ^ kℓ * |u ℓ| ^ (e(i,ℓ)-kℓ)`
   by `pow_add` plus the Nat subtraction lemma. Zero coordinates are fine: this is Nat-power algebra in a semiring, so `0^k` causes no trap, including exponent `0`. Then use product distributivity and pull the common square out of the finite sum.

3. **`monomialIntegrand`.** Yes: pass `kℓ := sharedDivisorExp e ℓ`, not `2*k`. One proves
   `commonDivisor e u ^ 2 = ∏ ℓ, |u ℓ| ^ (2 * k ℓ)`
   using `Finset.prod_pow`, `pow_mul`, and `Nat.mul_comm`. For the real-power split, prefer the shape
   `(G * U) ^ (-c') = G ^ (-c') * U ^ (-c')`
   with `0 ≤ G` and `0 ≤ U`; if you have the terminal unit witness, `1 ≤ U`, even better. Also ensure the banked threshold treats `kℓ = 0` as imposing no bound; otherwise fresh-only columns become misleading.

4. **Relative Chart Lemma.** Make the step theorem generator-level, not merely Frobenius-square-level. The useful shape is: define a computable `radialUpdate : SJState → StepData → SJState` whose support is old columns copied/incremented monotonically and one fresh column appended, with value `1` on active descendants and `0` on passive rows, or the explicit multiplicity if not always `1`.

The lemma should assert:
`loss_after = ∑ i, genMonomial state'.support i u' ^ 2`,
old exceptional exponents never decrease, the fresh column is exactly the radial ledger column, the unit/residual witness is preserved or updated, and the recursion measure decreases.

Sharpest risk: `pref · frobSq = pref · u² · residual` is too coarse to recover the support matrix. Shared-divisor faithfulness must be proved row-by-row for generators; a sum-of-squares equality alone does not certify which generators share `u`.