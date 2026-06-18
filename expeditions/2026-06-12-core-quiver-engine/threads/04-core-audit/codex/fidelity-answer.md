1. **mult** — **FACT:** Yes. `A i : Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k` is paper `A_{i+1} : k^{d_i} → k^{d_{i+1}}`, and `multPrefix` gives `A_{N-1} * ... * A_0`, i.e. paper `A_N ··· A_1`. Codomain is `d_N × d_0`. Discrepancy: Lean assumes `[CommRing k]`, while the paper says field.

2. **loci + fibre** — **FACT:** `productRankLocus` matches `{rank(mult A_*) = r}`. `fibre` matches `{A_* | mult A_* = B}`. `productRankLocusLE` uses `≤ r`, not `≥ r`. **INFERENCE:** `≤ r` is the standard Zariski determinantal closure of the rank-`r` stratum when that stratum is nonempty/attainable and the usual algebraic-geometry hypotheses are in force. Lean does not encode that closure theorem; for unattainable `r`, `rank = r` may be empty while `rank ≤ r` need not be.

3. **Prop 3.1a** — **FACT:** `diff_apply` matches exactly
   `r i j - r i (j+1) - r (i-1) j + r (i-1) (j+1)`.
   `cumul_apply` is `∑ k ∈ Icc 0 i, ∑ l ∈ Icc j N, m k l`, matching the paper’s `Σ_{k ≤ i ≤ j ≤ l}` on valid paper indices `0 ≤ i ≤ j ≤ N`. **FACT:** `Supported` realizes the stated boundary convention `i < 0` and `j > N`; it does not encode the whole upper-triangular domain. **FACT:** inversion is genuinely two-sided: both `diff_cumul` and `cumul_diff` are stated.

4. **Supported** — **FACT:** `Supported` is closed under the guard-free `cumul`/`diff` equivalence. **INFERENCE:** It is not the full paper support invariant: the finite box `0 ≤ i,j ≤ N` and upper-triangular condition `i ≤ j` are not part of the subtype, so the Lean equivalence is over a larger array space.

5. **Naming** — **FACT:** `rankPatternEquiv` proves an abstract inversion on `{f // Supported N f}` over `[AddCommGroup R]`. **INFERENCE:** The name overclaims if read as paper rank patterns: there is no rank-specific condition, no nonnegativity, no finite upper-triangular subtype, and no admissibility/monotonicity.

6. **Fidelity gaps / risks** — **FACT:** field hypotheses are absent in Module 1. **FACT:** Prop 3.1a is formalized over `ℤ`-indexed arrays with `N : ℤ`, not finite upper-triangular arrays with natural `N`. **INFERENCE:** The main vacuity risk is interpreting `productRankLocusLE` as an actual closure without hypotheses ensuring rank `r` is attainable and dense in `rank ≤ r`.