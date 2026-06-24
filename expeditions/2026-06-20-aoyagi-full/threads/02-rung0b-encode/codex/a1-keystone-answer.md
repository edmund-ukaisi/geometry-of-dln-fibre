**1. ROUTE RANKING**

R1. **Avoid.** Mathematically natural, but it forces `descentSet T → Fin c_T` and then transports gaps, widths, and sums through a `T`-dependent type. This is exactly the historical thrash point.

R2. **Viable but risky.** It avoids descent reindexing, but the needed closed form for `g(top, tail)` is essentially the same theorem for the multiset `{top} ∪ tail`; the IH must track a changing sort and changing `cstar`. Treat any closed form here as a new conjectural lemma to verify before formalising.

R3. **Viable if sharpened.** The right version is not a direct bound on `Mval`, but a fixed-length edge-variable transform reducing everything to `q : Fin L → Nat` and a water-filling/majorization theorem.

R4. **Best.** Use the fixed `q` transform plus a water-filling certificate. This keeps the index set `Fin L` fixed for every admissible `T`; the only smaller type is `Fin cstar`, fixed by `M`, not extracted from `T`.

**2. CHOSEN ROUTE**

Use the clean admissibility reframe with `u₀ = M₀`, `u_{j+1}=T_j`, `u_L=0`.

1. `Adm_iff_u`
   `T ∈ Adm M` iff `u₀=M₀`, `u_L=0`, `u₀ ≥ u₁ ≥ ... ≥ u_L`, and `u_j ≤ M_j` for `1≤j≤L`.

2. Define fixed edge variables:
   `q_j := M_{j+1} + (u_j - u_{j+1})`, for `j : Fin L`.

   Prove the fixed-index square identity:
   `2 * Mval M T = ∑_{j<L} q_j^2 - ∑_{i≤L} M_i^2`.

   This is CERTAIN algebra: expand `q_j^2` and telescope
   `∑ ((u_j)^2 - (u_{j+1})^2) = M₀^2`.

3. Define `QFeasible M q`:
   `∑ q_j = ∑ M_i`;
   `M_{j+1} ≤ q_j`;
   for every prefix `n≤L`,
   `∑_{j<n} M_j ≤ ∑_{j<n} q_j ≤ ∑_{j<n} M_j + M_n`.

   Then prove:
   `T ∈ Adm M → QFeasible M (edgeQ M T)`;
   conversely, from `QFeasible M q`, define
   `u_n := M_n + ∑_{i<n} M_i - ∑_{j<n} q_j`,
   and get an admissible `T`.

4. Let `a₀≤...≤a_L` be `M` sorted. Let `c=cstar`, `P=∑_{i≤c} a_i`, `b=P/c`, `r=P%c`.

   Define the target sorted `q`-multiset:
   `β_i = b` for `i < c-r`, and `β_i = b+1` for `c-r ≤ i < c`;
   `Y = {β₀,...,β_{c-1}} ∪ {a_{c+1},...,a_L}`.

5. Main lower-bound lemma, NEW / INFERRED:
   `waterfill_sq_min`:
   for every `q : Fin L → Nat`,
   `QFeasible M q → ∑_{y∈Y} y^2 ≤ ∑_{j<L} q_j^2`.

   Formal proof route: sort `q`; prove sorted `q` majorizes `Y`; apply a convexity/Abel-summation lemma for squares.

6. Existence lemma, NEW / INFERRED:
   `waterfill_target_feasible`:
   there exists `q* : Fin L → Nat` with `QFeasible M q*` and `q*` a permutation of `Y`.

   Use the greedy placement described below.

7. Combine:
   `min_T Mval M T = (1/2) * (∑Y^2 - ∑M_i^2)`
   `= (1/2) * (∑_{i<c} β_i^2 - ∑_{i≤c} a_i^2)`.

8. Plug-ins:
   `balancedSplit_min`: used inside `waterfill_sq_min` after the water-filling reduction isolates the active `c` slots with total `P`.
   `balancedSplit_sq_int`: rewrites `∑ β_i^2` as `c*b^2 + r*(2*b+1)`.
   `cleanCore_perm`: makes all tie/order choices among the `c+1` smallest widths irrelevant when matching the constructed small-width multiset to `sortedSmallest M c hc`.

**3. HARDEST SUB-STEP**

Hardest lemma: `waterfill_sq_min`.

Concrete tactic plan:

1. Work with `Finset.range` prefix sums, not dependent sub-`Fin`s.
2. Define sorted vectors `x = sort q` and target `Y`.
3. Prove `majorizes x Y` as:
   `∀ n≤L, ∑_{i<n} x_i ≤ ∑_{i<n} Y_i`, with equal total sums.
4. Prove generic convex lemma:
   if sorted `x,y` have equal total and `x` majorizes `y`, then `∑ y_i^2 ≤ ∑ x_i^2`.

   Use Abel summation with prefix differences
   `D_n = ∑_{i<n} (x_i-y_i)`.
   Prefix majorization gives `D_n≤0`; sortedness gives `(x_n+y_n)` increasing; the summation-by-parts signs give the square inequality.

5. The `cstar` arithmetic enters in two small lemmas:
   good `c` gives `a_{i+1} ≤ β_i` for `i<c`;
   maximality gives the tail gap `β_{c-1} < a_{c+1}` when `c<L`.

**4. ACHIEVER T\***

Sorted case first. Suppose `M_i=a_i`.

Define `β` as above and set

`u_j = ∑_{i=j}^{c-1} (β_i - a_{i+1})` for `1≤j≤c`,
`u_0=a_0`,
`u_j=0` for `j>c`.

Then `T*_j = u_{j+1}`.

Admissibility:
`β_i ≥ a_{i+1}` gives nonnegative gaps, so `u` is decreasing. Also
`a_j - u_j = ∑_{i<j} β_i - ∑_{i<j} a_i ≥ 0`,
so `u_j≤a_j`. Finally `u_L=0`.

Value:
`u_i-u_{i+1}=β_i-a_{i+1}` for `i<c`, and zero afterward, so the edge variables are
`q_i=β_i` for `i<c`, and `q_i=a_{i+1}` for `i≥c`.

Thus
`2*Mval M T* = ∑β_i^2 - ∑_{i≤c} a_i^2`,
hence
`Mval M T* = Vstar`.

For unsorted `M`, use the same target multiset `Y`, then greedily place it into original edge positions. At step `j`, with previous sum `Q_{<j}`, set

`need_j = max(M_{j+1}, ∑_{i≤j} M_i - Q_{<j})`

and choose the least remaining element of `Y` at least `need_j`. This gives `q*`. Then define

`u*_n = M_n + ∑_{i<n} M_i - ∑_{j<n} q*_j`,
`T*_j = u*_{j+1}`.

The greedy feasibility lemma is part of `waterfill_target_feasible`.

**5. REINDEX-AVOIDANCE**

Do not extract `c_T`, descents, breakpoint widths, or a `Fin c_T`.

Every arbitrary admissible `T` is sent to a fixed-length `q : Fin L → Nat`. The lower bound compares this fixed `q` to the single global target multiset `Y(M,cstar)`. The only `Fin c` that appears is `Fin cstar`, fixed once from sorted `M`; it never depends on `T`.