**PIECE 1**
(i) Cleanest decomposition:

`edgeQ_QFeasible` — follows from proven corridor facts.
For `T ∈ Adm M`, `q := edgeQ M T` satisfies total `∑q = ∑M`, nonnegativity, `q_j ≥ M_{j+1}`, and positional corridor
`∑_{j<n} M_j ≤ ∑_{j<n} q_j ≤ ∑_{j≤n} M_j`.

`targetY_sorted_prefix` — new arithmetic lemma, needs check.
For `Y = β(S_c,c) ⊕ tail`, with `c=c*`:
- if `k ≤ c`, `prefix_k(srt Y) = prefix_k(srt β)`;
- if `k > c`, `prefix_k(srt Y) = S_k`.
This depends on `max β ≤ a_{c+1}`.

`QFeasible_target_majorization` — the real new bridge.
For every `q` satisfying `QFeasible M q`,
`∀ k ≤ L, prefix_k(srt q) ≤ prefix_k(srt Y)`.

Then apply the already-proven `sq_sum_le_of_sorted_prefix`.

(ii) Key point:

Do **not** use the first `k` original positions. The positional corridor gives original-order prefixes; `Y` is sorted-width data. For unsorted `M`, your displayed regime proof does not compose. The correct lower-bound handoff is the single order-statistic lemma `QFeasible_target_majorization`.

Recommendation for Q1a: **NO global sorted-reduction first.** Proving `lambdaCore M = lambdaCore (sort M)` is harder than the local theorem. But also **NO** to the raw first-position argument on unsorted `M`.

(iii) Failure point:

The numeric domination can mask a real design gap: `QFeasible_target_majorization` is not a consequence of the listed engines unless you prove a Hall/water-filling/order-statistic lemma reconciling positional corridors with sorted prefixes.

**PIECE 2**
(i) Cleanest decomposition:

`balanced_prefix_closed_form` — new elementary lemma.
Let `b = P / m`, `r = P % m`. For `0 ≤ k ≤ m`,
`prefix_k(srt (balancedSplit P m)) = k*b + max(0, k + r - m)`.
Needs check, but this is the ascending-sort formula.

`sorted_prefix_le_balanced_of_sum_le` — main Step B.
For `q : Fin m → ℕ`, `∑q ≤ P`,
`prefix_k(srt q) ≤ prefix_k(srt (balancedSplit P m))`.

(ii) Key inequality:

Sort `q` ascending as `x`. Suppose
`A := ∑_{i<k} x_i > k*b + e`, where `e = max(0, k+r-m)`.
Then `A ≥ k*b + e + 1`, hence for `k>0`, `x_{k-1} ≥ b+1`. Since the tail entries are all `≥ x_{k-1}`,
`∑ x ≥ A + (m-k)(b+1) ≥ m*b + r + 1 = P+1`,
contradicting `∑q ≤ P`.

(iii) Failure point:

Your suggested closed form `k*b + min(k,r)` is for the wrong end of the sorted vector. For ascending `k`-smallest prefixes the correction term is `max(0, k+r-m)`. Using `min(k,r)` will silently prove a false identity.

**PIECE 3**
(i) Cleanest decomposition:

Do **not** prove global permutation invariance first.

`targetY_feasible_order` — new achiever existence lemma.
There exists `q* : Fin L → ℕ`, a permutation of `Y`, such that `QFeasible M q*`.

Best construction: greedy original-order placement. At edge `j`, with prefix `Q_j`, choose the least remaining `y ∈ Y` in the interval
`max(M_{j+1}, A_j - Q_j) ≤ y ≤ A_{j+1} - Q_j`,
where `A_j = ∑_{i≤j} M_i`.

`QFeasible_to_Adm` — clean inverse.
Given `QFeasible M q`, define
`u_n = ∑_{i≤n} M_i - ∑_{j<n} q_j`,
then `T_j = u_{j+1}`. Corridor gives `0 ≤ u_n ≤ M_n`; `q_j ≥ M_{j+1}` gives `u_j ≥ u_{j+1}`; total gives `u_L=0`.

`edgeQ_of_QFeasible_inverse`.
For this `T`, `edgeQ M T j = q j`.

Then use `edge_identity`, permutation invariance of square sums, and `Finset.inf'_le`.

(ii) Key identity:

`u_j - u_{j+1} = q_j - M_{j+1}`.

This makes admissibility and edge recovery immediate once `q*` is feasible.

Recommendation for Q3: **YES explicit unsorted witness, but construct it as `q*` first, then invert to `T*`.** A sorted-prefix formula for `T*` is clean only when `M` is already sorted.

(iii) Failure point:

`targetY_feasible_order` is the remaining design-sensitive lemma. The greedy interval must have a remaining element at every step; numerics do not replace the Hall/invariant proof.

**GO/NO-GO:** NO-GO as “pure Lean execution” until `QFeasible_target_majorization` and `targetY_feasible_order` are isolated and proved; after those two, the rest is assembly.