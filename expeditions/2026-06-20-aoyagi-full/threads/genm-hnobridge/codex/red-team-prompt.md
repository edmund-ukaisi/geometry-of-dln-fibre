# Decorrelated red-team: `¬InteriorDrop ⟹ NoInteriorBothDrop` and the argmin-exchange

You are an independent adversarial reviewer. Reason from scratch; do not assume the claim is true.
Answer the two questions at the end with an explicit verdict and, where possible, a concrete
counterexample or a proof sketch. Distinguish clearly which of your statements are FACTS you can
justify vs INFERENCES/CONJECTURES.

## Setup (a finite combinatorial optimisation, no probability/geometry needed)

Fix `L ≥ 1` and a width vector `M : {0,1,...,L} → ℕ` (nonneg integers), `M(0),...,M(L)`.

Define the admissible cone of exponent vectors `T = (T(1),...,T(L))` with `T(j) ∈ ℕ`:
`admPred(T)` holds iff ALL THREE:
1. (per-layer bound)  `T(1) ≤ min(M(0), M(1))`, and for `j ≥ 2`, `T(j) ≤ M(j)`.
2. (weak-decrease)     `T(1) ≥ T(2) ≥ ... ≥ T(L)`.
3. (last-zero)         `T(L) = 0`.

Define the objective (over ℤ; write `T(0) := M(0)` by convention):
`Mval(T) = Σ_{j=1}^{L} ( T(j-1) − T(j) ) · ( M(j) − T(j) )`.
Both factors are ≥ 0 for admissible T (weak-decrease gives `T(j-1) − T(j) ≥ 0`; per-layer bound
gives `M(j) − T(j) ≥ 0`; for j=1, `M(1) − T(1) ≥ 0`). So `Mval(T) ≥ 0` on the cone.

Let `tStar` be a minimizer of `Mval` over the (finite, nonempty) admissible cone, and
`minAdm = Mval(tStar) = min_T Mval(T)`.

Now define the compressed-width sequence along this fixed minimizer:
`T(0) = M(0)`, and `T(k+1) = tStar(k+1)` for `0 ≤ k ≤ L−1` (i.e. `Text(k) = tStar(k)` for `k ≥ 1`,
`Text(0)=M(0)`). Also `Wext(k) = M(k)` for `0 ≤ k ≤ L`.

Per-boundary residuals at boundary `s ∈ {1,...,L}` (i.e. block index `j = s−1 ∈ {0,...,L−1}`):
- row-residual `r_s = Text(s) − Text(s+1) = tStar(s−1?)...`  — concretely `r_s = Text(s) − Text(s+1) ≥ 0`.
- col-residual `c_s = Wext(s) − Text(s+1) = M(s) − Text(s+1) ≥ 0`.
(One checks `Σ_{s=1}^{L} r_s · c_s = minAdm`.)

Definitions of the two predicates:
- **row-drop at s**:  `Text(s+1) < Text(s)`  (i.e. `r_s > 0`).
- **col-drop at s**:  `Text(s+1) < Wext(s) = M(s)`  (i.e. `c_s > 0`).
- **both-drop at s**: row-drop AND col-drop at s.
- `NoInteriorBothDrop(M)`:  for every interior boundary `s` with `1 ≤ s ≤ L−1`, there is NO both-drop at s.
- `InteriorDrop(M)`:  `M(L) > 0` AND there exists an interior `p` with `1 ≤ p ≤ L−1` such that there is a
  row-drop at p AND a col-drop at EVERY boundary `b` in the whole tail `p ≤ b ≤ L−1`.

## The proposed argument (contrapositive)

Claim: assuming `M(L) > 0`, `¬InteriorDrop(M) ⟹ NoInteriorBothDrop(M)`.
Equivalently (contrapositive within the `M(L)>0` world): a both-drop at some interior `s₀` forces
InteriorDrop with witness `p = s₀`, i.e. forces a col-drop at every tail boundary `b ∈ [s₀, L−1]`.

Proof strategy: given a both-drop at interior `s₀`, suppose the tail col-drop FAILS somewhere in
`[s₀, L−1]`; take the FIRST such failure `b` (so `s₀ < b ≤ L−1`, `c_b = 0`, and `c_s > 0` for
`s ∈ [s₀, b−1]`). Let `q` be the LAST row-drop in `[s₀, b−1]` (exists, since `s₀` is a row-drop).
Build `T'` from `tStar` by adding `+1` to `Text(s)` for `s ∈ [q+1, b]` (equivalently `tStar(j)+=1`
for `j` in a contiguous block). Claim: `T'` is admissible, and
`Mval(T') = minAdm + (1 − r_q − c_q)`. Since q is a both-drop (row-drop by choice; col-drop because
`q ∈ [s₀, b−1]` where all col-drops hold), `r_q ≥ 1` and `c_q ≥ 1`, so `Mval(T') ≤ minAdm − 1 < minAdm`,
contradicting minimality of `tStar`. Hence no tail col-failure, i.e. whole-tail col-drop, i.e.
InteriorDrop with `p = s₀`.

## Your questions

Q1 (TRUTH). Is the implication `¬InteriorDrop(M) ⟹ NoInteriorBothDrop(M)` (assuming `M(L)>0`) TRUE
for all `L ≥ 1` and all `M`? Try to break it with a small explicit `M` (compute a minimizer `tStar`
by hand for L=2,3,4). If you cannot break it, give the cleanest reason it holds.

Q2 (SOUNDNESS of the exchange). Independently verify the delta `Mval(T') − minAdm = 1 − r_q − c_q`
for the plateau-raise on `[q+1, b]` (be careful with the two endpoints q and b, and the interior
flatness). Also verify `T'` is admissible: check the per-layer bound at the raised entries (does
`c_s > 0` protect it?), the weak-decrease at the bottom endpoint q (does the row-drop at q protect
it?), and the last-zero condition (is `L` ever in the raised block?). Flag ANY off-by-one or any case
(e.g. `q = s₀`, `q = 1`, `b = s₀+1`) where the argument breaks.

Be concrete and adversarial. If the argument is sound, say so plainly and give the tightest version.
