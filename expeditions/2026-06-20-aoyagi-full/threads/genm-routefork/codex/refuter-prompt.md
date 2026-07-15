# Decorrelated adjudication: is an integral inequality TRUE or FALSE?

You are a red-team mathematician. Adjudicate a measure-theoretic inequality. I have NOT told you my
conclusion; do not try to guess it. Produce your OWN verdict (TRUE / FALSE), and if FALSE, an explicit
minimal counterexample with the numbers; if TRUE, the mechanism. Exact algebra; Monte-Carlo only as a
guide. Separate what you PROVE from what you INFER.

## Setup (finite-dimensional real matrices)

Fix integers `M0, M1, M2 ≥ 1` and a "depth" giving a product map. Consider the linear-network product
`W = A0 · Zdeep`, where `A0` is an `M1 × M2` matrix (entries free in `[-1,1]`) and `Zdeep` is an `M2 × n`
matrix arising as a further product of layers with entries in `[-1,1]` (so `Zdeep` ranges over a
full-dimensional family of `M2 × n` matrices as its parameters vary; take `n = M2` and enough layers that
`W` ranges over an open set of `M1 × n` matrices). Let `A'` denote the full parameter tuple (all layers),
ranging over the box `[-1,1]^(all entries)`. Write `W(A')` for the resulting `M1 × n` product.

Pick an injection `κ : Fin u ↪ Fin M1` with `u := t + j`, `1 ≤ t`, that selects `u` "pivot" rows of the
leading layer; the other `M1 − u` rows are "corank" rows. Row-reindexing `W` by `κ` into
`(pivot rows) ⊕ (corank rows)` is a permutation of rows, so it preserves singular values.

Define for a real matrix `Z` and threshold `ε > 0`:
`weakEigCount ε Z = #{ singular values of Z that are < ε }`.
For `r := min(M0 − t, M1 − t)` and `0 ≤ j ≤ r`, the "shell-j" set is
`shell_j = { A' : min(weakEigCount ε (W(A')), r) = j }`.
For `1 ≤ j < r` this means EXACTLY `j` singular values of `W(A')` are `< ε` (the rest `≥ ε`).

## The two integrands

There is a known reduction (agreed, not contested): for a fixed `M1 × n` matrix `Q`, the inner integral
over auxiliary variables `(x, Γ)` of `freedSchurLoss(x, Γ, Q)^(−c')` equals, up to a measure-preserving
reassembly, `G(Q) := ∫_{T ∈ box} frobSq(T · Q)^(−c') dT`, where `T` ranges over an `M0 × M1` matrix box
(intersected with the full-measure open set where its top-left `u×u` block is invertible), `frobSq(·)` is
the squared Frobenius norm, and `c' > 0`. Standard homogeneity: `G(Q) < ∞` iff `c' < M0·rank(Q)/2`, and
as `Q` approaches a matrix of corank `k ≥ 1`, `G(Q)` diverges once `c' ≥ M0·(M1−k)/2`.

Now consider two things.

**LHS (shell-j spine):**
`LHS = ∫_{A' ∈ box ∩ shell_j} G( W(A') reindexed by κ ) dA'.`

**RHS (pivot-shell box):** introduce reduced parameters `z` (the pivot rows glued onto the deep layers) and
a FREE variable `A_cor` ranging over the box `matBox = [-1,1]^{(M1−u) × M2}`, decoupled from `z`. Set
`hsQ(z, A_cor) = fromRows( pivotProduct(z) ; A_cor · Zdeep(z) )` — an `M1 × n` matrix. Define the
"pivot shell" `pivotShell(z) = { A_cor : hsQ(z,A_cor)·hsQ(z,A_cor)ᵀ ⪰ ε²·I_{M1} }`, i.e.
`{ A_cor : smallest singular value of hsQ(z,A_cor) ≥ ε }`. Then
`RHS = ∫_z ∫_{A_cor ∈ matBox ∩ pivotShell(z)} G( hsQ(z, A_cor) ) dA_cor dz.`

Note: at the "genuine" `A_cor` (= the corank rows of `A0`), `hsQ(z, A_cor)` equals `W` reindexed, so has
the same singular values as `W`. But in RHS, `A_cor` is a FREE box variable, and the domain is intersected
with `pivotShell`.

## The claim to adjudicate

For parameters satisfying `1 ≤ t`, `1 ≤ j`, and STRICTLY `j < r = min(M0−t, M1−t)`, and `0 < ε`, `c' > 0`,
is it TRUE that
`LHS ≤ RHS`
(both sides in `[0, +∞]`), for all admissible data (all `Zdeep`-families of the stated shape)?

Specifically:
1. Are the LHS integration region (image of shell_j under the pivot/corank change of variables) and the
   RHS integration region (`pivotShell`) the same set, disjoint, or nested? Give the spectral condition on
   `hsQ` characterising each.
2. Is there a choice of `(M0, M1, M2, t, j, ε, c')` with `1 ≤ j < r` for which `LHS = +∞` while
   `RHS < +∞`? If so, exhibit it with the exponent arithmetic (the corank at which `G` diverges, the
   divergence rate in the smallest singular value, and why the `A'`-integral over shell-j then diverges
   while the pivot-shell RHS stays finite). If not, prove `LHS ≤ RHS`.
3. Does requiring `j < r` STRICTLY (as opposed to `j = r`, the saturated shell) change the answer? I.e., is
   the inequality rescued by excluding the saturated shell `j = r`?

Give a crisp final verdict: TRUE or FALSE for `1 ≤ j < r`, with the minimal witness or the proof.
