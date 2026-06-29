<task>
Independent algebraic adjudication (pure linear/multilinear algebra; no Lean). I have a square
Jacobian J = DPhi arising from a deep-linear-network RLCT calculation and I need to know whether
its determinant factors as a PRODUCT OF "TRIANGULAR PIECES" with a UNIFORM per-piece formula
across all width-tuples M, or whether some coupling resists a uniform triangular factor. Please
analyze from scratch and give your own structural conclusion. Do NOT assume the factorization holds.
</task>

<setup>
Fix L >= 1 and ambient widths W_0..W_L (the tuple M). Fix compressed widths T_0=W_0 and a
weakly-decreasing descent 0 < T_{k+1} <= W_k. Write c_k = W_k - T_{k+1}, r_k = T_k - T_{k+1}.

Per boundary k=0..L-1 the chart input data (free real coordinates unless noted):
  B_k : T_k x T_{k+1}   the "kept block", parametrized so its leading T_{k+1} x T_{k+1} square
        K-core is an LDU product L*diag(q)*U (q = pivots), and the extra r_k rows are
        (free row)*diag(q)*U (i.e. the extra rows CARRY the pivots).
  N_k : T_{k+1} x c_k
  W_k : c_k x W_{k+1}
  R_k : a FIXED 0/1 structural matrix EXCEPT a few "free-eta" entries (each multiplied by u).
  leaf Rfin : T_L x W_L (free, with ONE entry fixed = 1 as the radial pivot).
  u : one scalar "radial" coordinate.

Definitions (chainQ stacks I then N in columns; chainA stacks rows):
  chainQ(N_k) = [ I_{T_{k+1}} | N_k ]                 (T_{k+1} x W_k)
  C_L = u * Rfin
  C_k = B_k * chainQ(N_k) + u * R_k                   (T_k x W_k), k<L
  A_k = [ C_{k+1} - N_k * W_k ; W_k ]                 (W_k x W_{k+1})   (top T_{k+1} rows then c_k rows)
The chart output is (A_0,...,A_{L-1}) flattened; #free coords is arranged to equal sum_k W_k W_{k+1}
so J is square.

KEY OBSERVED DEPENDENCY: A_k depends on boundary k's own N_k, W_k AND on C_{k+1}, which depends on
boundary (k+1)'s B_{k+1}, N_{k+1}, R_{k+1}. So output layer k reads boundaries k and k+1
("nearest-neighbor coupling"); the K-core B_{k+1} appears in output A_k, NOT A_{k+1}.
</setup>

<the_proposed_pieces>
A claim under test is that |det J| = (radial piece) * prod_s (per-boundary piece), where:
  - radial piece = |u|^q for a single exponent q (the number of free angular u-scaled directions),
  - per-boundary-s piece = |det K_s|^{r_s + c_s} * (an LDU-pivot monomial prod_i q_{s,i}^{2(t_s-1-i)}),
  - and the nearest-neighbor chain coupling A_k = [[I,-N_k],[0,I]] [C_{k+1};W_k] sits in a separate
    UNIPOTENT shear factor of determinant 1.
</the_proposed_pieces>

<questions>
1. Structurally, does the nearest-neighbor coupling (B_{k+1} appearing in A_k via C_{k+1}) PREVENT a
   uniform per-boundary triangular factorization, or can it be absorbed into a determinant-1 unipotent
   shear so that each boundary's K-core/LDU determinant content is isolated? Give the mechanism.
2. The chain block op [[I,-N_k],[0,I]] is unipotent (det 1). But it MIXES boundary k's N_k with
   boundary (k+1)'s C_{k+1}. Does that mixing leak any K-pivot or u into the det-carrying pieces, or
   is it determinant-neutral for ALL M (any L, any descent, t_s >= 2 interior cores included)?
3. Is the per-boundary determinant content genuinely |det K_s|^{r_s+c_s} times the LDU monomial,
   UNIFORMLY in (t_s, r_s, c_s)? In particular: when c_s = 0 (no lift block) or r_s = 0 (no extra
   rows), does the formula degrade gracefully (e.g. the Schur frame factor |det K|^{r+c} becomes
   |det K|^0 = 1), or does some boundary configuration break the uniform exponent r_s + c_s?
4. Where, if anywhere, would this factorization be M-dependent (no single uniform formula)? Name the
   configuration that would break it, if one exists.
</questions>

<grounding_rules>
- Treat the matrix definitions as exact. The Jacobian is w.r.t. all free coords simultaneously.
- "Triangular piece" = a self-map of the flat coordinate space that is block-triangular under some
  ordering, embedding as identity-elsewhere plus one boundary's (or the radial) block.
- Give explicit small matrices / a clean inductive argument where useful. State assumptions on
  which entries are free vs fixed.
- If the factorization holds, give the mechanism (the layer filtration / shear) and the exact source
  of each per-piece determinant. If it can fail, exhibit the minimal breaking configuration.
</grounding_rules>
