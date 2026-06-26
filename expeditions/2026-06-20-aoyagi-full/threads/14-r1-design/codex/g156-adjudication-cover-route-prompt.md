<task>
Adjudicate, by independent derivation, whether a recursive RLCT computation for a chained matrix
product loss can avoid a known-false "full-product comparability", by recursing one layer at a time.

SETTING. Deep linear network. M = (M^0, M^1, ..., M^{L+1}) widths. Loss at the all-zero deepest point
is F = ||A_0 A_1 ... A_L||_F^2 where A_s is M^s x M^{s+1} (square-Frobenius product loss; the "B = 0"
target so the loss is the squared norm of the product). We want the real log canonical threshold
rlct(F) at the deepest critical point.

KNOWN-FALSE OBJECT (verified counterexample). One route ("L2 squeeze") tried to write
rlct via a normal form Phi = sum E^2 + ||Pi_s S_s||^2, where:
  - E = the FULL-PRODUCT residual blocks (P00-I, P01, P10) of the full product P = C_L...C_1
    (each layer block-partitioned into rank-r pivot + reduced blocks, C_s = [[I+X_s, Y_s],[Z_s, T_s]]),
  - S_s = T_s - Z_s (I+X_s)^{-1} Y_s  the PER-LAYER Schur complement,
  - Pi_s S_s = the product of per-layer Schur complements,
  - R = P11 - P10 P00^{-1} P01 the full-product Schur core.
The needed comparability ||R||^2 asymptotic-equiv ||Pi_s S_s||^2 is FALSE: exact counterexample
(L=2, r=1, reduced-dim=2, eps=1/7) has E=0 exactly, Pi S_s = 0, but R = -eps^4 E_11 != 0. The leakage
R - Pi S_s = -S_2 K_1 H^{-1} Y_2 S_1 (K_1 = Z_1 A_1^{-1}, H = A_2 + Y_2 K_1) is inter-layer cross-talk,
NOT in the ideal of the final E.

THE ALTERNATIVE ROUTE TO ADJUDICATE ("cover / one-layer-at-a-time"). Blow up ONLY the deepest layer
A_0 = y0 * Ahat, Ahat top-left pivot = 1. Then F = y0^2 * core, core = ||Ahat B||^2, where
B = A_1...A_L is treated as a GENERIC matrix (k x n, k = M^1, n = M^{L+1}). Schur-eliminate the unit
pivot of Ahat = [[1, a],[b, D]]:
  core = sum_j Erow_j^2 + sum_{i,j}(b_i Erow_j + (S Bred)_{ij})^2,  S = D - b a (SINGLE-step Schur
  complement of ONE layer), Bred = B[1:,:], Erow = B[0,:] + a Bred.
Claim: rlct(F) = min{ mk/2 , rlct(core) }, rlct(core) = n/2 + rlct(||S Bred||^2), and ||S Bred||^2 is
itself a GENERIC (m-1)x(k-1)xn product loss = the child loss dlnLoss(M^0-1, M^1-1, M^2, ..., M^{L+1}),
on which the SAME procedure recurses (blow up its deepest layer, etc.).

GROUNDING FACTS (take as given, verified by exact sympy):
  (a) the counterexample above is exact; R != Pi S_s.
  (b) the row-decomp core = ||Erow||^2 + ||b Erow + S Bred||^2 with S = D - b a is an exact identity.
  (c) min{mk/2, n/2 + rlct(child)} = (1/2) minAdm(M) holds combinatorially.

QUESTIONS (derive independently):
  1. Does the one-layer-at-a-time cover route ever FORM the object Pi_s S_s or R? Or does recursing
     on the GENERIC child loss ||S Bred||^2 sidestep it entirely? Be precise about what "generic B"
     buys: when we recurse, is the child's B again generic, or does it inherit a product structure
     that would reintroduce inter-layer cross-talk?
  2. The inner step needs core asymptotic-equiv sum Erow^2 + ||S Bred||^2 near the deepest point
     (b -> 0). Is THIS comparability (single-step, b bounded) sound, and is it DIFFERENT from the
     false full-product one? Can the eps=1/7 counterexample be re-cast to attack it?
  3. The outer product-min rlct(F) = min{mk/2, rlct(core)} via Fubini on disjoint groups {y0} vs
     {core vars}: does its "min <= joint" (>=) direction (the divergence/below-threshold leg) need
     ANY comparability between core and a product-of-Schur object, or only the down-set property of
     rlct(core) itself (below rlct(core) => child integrand integrable on a nbhd)?
  4. BOTTOM LINE: is rlct(F) = (1/2) minAdm(M) provable for arbitrary M by the recursive cover route
     WITHOUT the false ||R||^2 ~ ||Pi S_s||^2 comparability? If yes, what (if any) residual hypothesis
     remains. If no, where exactly does cross-talk re-enter the cover recursion.
</task>

<output_contract>
For each of Q1-Q4: a direct answer, your derivation, and an explicit FACT vs INFERENCE tag on each
load-bearing step. End with a one-line BOTTOM LINE: cover-route-comparability-free YES/NO + residual.
</output_contract>

<grounding_rules>
Derive independently; do not assume the alternative route is correct just because it is proposed.
If you find the cover route ALSO needs the false comparability, say so and locate it exactly.
Distinguish: (full-product Schur R / product Pi S_s) vs (single-step Schur S = D - b a of one layer).
</grounding_rules>
