<task>
Adjudicate the scope of computing the real log canonical threshold (RLCT) of a deep-linear-network
zero-product loss for general depth L>=3, and whether a per-layer recursion can work.

SETTING. Widths M=(M_0,...,M_{L+1}). Loss F = ||A_0 A_1 ... A_L||_F^2 (square-Frobenius, target 0).
rlct(F, all-zero). Known (Lehalleur-Rimanyi / Aoyagi): rlct(F,0) = (1/2) minAdm(M), where
minAdm(M) = min over admissible rank profiles T=(t^1>=...>=t^L=0) of
  Mval(M,T) = (M_1 - t^1)(M_2 - t^1) + sum_{j=2}^L (t^{j-1} - t^j)(M_{j+1} - t^j).

A PROPOSED per-layer recursion (blow up the deepest layer A_0 = y_0 Ahat, recurse on the
reduced chain redM = (M_0 -1, M_1 -1, M_2, ..., M_{L+1})): claims
  rlct(node) = min{ (M_0 M_1)/2 , (M_{L+1})/2 + rlct(child) }
with the "n = M_{L+1}" term being a Morse block of n squares (the pivot-row product Erow_j).

A FOUND DEFECT (verify): for L=2 (B = A_1 a single free matrix) this is CORRECT (Erow_j = B[0,j] +
sum u_i B[i,j] is a det-1 shear of free coords -> genuine n-Morse). For L>=3, B = A_1 A_2 ... A_L is a
PRODUCT of >=2 free matrices, so Erow_j is a degree-(L-1) form (not a free coordinate), so the
"n-Morse" count overcounts. Witness: M=(3,3,3,3): the per-layer recursion gives 7 (in 2*rlct units)
but minAdm = 6. The reduction redM preserves depth L, so the recursion never reaches the L=2
free-B base.

QUESTIONS:
 1. Confirm or refute: the per-layer (one-layer-at-a-time, depth-preserving) recursion with the
    n=M_{L+1} Morse count is L=2-only; for L>=3 the Erow block is not a free Morse block and the
    recursion overcounts. Is the (3,3,3,3) 7-vs-6 a genuine witness?
 2. The CORRECT general-L resolution: is it the iterated blow-up of the rank-profile (determinantal)
    strata {rank(partial product) <= t}, giving rlct = min_T Mval(M,T)/2 as the min over exceptional
    divisor ratios? Sketch why the per-profile divisor carries Mval(M,T) as its (ord Jac, ord loss) data.
 3. SCOPE: can the general-L resolution value rlct = (1/2) minAdm be proven MODULO a normal-crossing
    RLCT toolkit ("S2": rlct of a monomial product = min axis ratio (e_i+1)/(2 k_i), + additivity for
    sums in disjoint blocks, + min for products) -- i.e. by EXHIBITING an explicit iterated
    determinantal resolution whose exceptional divisors have monomial data Mval(M,T) -- WITHOUT
    importing the analytic "rlct <= (1/2) codim" bound (Aoyagi/Watanabe)? Or is constructing that
    explicit uniform resolution for arbitrary (L, widths) tantamount to re-proving Aoyagi, so that the
    cite is the only tractable route? Give your best assessment of which is the realistic path and why.
</task>

<output_contract>
Q1-Q3: direct answer + derivation, FACT vs INFERENCE tags. End with a one-line BOTTOM LINE: per-layer
recursion L=2-only YES/NO; general-L path = [iterated determinantal resolution modulo-S2 / Aoyagi cite];
+ the single decisive reason for the scope call.
</output_contract>

<grounding_rules>
The zero-locus is {product=0}; the deepest point is the cone vertex (homogeneous loss). Distinguish a
per-LAYER recursion (depth-preserving, the failed shortcut) from a per-PROFILE resolution (the full
rank-profile lattice). For Q3 distinguish "an explicit resolution exists in principle => S2 suffices"
from "constructing it uniformly for all (L,widths) is the hard Aoyagi theorem". Be concrete about which
is realistically reachable in a Lean formalization with only an S2 normal-crossing toolkit.
</grounding_rules>
