<task>
Setting: a DLN (deep-linear-network) resolution-of-singularities atlas for the multiplication map
of composable matrices of shape d=(3,3,4). Coordinates u0..u20 (21 of them). Two matrices:
  A0 = 3x3 = [[u20,u2,u3],[u0,u4,u6],[u1,u5,u7]]
  A1 = 4x3, column-major entries u8..u19 (col0=u8,u9,u10,u11; col1=u12..u15; col2=u16..u19).
The loss is L(u) = sum of squares of the 12 entries of the product P = A1 @ A0 (a 4x3 matrix).
We want a lower bound on the real log-canonical threshold (RLCT) of L via a resolution atlas of
monomial "blow-up" charts composed with unipotent shears.

Chart building blocks (each is a substitution map on the 21 coords):
  - bb(S,p): monomial blow-up with pivot p and direction set S:
        u_j -> u_p * u_j for j in S,  u_p -> u_p,  u_j -> u_j otherwise.  (|det Jac| = u_p^|S|)
  - permP: a fixed permutation of the 21 indices (unimodular).
  - shearH: a fixed unipotent shear (|det Jac|=1) that clears cross-terms:
        u4 += u0*u2; u5 += u1*u2; u6 += u0*u3; u7 += u1*u3;
        u8 -= u0*u12 + u1*u16; u9 -= u0*u13 + u1*u17; u10 -= u0*u14+u1*u18; u11 -= u0*u15+u1*u19.
  - The "born shear" = shearH o permP.

The atlas leaves are indexed (p1,p2,p3) with p1 in C0={0,1,2,3,4,5,6,7,20} (node-1 pivot, 9 choices),
p2 in C1={0,1,2,3,4,5,6,7} (node-2, 8), p3 in C2={1,5,6,7} (node-3, 4): 288 leaves.

The FIXED-shear chart is  g_leaf(p1,p2,p3) = bb(C0,p1) o (shearH o permP) o bb(C1,p2) o bb(C2,p3).
KNOWN FACT (exact toric-LP, already computed): the fixed-shear chart FAILS on the node-1 Delta-block
dominants p1 in {4,5,6,7}: true per-chart rlct = 2.5, 1.0, 1.0, 1.0 (< 4). It over-vanishes there.

FIX under study ("born-native fan"): replace the fixed shear by a PER-p1 native shear
  nativeSel(p1) = sigma_p1^{-1} o (shearH o permP) o sigma_p1
where sigma_p1 is a LOSS SYMMETRY (a coordinate permutation: simultaneous row-perm + col-perm of A0
with the matched A1-column perm) that maps the canonical dominant slot 20 to p1's A0 slot. So
  g_native(p1,p2,p3) = bb(C0,p1) o nativeSel(p1) o bb(C1,p2) o bb(C2,p3).
(The inner blow-ups bb(C1,p2), bb(C2,p3) keep their standard direction sets / pivots; only the shear
is conjugated per p1.)

The exact per-chart toric RLCT for a chart with |det Jac| = prod u_i^{kappa_i} and loss = sum of
squares of generators (the 12 entries of P=A1@A0) is
   rlct_chart = ( min_{w>=0}  w.kappa + sum_i w_i   s.t.  w.m >= 1  for every monomial m of every generator ) / 2.

The DE-RISK question: does EVERY one of the 288 born-native leaves have true rlct_chart >= 4?
Equivalently (divisorMin >= 8): whenever the loss-GCD "survivor" (the generator whose GCD-quotient
is nonzero at the origin) exists, does its support land only on coords with Jacobian exponent >= 7?
The worry: the per-leaf Jacobian exponent vectors VARY a lot (14 distinct multisets; some coords have
jac as low as 3, e.g. canonical leaf (20,0,1) has jac {u0:7, u1:3, u20:8} -- u1 has jac 3). If some
leaf's survivor support hits a jac-3 coord, divisorMin=4 and rlct=2 < 4 = a failure (RED).
Some born-native leaves OVER-VANISH (empty survivor) -- and over-vanishing was exactly what dropped
the fixed-shear Delta-block dominants to rlct 1.0. So over-vanishing per se is NOT automatically safe.
</task>

<output_contract>
Four sections, terse:
1. INVARIANCE: Does conjugating a chart F by a loss symmetry sigma (i.e. sigma^{-1} o F o sigma)
   preserve the true rlct of loss o (that chart)? State the argument precisely (what "loss symmetry"
   must satisfy, why the permutation coordinate change on the domain preserves rlct), and name any
   gap. Note: in g_native only the SHEAR is conjugated, the outer/inner blow-ups are NOT globally
   conjugated together with it -- so does the clean invariance argument actually apply to g_native as
   defined, or only to a fully-conjugated chart sigma^{-1} o g_leaf(20,p2,p3) o sigma? Distinguish.
2. OVER-VANISHING: When a chart over-vanishes (empty survivor), what determines whether its true
   rlct is >=4 or <4? Give the mechanism that made the fixed-shear Delta-block dominants drop to 1.0,
   and the discriminant that separates "over-vanishes but still >=4" from "over-vanishes and <4".
3. WHERE-IT-WOULD-BREAK: If a born-native leaf DID have rlct<4, what would the survivor support /
   jac vector look like? Name the single most likely (p1,p2,p3) family to break and the cheapest
   exact test to isolate it.
4. VERDICT PRIOR: Purely from the structure above (NOT from any computed sweep), is the all-288
   rlct>=4 more likely to hold or fail, and what is the one fact that would settle it.
</output_contract>

<grounding_rules>
- Reason from the given algebra only; do not invent matrix entries or shear terms.
- Keep "provable fact" vs "plausible inference" explicitly separated.
- Do not write or run code; give the reasoning and the cheapest discriminating test.
- If the invariance argument in (1) is clean, say so plainly and say exactly which construction it
  covers (fully-conjugated vs shear-only-conjugated).
</grounding_rules>
