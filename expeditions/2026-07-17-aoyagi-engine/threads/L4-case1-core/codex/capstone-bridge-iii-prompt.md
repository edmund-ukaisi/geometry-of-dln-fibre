<task>
Design-review a proof-transport question arising in a blow-up resolution of a deep linear network's
product map. Decide whether a needed algebraic identity can be re-derived across a "clear" operation,
or whether it necessarily requires a measure/gauge (RLCT-level) argument rather than a
polynomial/ideal one. Exact algebra where possible; flag FACT vs INFERENCE. Do NOT rubber-stamp;
construct/verify.
</task>

<context>
Coordinates u_{L,r,c} = entries of matrices A_L (L=0..N-1). "coreGen" = entries of the product
P = A_{N-1}···A_0. A resolution walks a tree; at a node p, foldResid(p)(u) = coreGen(Phi_p(u)) where
Phi_p composes per-edge coordinate transforms (unipotent shears + block blow-ups + strict-transform
quotients). At a "case11 merge" child edge with pivot e2 and center set ed.center, the proof needs:

  APPEND CRUX: from `Deg1SupportedOn (foldResid p) ed.center` — i.e. each residual slot
    foldResid(p)_j = sum_{i in ed.center} c_i(u)*u_i  with c_i CONTINUOUS —
  it derives the child's step identity foldResid(child) = u_{e2}*foldResid(p)(quotient-map), by
  moving the pivot factor through the blow-up (each center coord pulls back as u_{e2}*quot) and using
  that the c_i ignore the center coords. Continuity of the quotient q needs foldResid(p) in the
  continuous span of ed.center.

FACTS ESTABLISHED (exact Groebner, witness d=(2,2,2,2), case11 at layer 1 reusing a layer-0 divisor,
e2=(0,1,1), ed.center={(0,1,1),(1,0,0),(1,1,0)}):
  * `Deg1SupportedOn (foldResid p) ed.center` is FALSE on the RAW foldResid: slot 0 on the center's
    zero-variety {u_011=u_100=u_110=0} equals 2*u_010*u_101*u_200 + 2*u_010*u_111*u_201 != 0, so it is
    not in the continuous span of ed.center.
  * Intended fix = SOURCE-CLEARED object: sourceCleared := raw|_{u_010=0} (zero the cleared input
    column's below-pivot entry u_010 at the source). On it, Deg1SupportedOn ed.center HOLDS.
  * BUT (exact Groebner): <sourceCleared slots> != <raw slots> (both inclusions fail); <coreGen> (the
    product P) is NOT preserved by setting u_010=0; and the remainder r = raw - sourceCleared =
    2*u_010*(...) is NOT divisible by u_e2=u_011, not in <ed.center>, not in <sourceCleared>.
  * sourceCleared = raw|_{u_010=0} genuinely drops the raw fold's dependence on u_010 (raw depends on it).
</context>

<questions>
1. Is there ANY route to re-derive the APPEND CRUX for the case11 child given only that the
   SOURCE-CLEARED object is Deg1SupportedOn ed.center (not the raw one)? Consider (a) ideal-equality
   <cleared>=<raw> (shown false); (b) decomposition raw = cleared + remainder with the remainder
   discharged by u_e2-divisibility (remainder shown not u_e2-divisible); (c) any other polynomial/ideal
   route you can construct. If (c), exhibit it; if none, argue why.
2. Since sourceCleared = raw|_{u_010=0} is a hyperplane RESTRICTION (not an invertible change of
   variables), can any det-1 coordinate change of the full space map raw |-> cleared?
   (Dimension/flat-direction reasoning.) State as fact with justification if not.
3. u_010 is the below-pivot entry of a cleared INPUT column (here a layer-0 = network-input coordinate).
   Under what condition is fixing u_010=0 RLCT-PRESERVING for the loss sum coreGen^2 (so re-stating the
   boost-readiness on the restricted object does not change the learning coefficient)? Is "u_010 is a
   coordinate of an input GL_{d0} gauge orbit" sufficient — noting sum ||P||^2 is NOT invariant under
   A_0 |-> A_0*G for general G in GL_{d0}? Distinguish the fibre (P=const) picture from full-space.
4. Bottom line (one sentence): must the cleared<->raw bridge be a MEASURE/GAUGE argument (RLCT
   invariance under fixing the coordinate), or is there a purely algebraic (ideal/CoV) bridge?
</questions>

<output_contract>
- Verdict on Q1 with construction or impossibility argument. Q2 fact + justification. Q3 the precise
  RLCT-preservation condition. Q4 one-sentence bottom line. FACT vs INFERENCE flagged throughout.
</output_contract>

<grounding_rules>
Exact algebra where checkable; justify any ideal/divisibility/RLCT claim. RLCT of sum f_i^2 at 0 = the
real log-canonical threshold (Watanabe). Distinguish "restricting to a hyperplane preserves the RLCT"
(needs a reason) from "it changes it" (generic case).
</grounding_rules>
