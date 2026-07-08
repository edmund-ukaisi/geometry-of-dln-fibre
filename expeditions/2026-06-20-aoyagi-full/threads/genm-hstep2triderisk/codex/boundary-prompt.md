<task>
Adjudicate a first-derivative-vanishing question about a boundary-frame "decode" map, at a
base point I call wstar. This is an exact-algebra question over a commutative ring / R; I want
your INDEPENDENT verdict and reasoning, not confirmation. Withhold nothing about doubts.

SETTING. A "chain" is a finite list of block matrices C_s, s = 0..L-1, each in r+m block form
    C_s = [[A_s, Y_s], [Z_s, T_s]]   (A_s: r x r,  Y_s: r x m,  Z_s: m x r,  T_s: m x m).
The block matrices depend smoothly on a parameter q (a vector). At q = 0 (= wstar) every layer
is C_s(0) = corM := [[I_r, 0],[0, 0]] (i.e. A_s(0)=I_r, all other blocks 0).

The chain is built by FRAMING raw per-layer reads:
    C_s(q) = corM + P_s * rawDev_s(q) * Q_s
where rawDev_s(q) = [[X_s(q), Y_s(q)],[Z_s(q), T_s(q)]] is LINEAR in q with rawDev_s(0)=0 (these
X,Y,Z,T are the "identity reads" of q at layer s), and P_s, Q_s are FIXED matrices that DO NOT
depend on q (they are structural frames, evaluated once at wstar). The frames are trivial
(= I) except:
    layer 0    : P_0 = [[P11, 0],[P21, I_m]]  (block-LOWER),   Q_0 = I
    last layer : P_{L-1} = I,                 Q_{L-1} = [[Q11, Q12],[0, I_m]]  (block-UPPER)
with P11, Q11 constant INVERTIBLE r x r matrices (units at wstar), P21 (m x r), Q12 (r x m) constant.

A separate, already-verified construction produces a "moved chain" movedC_s(q) from C(q) (it
fixes each pivot A_s, edits the up-blocks Y_s, edits one down-block Z_0 via an accumulator, and
reconstructs the cores). The ONLY facts about movedC you may use (previously certified, exact,
for L<=5): for EVERY layer s,
    movedC_s(q) - C_s(q) = O(||q||^2)   (its first derivative in q at q=0 is zero);
    in fact the interior/last-layer edit is O(||q||^3) and the layer-0 edit is O(||q||^5).

THE DECODE. Define per-layer "reads" psiRead_s(q):
    interior s : psiRead_s = movedC_s(q) - corM
    layer 0    : psiRead_0 = forcedDecodeLeft (P_0)  (movedC_0(q) - corM)
    last layer : psiRead_{L-1} = forcedDecodeRight(Q_{L-1})(movedC_{L-1}(q) - corM)
where (with A,Y,Z,T the four blocks of the argument D, and Pinv := P11^{-1}, Qinv := Q11^{-1}):
    forcedDecodeLeft(F, D)  = [[ Pinv*A , Pinv*Y ],
                              [ Z - P21*Pinv*A , T - P21*Pinv*Y ]]
    forcedDecodeRight(Q, D) = [[ A*Qinv , Y - A*Qinv*Q12 ],
                              [ Z*Qinv , T - Z*Qinv*Q12 ]]
(These are the "forced" reads that satisfy F * forcedDecodeLeft(F,D) = D and
 forcedDecodeRight(Q,D) * Q = D when P11*Pinv = 1 resp. Qinv*Q11 = 1.)

THE QUESTION. Define f_s(q) := psiRead_s(q) - rawDev_s(q)  (moved read minus identity read).
At the two BOUNDARY layers s in {0, L-1}, where the decode goes through the frame factors and
the constant inverses Pinv/Qinv:
   (Q1) Is f_s(0) = 0 (value vanishes at wstar)?
   (Q2) Is the first derivative D f_s(0) = 0 ?  (i.e. f_s(q) = o(||q||); equivalently
        HasStrictFDerivAt of (psiRead - identity) is 0 at the boundary.)
   (Q3) If yes, what is the actual leading order in ||q|| at layer 0 and at the last layer, and
        WHY (the mechanism)? If no, exhibit the surviving first-order term.
Focus on whether the FRAME (the constant Pinv/Qinv, P21, Q12) can inject a first-order term that
the interior layers do not have. The interior case is settled (f_interior = movedC - C = O(||q||^2)).
</task>

<output_contract>
1. A one-line verdict for (Q1) and (Q2) at each boundary layer: value-zero? first-derivative-zero?
2. The mechanism (Q3): the key algebraic identity you use, in <=6 lines. State explicitly whether
   forcedDecodeLeft/Right is LINEAR in its argument D and whether its coefficients depend on q.
3. The single most likely way the claim could FAIL, and the one cheapest exact check to catch it.
4. Mark each statement [FACT] (algebra you derived here) or [INFERENCE] (belief not fully derived).
</output_contract>

<grounding_rules>
- Do not assume a numeric example; reason symbolically over a commutative ring (P11, Q11 units).
- You MAY use the given movedC - C = O(||q||^2) fact; do not re-derive it.
- If the answer depends on P_last or Q_0 being trivial (= I), say so explicitly and say what
  breaks if they were not trivial.
- Flag any step where invertibility of P11/Q11 in a neighbourhood of wstar is load-bearing.
</grounding_rules>
