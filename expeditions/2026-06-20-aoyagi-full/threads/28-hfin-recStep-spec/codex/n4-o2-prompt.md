<task>
Adjudicate one analytic inequality that gates a recursion for an RLCT (real-log-canonical-
threshold) finiteness proof. Decide its truth value and give the cleanest correct argument OR a
counterexample. Exact reasoning; Monte-Carlo only as a guide.
</task>

<setup>
Fix integers r >= 3, p >= 2, and a small radius T>0. "frobSq(X)" = sum of squares of all entries of
a real matrix X. A "box" of dimension d and radius b is [-b,b]^d with Lebesgue measure.

We work on the "M11-dominant chart" of an r x r real angular matrix R:
  - R[0,0] = 1 (pivot normalized), |R[i,k]| <= 1 for all i,k.
  - Take j = 1 (the simplest block split): M11 = R[0,0] = 1 (1x1, scalar);
    M12 = R[0, 1:] (1 x (r-1), the "spectator row"); M21 = R[1:, 0] ((r-1) x 1, "spectator col");
    M22 = R[1:, 1:] ((r-1) x (r-1)).
  The Schur complement is Sc = M22 - M21 * M11^{-1} * M12 = M22 - M21 * M12  (M11=1),
  an (r-1)x(r-1) matrix. Entrywise Sc[a,b] = M22[a,b] - M21[a]*M12[b].

The free coordinates of R on this chart (after fixing R[0,0]=1) are: M12 (r-1 entries),
M21 (r-1 entries), M22 ((r-1)^2 entries). All lie in [-1,1].

S is an r x p free matrix; write S_top = top j=1 rows (1 x p), S_bot = bottom (r-1) rows ((r-1)x p).
S ranges over a box of radius T.

Two facts already established (you may take them as GIVEN, they are separately proved):
 (F1) On this chart there is a UNIFORM two-sided comparison (constants depend only on r, NOT on R,S):
        c0 * D(R,S) <= frobSq(R*S) <= c1 * D(R,S),   c0,c1 > 0,
      where D(R,S) = frobSq((R*S)_top) + frobSq(Sc*S_bot).
 (F2) (R*S)_top depends only on (M11,M12) and S, NOT on M22; and after a measure-preserving
      shear (translation) in S_top, frobSq((R*S)_top) becomes a free nondegenerate quadratic
      (Morse) form in the j*p = p variables S_top.

The recursion's INDUCTION HYPOTHESIS (corank r-1, "IH"): for an (r-1)x(r-1) coefficient matrix C
ranging over a FREE box and S_bot over a box, the JOINT integral
   ∫_{C in box} ∫_{S_bot in box} (Morse_top(S_top) + frobSq(C*S_bot))^{-c'} dS_bot dC < infinity
for c' < (jp/2 + lambda_{r-1,p}), where lambda is the recursion threshold
   lambda_{r,p} = min(r^2/2, min_{1<=j<=r}( j*p/2 + lambda_{r-j,p} )),  lambda_{0,p}=0.
(Equivalently: the free-box corank-(r-1) core is finite at its own threshold.)
</setup>

<question>
The recursion needs the per-chart inner integral, integrated over the chart's R-coordinates, to be
finite at the right threshold:

  TARGET:  ∫_{R on chart} [ ∫_{S} D(R,S)^{-c'} dS ] dR  <  infinity   for c' < (p/2 + lambda_{r-1,p}),

AND the bound must be expressible with CONSTANTS INDEPENDENT of the "spectator" coordinates M12, M21
(i.e. it must reduce to a FREE corank-(r-1) core integral, the IH, up to a spectator-independent
constant factor). The worry being adjudicated (call it O2): "Sc = M22 - M21*M12 is a nonlinear
function of R; is there a clean change of variables / pushforward so that the R-integral of the
inner Sc-core integral reduces to the free-box IH with a spectator-independent constant -- or does
the law of Sc(R) concentrate / the constant blow up with the spectators, breaking the recursion?"

Specifically:
 (Q1) As R ranges over the chart, what is the Jacobian of the map (M12,M21,M22) -> (M12,M21,Sc)?
      Is the map M22 -> Sc, at fixed spectators (M12,M21), volume-preserving? What is the image of
      the M22-box [-1,1]^{(r-1)^2} under M22 -> Sc, and is it contained in a FIXED box independent
      of the spectators?
 (Q2) Given (Q1), does
        ∫_{M22 in [-1,1]^{(r-1)^2}} g(Sc(M22,spectators)) dM22  <=  ∫_{Sc in [-2,2]^{(r-1)^2}} g(Sc) dSc
      hold for any g >= 0, with the RHS a spectator-independent constant? (g(Sc) = the inner-S
      integral at fixed Sc.) Does this give the TARGET with K = vol(spectator box) and the bound =
      the free corank-(r-1) JOINT core over the box [-2,2]? Verify the threshold matches.
 (Q3) Does this argument correctly carry the ADDITIVE threshold p/2 + lambda_{r-1,p} (the disjoint
      sum of the top Morse block AND the Sc-core), or does it only deliver the Sc-core threshold
      lambda_{r-1,p} (which would UNDERSHOOT)? I.e. is the disjoint-sum additivity preserved by the
      M22->Sc translation? Where does the j*p/2 Morse contribution enter?
 (Q4) Are there hidden failure modes: does the {det Sc = 0} or {Sc = 0} locus (which exists in the
      Sc-box) cause the free-box core integral to DIVERGE below threshold? Does the j>=2 case (where
      M11 is a genuine block, shears bounded by Cramer's rule rather than exactly <=1) change Q1-Q3?
 (Q5) VERDICT: does O2 hold (the recursion's pushforward/CoV step is sound, spectator-uniform) or
      fail (a genuine wall needing a different recursion variable/chart)? If it fails, propose the
      fix. Also: is the framing "pushforward density dR >= rho dSc" even the right way to think about
      this, or is the recursion better seen as holding R fixed and recursing on the core integrand?
</question>

<output_contract>
For each Qi: PROVEN (with the argument) / FALSE (with counterexample) / NEEDS-CARE (with the gap).
Then a one-paragraph VERDICT on O2 (sound / wall) and, if sound, the cleanest spectator-independent
domination. Separate what you can prove from what you conjecture.
</output_contract>

<grounding_rules>
- Exact reasoning; cite Monte-Carlo only as a heuristic guide, never as proof.
- Do not assume the conclusion. The point is to independently check whether the M22->Sc translation
  argument (or any other) makes the R-integral of the Sc-core reduce to the free-box IH with
  spectator-independent constants, AND whether the additive (Morse + core) threshold survives.
- Keep the j=1 case primary; comment on j>=2 only for failure modes.
</grounding_rules>
