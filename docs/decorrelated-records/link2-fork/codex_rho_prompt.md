<task>
A real-log-canonical-threshold (RLCT) invariance question. The RLCT of a real-analytic
H >= 0 at 0 is the smallest pole of the zeta function Z(z) = ∫_{nbhd of 0} H(w)^{-z} dw
(equivalently controls ∫ H^{-z}); two H with the same local zeta poles have the same RLCT.

I have two nonnegative analytic germs at 0 in R^6 (coords r0,r1,s0,s1,T0,T1):

  F      = r0^2 + (a r0 + r0 T1)^2 + (b r1 + r1 T0)^2 + T0^2 + T1^2
  F_moved= r0^2 + (a r0 + r0 T1 + r0 r1 s1)^2 + (b r1 + r1 T0 + r0 r1 s0)^2 + T0^2 + T1^2

(a,b are fixed nonzero real constants.) F_moved is F with the substitution
T1 -> T1 + r1 s1 inside the second squared term and T0 -> T0 + r0 s0 inside the third —
a perturbation of the *argument* that vanishes at the origin.

QUESTION: Is RLCT(F_moved at 0) = RLCT(F at 0)?

I believe the route is two-sided comparability: show positive constants c1,c2 and a
neighborhood U of 0 with c1 F <= F_moved <= c2 F on U, which forces equal zeta poles
hence equal RLCT. The difference F_moved - F is a sum of terms each of total degree >= 5,
e.g. 2 a r0^2 r1 s1, 2 b r0 r1^2 s0, 2 T1 r0^2 r1 s1, 2 T0 r0 r1^2 s0, plus degree-6 squares.
</task>

<output_contract>
1. Is RLCT(F_moved) = RLCT(F)?  yes/no/conditionally.
2. Does the two-sided comparability c1 F <= F_moved <= c2 F actually hold on a neighborhood
   of 0?  Verify or refute. Address specifically: F is NOT a clean sum of squares
   (the squared terms expand to include cross terms like 2 a T1 r0^2 which can be negative);
   is F nonetheless bounded below by a sum of squares near 0 so that the domination denominator
   is sound?  Give the explicit lower bound or the obstruction.
3. Is the comparability theorem (c1 H1 <= H2 <= c2 H2 => equal RLCT) the correct tool, stated
   correctly?  Any hidden hypotheses (e.g. H analytic, nbhd compactness, H>=0)?
4. Is there any way the RLCT could DIFFER despite the perturbation being higher-order — i.e.
   a case where the degree->5+ perturbation changes the Newton polytope / the smallest pole?
</output_contract>

<grounding_rules>
- Reason from zeta-function poles / Newton-polytope / comparability only.
- Keep "comparability holds" distinct from "RLCT happens to be equal by coincidence".
- Flag inference vs. fact. A sharp certificate (or a sharp refutation) is what is wanted.
</grounding_rules>
