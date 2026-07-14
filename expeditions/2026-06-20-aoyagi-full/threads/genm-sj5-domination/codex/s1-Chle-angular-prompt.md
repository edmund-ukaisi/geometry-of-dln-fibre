<task>
Adjudicate the finiteness of a specific multi-variable singular integral (a real-log-canonical-threshold /
Aoyagi-style convergence question) that gates a formalisation step. Decide EITHER direction; do not assume
it converges.

SETUP. A "chain" is a tuple of positive integers M = (M0, M1, M2, ..., M_last) (widths of a deep linear
network). Fix a chain and an integer "cut" u with 1 <= u <= min(M0,M1); set a = M0-u >= 1, b = M1-u >= 1.
Let n = M_last. Consider a matrix Q that is a product of independent generic real matrices of shapes
M1 x M2, M2 x M3, ..., i.e. Q is M1 x n with generic (maximal) rank rho := min(M1, M2, ..., M_last).
Split Q's rows into the top u rows Q_p (u x n) and the bottom b rows Q_b (b x n), so [Q_p ; Q_b] = Q.

THE INTEGRAL IN QUESTION ("the absorbed / angular integral"). Over the compact boxes
P in [-T,T]^{u x u}  and  B12 in [-T,T]^{u x b}  (T>0 fixed), with an exponent c > 0, is

    J(c) := integral over P, B12 of  frobSq( P * Q_p  +  B12 * Q_b )^{ -c }  dP dB12

FINITE, and for which c?  (frobSq(X) = sum of squares of entries of X.)

CONTEXT / why this shape. This is the front-layer "pivot block" of a change-of-variables in an RLCT
computation. Elsewhere the same construction introduces a determinant-radial blow-up P = s * Phat with
|det Phat| = 1 (s a scalar scale coordinate), and a worry was raised: on the |det|=1 sphere Phat can have
smallest singular value sigma_min(Phat) -> 0 while sigma_max(Phat) -> infinity (the sphere is NON-compact),
so P*Q_p can become small in some directions and the integrand could blow up. Separately, B12 is rescaled
by s^{-1} in that chart, which amplifies as s -> 0. The question is whether, after honestly accounting for
the box constraints and the blow-up Jacobian, J(c) converges. You may analyze J(c) directly in the ORIGINAL
(P,B12)-box coordinates (no blow-up) if that is cleaner -- the blow-up is only one chart, the integral is
coordinate-free.

FACTS ESTABLISHED so far (verify or refute; do not just accept):
- The map (P,B12) -> P*Q_p + B12*Q_b is linear from R^{u*M1} to R^{u*n}.
- Numerically its rank equals u*rho for generic Q (checked exactly on several chains incl. interior-min
  ones where rho comes from an interior width, e.g. M=(3,4,2,4) giving rho=2).
- For u=1, the sublevel volume Vol{ frobSq < eps } scales like eps^{rho/2} (log-log slope ~ rho/2 in MC).

WHAT I NEED:
1. The exact convergence threshold: the supremum of c for which J(c) < infinity, as a formula in
   (u, M1, n, rho, a, b). Justify via the geometry of the zero-locus { P*Q_p + B12*Q_b = 0 } (its
   dimension / codimension) and the standard "integral of dist-to-subspace^{-2c}" criterion.
2. Whether the non-compactness of the |det Phat|=1 sphere and the s^{-1}*B12 amplification actually cause
   a divergence, or whether they are compensated (and by what). Is the integrand bounded, or genuinely
   singular-but-integrable? (The claim I am checking asserts the integrand is BOUNDED because
   sigma_min(Phat) >= sigma_max(Phat)^{-(u-1)} on the det=1 sphere -- assess whether that reasoning is
   correct.)
3. Given a SECOND threshold from an independent "comparator" object, namely  c < minAdm(M')/2  where
   M' = (u, M2, ..., M_last) and minAdm is defined by the recursion
       minAdm(len<=1)=0;  minAdm(x,y)=x*y;  minAdm(M)=min over 0<=t<=min(M0,M1) of (M0-t)(M1-t)+minAdm(t,M2,...) :
   state the condition on the chain under which J's threshold is >= the comparator threshold (so that a
   finite multiplicative constant C with J(c) <= C * (comparator integral) can exist as c -> critical).
   Compute both thresholds for M=(3,3,3) at u=2 and for M=(3,3,4,4) at u=2 and report whether J is no more
   singular than the comparator in each.
</task>

<output_contract>
Four short sections:
(1) THRESHOLD: the formula sup{c : J(c)<inf} with a one-paragraph geometric justification.
(2) NONCOMPACTNESS: converge or diverge from the det=1 sphere / s^{-1} amplification, and a yes/no on the
    "sigma_min >= sigma_max^{-(u-1)} => bounded integrand" reasoning, with the correct reason.
(3) COMPARATOR: the exact condition (in chain data) for J-threshold >= minAdm(M')/2; the two worked cases
    (3,3,3)@u=2 and (3,3,4,4)@u=2 with numbers.
(4) VERDICT: one line -- does a finite C exist (a) always, (b) only under an explicit condition (state it),
    or (c) never. Tag each claim [FACT] (proof/exact) vs [INFERENCE].
Be terse. Do not pad.
</output_contract>

<grounding_rules>
Exact algebra only for load-bearing claims (dimension counts, convergence exponents). MC is a guide, not a
proof. If you find my "facts" wrong, say so explicitly. State the threshold as an exact rational/linear
expression, not a decimal.
</grounding_rules>
