<task>
Adjudicate a sharp truth-value about the local normal form of a specific polynomial loss at a
specific point, for a Lean 4 + Mathlib (v4.29) formalization. I need to know whether a regular/core
("Morse-Bott"-style) split is achievable by an EXPLICIT algebraic/analytic change of variables
(polynomial map + division-by-units, local diffeomorphism written down in closed form), OR whether it
FUNDAMENTALLY requires the general constant-rank theorem / Morse-with-parameters / submersion normal
form (which is ABSENT from Mathlib v4.29).
</task>

<setup>
Deep linear network, L=2 layers, all widths 2, target rank r=1.
- Parameters: two 2x2 real matrices A0, A1. Product P = A0 @ A1. Loss = ||A0 A1 - B||_F^2 (squared
  Frobenius), B a fixed rank-1 target.
- "Deepest point" w* is the explicit block-normal rank-exactly-1 chain. In the canonical normalized
  gauge (B = e_{00}, the (0,0) unit), w* = (A0* = [[1,0],[0,0]], A1* = [[1,0],[0,0]]).
- Perturb A = w* + W, W = (W0, W1), 8 real perturbation coordinates
  a00,a01,a10,a11 (W0) and b00,b01,b10,b11 (W1).

The four error-matrix entries E_ij = (A0 A1 - B)_ij are (EXACT, verified in sympy):
  E00 = a00 + b00 + a00*b00 + a01*b10
  E01 = b01 + a00*b01 + a01*b11
  E10 = a10 + a10*b00 + a11*b10
  E11 = a10*b01 + a11*b11            (NO linear part: this is the singular "core" entry)
The loss is exactly F = E00^2 + E01^2 + E10^2 + E11^2.

The error-Jacobian at W=0 has rank 3 = nReg = -r^2 + r(H0 + H2) = -1 + 1*(2+2) = 3 regular directions.
The claimed split (Aoyagi 2023 Theorem 3): F ~= (sum of nReg squares) + ||core||^2, where the core is
the reduced-width product loss on widths M_s = H_s - r = (1,1,1), r=0, i.e. core = (scalar*scalar)^2.
</setup>

<facts_established>
1. The map Phi: (a00,a01,a10,a11,b00,b01,b10,b11) |-> (E00, E01, E10, a00, a01, a11, b10, b11) is a
   LOCAL DIFFEOMORPHISM at 0: its Jacobian determinant at the origin is exactly 1.
   Equivalently: solve the three "pivot" variables (b00, b01, a10) as explicit rational functions of
   the new regular coords (x1=E00, x2=E01, x3=E10) and the kept core vars (a00,a01,a11,b10,b11), each
   pivot solved by DIVISION BY A UNIT (denominators (1+a00) and (1 - a01 b10 + x1), both = 1 at origin).
2. Under Phi, the loss becomes EXACTLY: F = x1^2 + x2^2 + x3^2 + core(x,c)^2, where
       core = [ a11*b11*(1 - a01 b10 + x1) + (a01 b11 - x2)(a11 b10 - x3) ] / (1 - a01 b10 + x1).
3. At the regular-zero slice {x1=x2=x3=0}: core = a11*b11 / (1 - a01 b10) = a11*b11 * UNIT,
   unit(0)=1. So on the slice the core is the reduced (1,1,1) product a11*b11 times an analytic unit.
4. BUT off the slice, core still depends on x1,x2,x3. In particular core's numerator contains the
   PURE-REGULAR cross-term "+ x2*x3" (degree 2, NO core variable), plus mixed terms
   "- a01 b11 x3 - a11 b10 x2 + a11 b11 x1".
   So core = a11*b11 + x2*x3 + (mixed/higher) over a unit; the regular block x1^2+x2^2+x3^2 + core^2
   has, in its (x2,x3) quadratic part, the Hessian [[2, 2*a11*b11],[2*a11*b11, 2]] which is positive
   definite for |a11*b11|<1 (a neighborhood of the deepest point). So the regular quadratic form stays
   nondegenerate but is NOT a clean orthogonal sum of squares + a core-only function: there is genuine
   regular<->core entanglement through the x2*x3 term inside core^2.
</facts_established>

<questions>
Q1. Is the regular/core split at this SPECIFIC deepest point achievable by a further EXPLICIT
    algebraic/analytic change of variables (polynomial + unit-division, a local diffeo written in
    closed form) that brings F to the clean form  Sum_{i<3} y_i^2 + (unit * a11*b11)^2  with the core
    depending only on core variables (modulo an analytic unit that S1.3 unit-invariance removes)?
    Or does eliminating the x2*x3-type cross-term inside core^2 require completing-the-square /
    a Morse-Bott / constant-rank / parameter-dependent normal-form theorem?

Q2. Concretely: F = x1^2 + x2^2 + x3^2 + (a11 b11 + x2 x3 + ...)^2. Consider the substitution that
    completes the regular block. Is there an explicit triangular/polynomial change y1=x1, and y2,y3
    explicit functions of (x2,x3, core vars) making the (x2,x3,core^2) part separate as
    y2^2 + y3^2 + (pure core)^2? Does such a change have a unit Jacobian at 0 and stay explicit
    (closed-form, no implicit function theorem invocation that Mathlib can't discharge)?

Q3. RLCT-level fallback: even if a clean coordinate split is not available, is the RLCT of
    F = x1^2+x2^2+x3^2 + core(x,c)^2 (with the x2 x3 entanglement) still EQUAL to nReg/2 + lambdaCore
    = 3/2 + lambdaCore((1,1,1)), provable by an ELEMENTARY squeeze (two-sided comparison |F| bounded
    above/below by clean split losses on a neighborhood, using only RLCT-monotonicity which we have
    green, NOT a normal-form theorem)? I.e. does the entanglement matter for the RLCT value at all?

Q4. Sharpest: name the truth-value. Pick exactly one and justify with the mechanism:
    (A) "EXPLICIT-ALGEBRAIC: the deepest-point split needs only polynomial maps + unit-division +
        finite triangular elimination + RLCT unit-invariance/monotonicity (all elementary); NO general
        constant-rank/Morse theorem." -- with the explicit final change exhibited.
    (B) "CONSTANT-RANK-GATED: separating regular from core at the deepest point fundamentally needs the
        Morse-Bott / constant-rank / parameter-dependent normal form (same Mathlib gap as the
        arbitrary-fibre-point case)." -- with the cross-term that forces it pinned.
    Note the difference from the ARBITRARY fibre point v (where the core HAS a nonzero linear part and
    the split is known to be genuinely constant-rank-gated). At the DEEPEST point the core has NO
    linear part. Does that structural fact tip it to (A)?
</questions>

<output_contract>
- A single truth-value (A) or (B) for Q4, with the load-bearing mechanism.
- For Q1/Q2: either EXHIBIT the explicit further change of variables (closed form) that cleans the
  cross-term, or PROVE no polynomial/unit-division change can (and say what is the minimal extra
  ingredient: completing-the-square as a polynomial map? a 1-variable IFT step? full constant-rank?).
- For Q3: a yes/no on whether the RLCT VALUE is 3/2 + lambdaCore regardless, via elementary squeeze,
  with the two comparison bounds if yes.
- Label every step PURE-ALGEBRA / UNIT-DIVISION / COMPLETE-THE-SQUARE / NEEDS-IFT / NEEDS-CONSTANT-RANK.
- Distinguish FACT (you verified) from INFERENCE.
</output_contract>

<grounding_rules>
- This is for a Lean formalization that is ONE-CITATION-ONLY (the only allowed external citation is the
  monomial normal-crossing RLCT extraction). A "constant-rank theorem needed" verdict means the rung is
  Mathlib-gated and must be roadmapped; an "explicit-algebraic" verdict means it is buildable now from
  green primitives (block elimination, RLCT monotonicity, unit-invariance, smooth-block Fubini value).
- Do NOT hand-wave "by the splitting lemma" -- the whole question is whether the splitting lemma is
  AVOIDABLE here by explicit construction.
- A wrong "explicit" verdict sends a formalizer into an unbuildable construction; a wrong "gated"
  verdict roadmaps a buildable rung. Be rigorous about which cross-terms genuinely obstruct.
</grounding_rules>
