<task>
Resolution of singularities / RLCT question. Reason from first principles; you have NO code and NO web.

DEFINITION (real log-canonical threshold): λ(F) at origin = sup{ c : ∫_{U} |F(w)|^{−c} dw < ∞ }, U a
neighbourhood of 0. So "λ ≥ c" ⟺ "∫_U |F|^{−c} < ∞".

Aoyagi computes λ of F = ‖∏_{s=1}^L C^(s)‖² (a real-analytic function, homogeneous of degree 2L) at the
origin by an EXPLICIT FINITE recursive sequence of monomial blow-ups along named submanifolds, terminating
in an exact ideal equality ⟨∏C⟩ = ⟨diag(monomials)⟩ (normal-crossing form) with explicit Jacobian
∏ u^{M−1}, then reads λ = ½·min over the monomial exponents.

I need a clean ruling on TWO statements and their logical relationship:

A = "λ(F) at 0 = ½·min{exponents}" (the exact value, both bounds), proved by the blow-up + monomial read-off.
B = "∫_{box around 0} |F|^{−c'} dw < ∞ for every c' < ½·min{exponents}" (finiteness strictly below the
    threshold, on a bounded box neighbourhood).

QUESTIONS:
(1) A proper birational blow-up is an isomorphism off a measure-zero exceptional divisor, giving an EXACT
change-of-variables ∫|F|^{−c'}dw = ∫|monomial|^{−c'}·|Jac|du. Does this deliver BOTH sides of A (finiteness
below AND divergence above the threshold), from the one and the same normal-crossing form?
(2) Is B exactly the "λ ≥ ½·min" half of A, i.e. the finiteness-below-threshold direction, so that a
complete honest proof of A (the equality via the blow-up) NECESSARILY establishes B along the way — hence
B need not be proved by any SEPARATE machinery (e.g. an independent iterated-fibre / Schur recursion on the
box integral)? Or is there a genuine residual: does establishing finiteness ON A BOX require a
finite-COVER of the box by the blow-up charts (the blow-up gives finiteness in each chart's coordinate
patch; the box must be covered by finitely many such patches and each patch pullback contained in a
polydisc) that A's pointwise-at-origin statement does NOT automatically include?
</task>

<output_contract>
Exactly this, terse:
1. BOTH-BOUNDS: YES/NO + one sentence.
2. B-vs-A: SUBSUMED or SEPARATE + one sentence naming the exact residual if SEPARATE.
3. RESIDUAL-RISK: the single most important thing a formaliser must check to make "A ⟹ B" airtight.
4. VERDICT: one line.
Keep the whole answer under 250 words.
</output_contract>

<grounding_rules>
Standard resolution-of-singularities + local-RLCT facts only. Flag inference vs standard fact. I have
withheld my own conclusion; do not guess it. If B is genuinely separate, say so with the sharpest reason.
