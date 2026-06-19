<task>
Two commutative-algebra / Krull-dimension questions, for a fidelity audit of a Lean 4 (Mathlib)
formalisation. Answer from your own knowledge of commutative algebra; do NOT assume my framing is correct.

Q1. STATEMENT CORRECTNESS.
Let A and S be commutative rings and f : A → S a ring homomorphism that is (a) INTEGRAL (every element
of S is integral over the image of A, i.e. f makes S an integral extension / module-finite-ish) and (b)
INJECTIVE. Is it a TRUE and STANDARD theorem that the Krull dimensions are equal, dim S = dim A?
  - Are BOTH hypotheses (integral AND injective) needed, and at minimum which is needed for which
    inequality? Specifically: which of dim S ≤ dim A and dim A ≤ dim S needs only integrality, and which
    additionally needs injectivity?
  - Is injectivity exactly the right/minimal extra hypothesis for the harder inequality, or is there a
    weaker standard hypothesis (e.g. ker f ⊆ nilradical, or "f makes Spec S → Spec A surjective")? Where
    precisely does injectivity enter — is it only at the bottom of a chain (so that the zero ideal of A
    pulls back / a prime over (0) exists)?
  - Note any subtlety with the integral-but-not-injective case (e.g. A → A/I): does dim drop, and why does
    that NOT contradict the ≤ direction?

Q2. PROOF-TOOL SOUNDNESS.
For the inequality dim A ≤ dim S of an integral extension, consider proving it via an order-theoretic
lemma of this exact shape (this is a real Mathlib lemma):

  krullDim_le_of_strictComono_and_surj :
     (g : X → Y) (hg : ∀ ⦃a b⦄, g a < g b → a < b) (hg' : Surjective g) : krullDim Y ≤ krullDim X

To get dim A ≤ dim S from this one would take X = Spec S, Y = Spec A, g = comap f = (P ↦ f⁻¹(P)).
The required hypothesis hg becomes: for primes a, b of S,  f⁻¹(a) < f⁻¹(b)  ⟹  a < b   (an ORDER-REFLECTION
/ "strictly-comonotone" property of comap), plus surjectivity of comap (lying-over).

  - Is that order-reflection hypothesis  (comap a < comap b ⟹ a < b)  actually TRUE for a general integral
    (injective) extension of commutative rings? If false, give a concrete minimal counterexample (a specific
    integral extension and two primes a, b of S with f⁻¹(a) < f⁻¹(b) but a, b incomparable, or a ≮ b).
  - If that lemma is unsound for this purpose, is the correct route instead a direct GOING-UP chain lift:
    take a maximal chain of primes p_0 < ... < p_n in A, and inductively lift it (lying-over at the bottom,
    going-up at each step) to a chain Q_0 < ... < Q_n in S of the SAME length with comap Q_i = p_i, hence
    dim A ≤ dim S? Confirm this going-up lift is the sound argument and that it needs injectivity only at the
    base (lying over the zero ideal / a prime contracting to (0)).
</task>

<output_contract>
Four short sections:
1. Q1-VERDICT: is dim S = dim A true+standard for integral injective; which hypothesis powers which
   inequality; is injectivity minimal and where it enters. One paragraph.
2. Q1-NONINJECTIVE: the A → A/I behaviour and why no contradiction. 2-3 sentences.
3. Q2-COUNTEREXAMPLE: is comap order-reflecting for integral extensions — YES/NO + a concrete counterexample
   if NO (name the rings, the extension, the two primes).
4. Q2-ROUTE: is the going-up chain lift the sound route, and where exactly injectivity is used. 2-3 sentences.
</output_contract>

<grounding_rules>
Flag clearly which statements are textbook-standard facts vs your inference. For the counterexample, give an
explicit construction you are confident is correct (rings + primes), not a vague "such things exist".
</grounding_rules>
