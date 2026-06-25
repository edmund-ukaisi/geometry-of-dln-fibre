<task>
I am an independent FIDELITY reviewer auditing a Lean 4 / Mathlib formalisation. A formaliser claims
to have proved that a localized quotient ring is an algebra-equiv to a free Schur localization, and
the CRITICAL correctness guard is that the "hard direction" of an ideal equality is EARNED by a Krull
height squeeze, not assumed. I need a decorrelated skeptical read on whether the squeeze logic is
sound and whether there is any way it could pass while proving the WRONG thing.

THE SETUP (all in a commutative ring Q = MvPolynomial B22block Sd, where Sd = Localization.Away
detSchurS is a domain of Krull dimension δ; B22block is a finite type of cardinality C = (p-r)(q-r)):

- K := Ψ(Iad)  -- image of the localized determinantal base ideal under an algebra equiv Ψ
- J := graphIdeal forcedB22 = span { X b - C(forcedB22 b) : b ∈ B22block }  -- the forced-graph ideal

The formaliser's proof of `K = J` (Lean `map_Iad_eq_graphIdeal_forcedB22`):

1. K.IsPrime  (image of a prime under an equiv)
2. J.IsPrime  (Sd is a domain ⟹ graphIdeal is the kernel of an aeval to a domain)
3. height J = C  (a translation automorphism carries the coordinate ideal span{X b} to J; coordinate
   ideal of MvPolynomial over a localization has height = card B22block = C). Proven, finite.
4. height K = height Iad  (Ψ an algebra equiv, height invariant under equiv)
   and  height Iad = C  (a landed determinantal-codimension brick over an alg-closed char-0 field).
   So height K = C. Equal finite values (reconciled by Nat.mul_comm of (p-r)(q-r) vs (q-r)(p-r)).
5. J ⊆ K  (each generator X b - C(forcedB22 b), times the unit C(detSchurS), is the Ψ-image of a
   bordered (r+1)-minor that lies in Iad; unit-cancellation).
6. CONCLUSION: K = J  via `eq_of_le_of_not_lt (J ⊆ K) (not (J < K))`, where `not (J < K)` is:
   assume J < K, then `Ideal.height_strict_mono_of_is_prime` (needs J.IsPrime, J.FiniteHeight,
   J < K) gives height J < height K, contradicting height J = height K.

The Mathlib lemma used:
  `Ideal.height_strict_mono_of_is_prime {I J : Ideal R} [I.IsPrime] (h : I < J) [I.FiniteHeight] :
   I.height < J.height`

<output_contract>
Answer these five questions, each in 2-4 sentences, flagging INFERENCE vs FACT:

Q1. Is the squeeze logically valid? I.e. does {J ⊆ K, J prime, J finite height, height J = height K}
    genuinely force J = K? Is `eq_of_le_of_not_lt` applied in the correct direction here (the goal is
    K = J, the proof produces (J = K).symm)?

Q2. THE KILL QUESTION: is there ANY way this proof could succeed while J is NOT the genuine forced
    graph ideal — i.e. could the squeeze "prove the wrong thing"? Consider: what if forcedB22 were 0
    or some wrong value? Would height J still be C? Would J ⊆ K still hold? Where exactly does the
    Schur content enter so that the equality is the INTENDED one?

Q3. Could either height secretly be ⊤ (infinite) or 0, making the equality vacuous or the FiniteHeight
    hypothesis false? The proof asserts height J = C as a finite Nat cast and supplies J.FiniteHeight
    from it. Is there a soundness gap if C = 0 (e.g. r = p or r = q)?

Q4. The hard direction the guard cares about is Iad ⊆ J (injectivity of Sd → A_loc/Iad). Does K = J
    (with K = Ψ(Iad), Ψ an equiv) genuinely deliver Iad = Ψ.symm J and hence the hard inclusion? Or is
    there a direction/transport subtlety that could leave the hard direction actually unproven?

Q5. Any other hidden assumption in steps 1-6 that would make "Iad ⊆ J is earned" false or circular —
    e.g. does step 5 (J ⊆ K) secretly already assume the reverse, or does height Iad = C secretly
    assume the presentation?
</output_contract>

<grounding_rules>
This is abstract commutative-algebra reasoning; you do not have the Lean source. Reason from the
stated structure. Explicitly mark each claim as FACT (standard commutative algebra / standard Mathlib
semantics you are confident of) or INFERENCE (depends on details you cannot see). Do NOT assume the
formaliser is correct; your job is to find the hole if there is one.
</grounding_rules>
