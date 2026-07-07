<task>
You are red-teaming a Lean 4 formalisation for an EXACT-IDENTITY fidelity check. No Lean knowledge
needed — verify the underlying matrix algebra by hand and judge whether the stated identity is exact.

Setup. Real matrices in block form. A : t×t, B : t×b, C : a×t, D : a×b, with A invertible.
Δ = fromBlocks A B C D is the (t⊕a)×(t⊕b) block matrix [[A,B],[C,D]].
Q : (t⊕b)×n. Split Q by rows: Q_p = top t rows, Q_b = bottom b rows.
Define Q̃ := Q_p + A⁻¹ B Q_b  and  Γ := D − C A⁻¹ B  (Schur complement).
frobSq(M) := Σ_ij (M_ij)²  (squared Frobenius norm, sum of squares of entries).
u : real scalar; u • Δ scales every entry of Δ by u.

The formalisation proves this SINGLE claimed identity (the "corank step"):

    frobSq( (u • Δ) · Q ) = u² · ( frobSq(A · Q̃) + frobSq(C · Q̃ + Γ · Q_b) ).

Please independently verify or refute EACH of these three sub-claims by hand:

(1) frobSq((u•M)·Q) = u² · frobSq(M·Q) for any conformable M, Q (radial factors out, degree-2 homogeneous).

(2) The row-block split: frobSq(Δ·Q) = frobSq( top rows of Δ·Q ) + frobSq( bottom rows of Δ·Q ),
    and then:
      top rows of Δ·Q  = A·Q_p + B·Q_b  = A·Q̃                     (i.e. A·Q_p + B·Q_b = A·(Q_p + A⁻¹ B Q_b))
      bottom rows of Δ·Q = C·Q_p + D·Q_b = C·Q̃ + Γ·Q_b            (i.e. = C·(Q_p+A⁻¹B Q_b) + (D−CA⁻¹B)·Q_b)

(3) Whether the BOTTOM block genuinely RETAINS the cross-coupling term C·Q̃ — i.e. is the bottom block
    C·Q̃ + Γ·Q_b (cross-coupled), and NOT a clean decoupled Γ·Q_b alone? A prior (superseded) design
    allegedly wrote the residual as frobSq(A·Q̃) + frobSq(Γ·Q_b), dropping C·Q̃. Which is the correct
    EXACT POINTWISE identity in the original coordinates (no reparametrisation / no gauge change)?

(4) Separately: some resolution-of-singularities write-ups reduce the loss to a DECOUPLED
    "Morse pivot + δ²·downstream" sum via unit-triangular row+column operations on Δ. Note those row/col
    operations are NOT orthogonal, so they do NOT preserve the Frobenius norm pointwise. Confirm or refute:
    the decoupled form is a change-of-variables (measure/Jacobian) statement, whereas the identity above is
    an exact pointwise equality in the original coordinates that MUST keep C·Q̃. Are these consistent?
</task>

<output_contract>
Four short numbered verdicts (1)-(4), each: HOLDS / FAILS + the one-line reason (the key cancellation or
the counterexample). Then one final line: is the claimed corank-step identity EXACT as stated? YES/NO.
Be terse.
</output_contract>

<grounding_rules>
Do the algebra yourself; do not defer to the formalisation. If you assert a cancellation, name the
terms that cancel. Flag any step you are inferring vs. computing directly.
</grounding_rules>
