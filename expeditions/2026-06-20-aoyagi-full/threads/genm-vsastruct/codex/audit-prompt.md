<task>
Adjudicate a FIDELITY question: a Lean lemma proves finiteness of a "clean-coordinates" model integral;
is the deferred change-of-variables to the LITERAL integral genuinely finiteness-preserving, or a hidden
gap? Exact reasoning; I withhold my lean.
</task>

<setup>
The literal one-peel integral (of a matrix-multiplication RLCT finiteness proof) is, after banked
pivot/Schur/shear reductions, the "corner slice" integrated over the DEEP LAYER A2 (a free 3×4 real
matrix, integrated over a box):
   J_literal = ∫_{A2 box} S(U0(A2), U1(A2); c') dA2,
   S(U0,U1;c') = ∫∫_{[0,1]^2} u0^3 u1^2 (u0^2 U0 + u1^2 U1)^{-c'} du0 du1   (banked finite for c'<7/2 if U0,U1>0),
   U0(A2) = ‖w1 A2‖^2 + δ^2 ‖w2 A2‖^2,   U1(A2) = a_piv^2 ‖v̄ A2‖^2,
where w1,w2,v̄ ∈ R^3 are fixed test directions (the resolved front rows), δ,a_piv ≠ 0 scalars.

The LANDED lemma proves instead the CLEAN-COORDINATES integral:
   J_clean = ∫_{X ∈ [-T,T]^8} ∫_{Z ∈ [-T,T]^4} S(‖X‖^2, ‖Z‖^2; c') dX dZ  < ∞   for c'<7/2,
i.e. it posits U0 = ‖X‖^2 (X ∈ R^8), U1 = ‖Z‖^2 (Z ∈ R^4), integrated over PRODUCT boxes, and proves
finiteness by weighted-AM-GM (min-cut weights (4/7,3/7)) + Tonelli into two deep Morse integrals
∫(∑X^2)^{-w0 c'}, ∫(∑Z^2)^{-w1 c'} (finite iff w_k c' < d_k/2, d0=8, d1=4) and a u-monomial (binding 7/2).
The map A2 ↦ (X,Z) := (w1 A2, δ w2 A2 ; a_piv v̄ A2) is the deferred "casting"; A2 is 12-dim, (X,Z) is
(8+4)=12-dim.
</setup>

<questions>
Q1 (is the casting a measure-preserving / finiteness-preserving CoV?). Is A2 ↦ (X,Z) a linear
   isomorphism R^12 → R^12? Compute its Jacobian (in terms of the 3×3 matrix M = [w1;w2;v̄] and δ,a_piv).
   Is it constant? If w1,w2,v̄ are an orthonormal basis of R^3, is the map orthogonal (Jacobian 1)? For a
   general BASIS, is finiteness still preserved (constant nonzero Jacobian)?

Q2 (domain: product box vs parallelepiped). The literal A2 ranges over a box [-1,1]^12; its image under
   the linear map is a PARALLELEPIPED M⊗I·(box), NOT the product box [-T,T]^8×[-T,T]^4 the clean lemma
   uses. Does this domain mismatch affect FINITENESS? (The integrand S(‖X‖^2,‖Z‖^2) is ≥0 and singular
   only at (X,Z)=0.) Does J_clean<∞ ⟹ J_literal<∞ via enclosing the parallelepiped in a box?

Q3 (when does the casting FAIL, and is it a hidden gap?). The casting needs M = [w1;w2;v̄] invertible
   (w1,w2,v̄ linearly independent). When M is singular (test directions dependent), the map is not an iso
   — what happens to the codims d0,d1 and to finiteness? Is the invertibility a benign chart hypothesis
   (the resolved front is full-rank on the good chart) or a hidden gap? Also: are U0,U1 EXACTLY the clean
   ‖·‖^2 forms, or could the literal units have cross-terms / a different quadratic form that the clean
   ‖X‖^2 model misrepresents?
</questions>

<output_contract>
For Q1–Q3: exact algebra + "FACT" vs "INFERENCE". End: is J_clean<∞ ⟹ J_literal<∞ a GENUINE
measure-preserving (up to constant Jacobian) finiteness-preserving follow-on — or is the casting a hidden
load-bearing gap? State the exact hypotheses the casting follow-on must carry.
</output_contract>

<grounding_rules>
Exact linear-algebra / measure CoV. A constant nonzero Jacobian preserves finiteness. Keep "measure-
preserving" (Jacobian 1) separate from "finiteness-preserving" (constant nonzero Jacobian). Flag if the
literal units are NOT clean squared norms.
