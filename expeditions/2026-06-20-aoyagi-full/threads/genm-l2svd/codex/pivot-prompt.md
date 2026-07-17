<task>
Independent adjudication of a matrix-integral "pivot-Gram disposal" design + its deeper-stratum obligation. Recompute from scratch; do not defer to my framing.

SETUP. Fix integers t,b,q,a (t = pivot size, b = corank width, a = another corank width; think t,b,q >= 2). Fixed matrices Q_p (t x q) and Q_b (b x q) (these come from a deeper matrix PRODUCT evaluated at an outer parameter A'). Variables: P (t x t, invertible) and B12 (t x b). Define the "pivot-shifted tail"
    Qtilde = Q_p + P^{-1} * B12 * Q_b     (a t x q matrix).
An earlier integration step (a Gaussian/aniso atom) has produced a factor  det(Qtilde * Qtilde^T)^(-a/2)  (the "pivot Gram", a t x t determinant to the power -a/2). We must show its integral over (P,B12) in a bounded box is finite (so the whole descent closes), by reducing to a banked lemma:
    QBOX:  for a FREE matrix W with t rows and m columns, integrated over a ball,  ∫ det(W W^T)^(-a/2) dW < ∞  provided  a < m - t + 1  (and t <= m).

Q1. PROPOSED CHANGE OF VARIABLES (top stratum, rank(Q_b) = b). 
  (i) B12 -> B' := P^{-1} B12 (P fixed), claimed Jacobian |det P|^b (a bounded numerator factor on a bounded P-box away from det P = 0). Then Qtilde = Q_p + B' Q_b.
  (ii) right-multiply by an orthogonal V (from the SVD of Q_b) so that Q_b V = [Psi | 0] with Psi (b x b) invertible; note det(Qtilde Qtilde^T) is invariant under Qtilde -> Qtilde V.
  (iii) then Qtilde V = [R1 + B' Psi | R2] (R1 = first b cols of Q_p V, R2 = last q-b cols). Substitute W := R1 + B' Psi (Jacobian |det Psi|^t), so W is a FREE t x b matrix, and
        det(Qtilde Qtilde^T) = det(W W^T + C0),  C0 := R2 R2^T  (positive semidefinite),
        hence det(Qtilde Qtilde^T)^(-a/2) = det(W W^T + C0)^(-a/2) <= det(W W^T)^(-a/2).
  (iv) bound the box by a ball, apply QBOX (m = b) at gate a < b - t + 1.
  Is this reduction CORRECT and COMPLETE for the top stratum (Q_b full row rank)? Name any gap (e.g. does the PSD-shift determinant inequality det(A + C0) >= det(A) for A = W W^T PSD, C0 PSD, hold; is the |det Psi|^t Jacobian right; does the right-orthogonal V couple to other integrand factors?).

Q2. THE JACOBIAN |det Psi|^t. Note |det Psi| = product of the nonzero singular values of Q_b. As the outer parameter A' drives Q_b toward LOWER RANK r < b (some singular values -> 0), |det Psi|^{-t} -> infinity, so the OUTER integral over A' of [ |det Psi(A')|^{-t} * (QBOX constant) ] can diverge. To repair it one blows up the rank-r stratum of Q_b (a determinantal variety, codimension (b-r)(q-r)) and charges a transverse-Jacobian weight. Question: for Q_b a GENERIC (free) b x q matrix, is ∫_{A'} |det Psi(A')|^{-t} finite for suitable t (i.e. is the rank-drop integrable), and what is the exact integrability threshold in terms of the codimension of the rank strata? Is this a standard (submersive) determinantal computation?

Q3. THE NON-SUBMERSIVE TWIST. In the real problem Q_b = Q_b(A') is NOT a free matrix — it is a deeper MATRIX PRODUCT of several free factors evaluated at A'. The multiplication map (free factors) -> product is NON-SUBMERSIVE at the rank-drop locus (its differential has a cokernel). Does the rank-r-stratum blow-up / transverse-Jacobian computation from Q2 carry over UNCHANGED to the product-parametrized Q_b(A')? Or can the non-submersive pullback change the codimension / discrepancy so that the naive transverse-Jacobian is wrong (the exceptional exponent can drop below the integrable threshold)? Is establishing the exact transverse-Jacobian for the product-parametrized rank strata a standard technique, or a genuinely open/research-grade step?
</task>

<output_contract>
- Lead: Q1 (reduction sound & complete for top stratum? Y/N + any gap). 
- Q2: is the free-Q_b rank-drop integral finite; the threshold; standard? Y/N.
- Q3: does it carry over to product-parametrized Q_b; standard-technique or research-grade? Be decisive and separate FACT from INFERENCE.
- Show the key computation for the PSD-shift determinant inequality and the rank-stratum codimension.
</output_contract>

<grounding_rules>
- Real-field Lebesgue integrability / elementary matrix analysis + a bit of determinantal-variety geometry. No RLCT black box.
- det is monotone on the PSD cone: A <= A + C0 (Loewner) => det A <= det(A+C0) for PSD A, C0.
- "rank-r stratum of a p x q matrix" has codimension (p-r)(q-r) as a determinantal variety.
- The multiplication map (A,B) |-> A B of matrices is non-submersive exactly where rank drops; its cokernel dimension on the balanced rank-k product-corank locus is floor(k^2/4) (this is a known fact in my project).
</grounding_rules>
