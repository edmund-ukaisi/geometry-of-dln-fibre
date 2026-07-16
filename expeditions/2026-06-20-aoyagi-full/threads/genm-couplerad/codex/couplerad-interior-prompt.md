<task>
Two self-contained real-analysis questions about finiteness of integrals of powers of quadratic forms over a bounded box. Answer each independently and rigorously. Do NOT read any files; everything you need is below. Give exact thresholds with proof sketches.
</task>

<context>
All matrices are real. frobSq(A) = sum of squares of entries = ‖A‖²_Frobenius = tr(A Aᵀ). "Box" means a bounded hypercube like [−1,1]^N in the entries of the free variables, with Lebesgue measure. A "PSD quadratic form of rank ρ" on ℝ^N is q(x)=xᵀHx with H PSD of rank ρ.
</context>

<question id="Q1">
Fix real matrices S (size m×n) and K (size u×n), with rank(S)=r_S and rank(K)=r_K. Let the free variables be X (size u×m) and Y (size a×u), integrated over a bounded box B (each entry in [−1,1]); X and Y are independent blocks. Define
    f(X,Y) = frobSq(X·S) + frobSq(Y·K).
For which real q>0 is  ∫_B f(X,Y)^{−q} dX dY  finite?
Sub-parts:
(a) Show f is a PSD quadratic form in the combined variable vec(X,Y), and determine its rank ρ in terms of u, a, r_S, r_K.
(b) State the exact finiteness threshold: ∫_B f^{−q} < ∞ iff q < ? (give it in terms of u,a,r_S,r_K).
(c) Is the term frobSq(X·S) load-bearing for finiteness? Concretely: can ∫_B frobSq(Y·K)^{−q} dY diverge (over the box) for the same q at which ∫_B f^{−q} converges? Characterize exactly when this "load-bearing" gap occurs (i.e. the range of q where the Y-only integral diverges but the sum is finite).
(d) If additionally the box excludes a measure-zero set {det(some u×u sub-block of X)=0} (i.e. X constrained invertible in one square block), does the threshold change? Why / why not?
</question>

<question id="Q2">
Fix a real matrix B (size (b−1)×n) of full row rank b−1 (so b−1 ≤ n), a real matrix R (size a×n), and a constant W ≥ 0. Let Γ range over ℝ^{a×(b−1)} (all of it, unbounded). Let Π = I_n − Bᵀ(BBᵀ)⁻¹B be the orthogonal projection onto the orthogonal complement of the row space of B. Evaluate / bound
    J = ∫_{ℝ^{a×(b−1)}} ( W + frobSq(R + Γ·B) )^{−c'} dΓ.
Sub-parts:
(a) Prove the change-of-variables/decomposition frobSq(R + Γ·B) = frobSq(R·Π) + frobSq(R(I−Π) + Γ·B), and that as Γ ranges over ℝ^{a×(b−1)}, the term Γ·B ranges over a·(row space of B) freely with Jacobian det(BBᵀ)^{a/2}.
(b) Conclude a closed form J = det(BBᵀ)^{−a/2} · Cst(a,b−1,c') · (W + frobSq(R·Π))^{−(c' − a(b−1)/2)}, and give the constant Cst and the exact condition on c' for convergence.
(c) State how the exponent c' is reduced to c'' = c' − a(b−1)/2 by this integration.
</question>

<output_contract>
For Q1: (a) the rank ρ, (b) the exact "q < threshold" condition, (c) exact characterization of the load-bearing gap, (d) yes/no + one-line reason. For Q2: (a) the decomposition proof, (b) the closed form with the exact constant and convergence condition, (c) the c'' formula. Keep it rigorous and concise; flag any assumption you need (e.g. genericity, box containing the origin).
</output_contract>

<grounding_rules>
Do not read files or search a codebase — the problem is fully specified above. Standard fact you may cite: ∫_{ℝ^d}(‖y‖²+κ)^{−q}dy = π^{d/2} Γ(q−d/2)/Γ(q) · κ^{d/2−q} for q>d/2, κ>0; and the RLCT of a rank-ρ PSD quadratic form is ρ/2 (∫ over a box neighborhood of its zero-set of q^{−s} is finite iff s < ρ/2). Distinguish clearly what you prove vs. assume.
</grounding_rules>
