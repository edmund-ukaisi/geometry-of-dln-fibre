<task>
Verify (or refute) a REDUCTION that would dissolve a stratified-RLCT question into a single lower-arity RLCT. This is the crux of a convergence proof. Do NOT read files; fully specified below. Answer rigorously; if the reduction has a gap, say exactly where.
</task>

<setup>
Real matrices. Fix generic Z (M2×n, rank ρ), and Q_b (b×n, full row rank b, row(Q_b) ⊆ row(Z)). Π = I_n − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b. Let d := rank(ZΠ) = ρ − b.
Outer variable z0: u×M2 matrix, box [−1,1]^{u·M2}.
Inner x = (P, B, C): P (u×u), B (u×b), C (a×u), bounded box.
Q(z0) := z0·Z (u×n). Loss and integrals:
   f(z0,x) = frobSq([P|B]·[Q(z0);Q_b]) + frobSq(C·Q(z0)·Π),
   I = ∫_{z0 box} ∫_{x box} f^{−q} dx dz0   (q>0).
A competing analysis stratifies by the rank of Q(z0)·Π and asks whether the determinantal strata contribute independently. I want to check a REDUCTION that avoids stratification entirely.
</setup>

<reduction-to-verify>
Claim (4 steps):
(R1) Decoupling: with Ã_z := Q(z0)·Q_bᵀ(Q_bQ_bᵀ)⁻¹ and B̃ := B + P·Ã_z (an x-CoV with unit Jacobian),
     frobSq([P|B]·[Q;Q_b]) = frobSq(P·(Q·Π)) + frobSq(B̃·Q_b).
   Hence f = frobSq(P·Y) + frobSq(C·Y) + frobSq(B̃·Q_b), where Y := Q(z0)·Π = z0·(ZΠ) (u×n, rank ≤ d). So f depends on z0 ONLY through Y.
(R2) The map z0 ↦ Y = z0·(ZΠ) is a linear surjection from u×M2 onto u×(row(ZΠ)) ≅ u×d, with u·(M2−d)-dim kernel. So ∫_{z0 box} (⋯) dz0 = (const Jacobian)·∫_{kernel box}[∫_{Y box'} (⋯) dY] — the kernel directions integrate to a finite constant (bounded box), and Y ranges over a u×d box-image.
(R3) So I = C1·∫_{Y,P,C,B̃ box} ( frobSq(E·Y) + frobSq(B̃·Q_b) )^{−q}, with E := [P;C] ((u+a)×u). frobSq(P·Y)+frobSq(C·Y) = frobSq([P;C]·Y) = frobSq(E·Y).
(R4) This is the arity-3 "multiplication loss" integral for the 2-layer chain (u+a, u, d) — the product E·Y (size (u+a)×d) through the middle dimension u — plus a FREE Gaussian block frobSq(B̃·Q_b) of rank u·b. Its finiteness threshold (RLCT-numerator) is u·b + Λ, where Λ is the RLCT-numerator (2·learning-coefficient) of ∫ frobSq(E·Y)^{−q} over boxes for the chain (u+a,u,d).
</reduction-to-verify>

<questions>
(1) Verify R1 (the Frobenius-orthogonal split — is B̃·Q_b orthogonal to P·(QΠ) in Frobenius inner product, given Q_b·Πᵀ = 0?) and that f factors through Y. Any hidden z0-dependence outside Y?
(2) Verify R2: is z0 ↦ z0·(ZΠ) genuinely surjective onto u×d with the kernel integrating freely over the bounded box (so no extra z0-singularity is lost)? Does the box-image of Y cause any boundary issue vs. a full neighborhood of Y=0?
(3) Verify R4: is ∫(frobSq(E·Y)+frobSq(B̃Q_b))^{−q} over boxes finite iff 2q < u·b + Λ, with Λ the (u+a,u,d) two-layer RLCT-numerator, and the u·b coming from the free B̃-block (rank of B̃↦B̃Q_b is u·b since Q_b full rank b)?
(4) THE KEY CROSS-CHECK: the competing stratified analysis gives finiteness iff 2q < min_{0≤ℓ≤min(u,d)} φ(ℓ), φ(ℓ) = ρ₀ + ℓ² + (d−2u−a)ℓ, ρ₀ = (u+a)·min(u,d) + u·b. IS min_ℓ φ(ℓ) EQUAL to u·b + Λ (i.e., does the reduction give the SAME threshold as the direct stratification)? Compute Λ = the (u+a,u,d) two-layer RLCT-numerator (you may use the known formula for the learning coefficient / real-log-canonical threshold of a two-layer / rank-≤u matrix-factorization model with matrix sizes (u+a)×u and u×d), and check min_ℓ φ − u·b = Λ. If they agree, the reduction dissolves the stratification (the strata-independence question is subsumed by the arity-3 RLCT). If they disagree, the reduction has a gap — locate it.
</questions>

<output_contract>
(1)-(3): confirm or find the gap in each reduction step. (4): the closed form Λ for the (u+a,u,d) two-layer RLCT-numerator, and whether min_ℓ φ − ub = Λ. State clearly: does the reduction hold, dissolving the stratification into the arity-3 base case? Concise, rigorous; flag genericity assumptions.
</output_contract>

<grounding_rules>
No files. Distinguish proven vs assumed. The two-layer (matrix factorization) RLCT is a known result (Aoyagi–Watanabe); use it. If the box vs. full-space distinction matters for the two-layer threshold, note it.
</grounding_rules>
