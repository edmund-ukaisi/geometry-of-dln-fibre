**Q1**  
Verdict: TRUE — Follows from the Ky Fan (a.k.a. Weyl’s) singular-value inequality, valid for rectangular matrices: σᵢ(A₀Z_deep) ≤ σ₁(A₀)σᵢ(Z_deep). — FACT

**Q2**  
Verdict: VALID WITH RANGE CONDITION — If m = min(M₁,N)−j ≤ min(M₂,N), then σ_m(Z_deep) ≥ ε/σ₁(A₀) ≥ ε/√(M₁M₂), so rank ≥ m and Z_deepZ_deepᵀ ⪰ (ε²/(M₁M₂))·U_sU_sᵀ pointwise; if m exceeds min(M₂,N), the shell S_j is empty, so the stated conclusion is vacuous. — FACT

**Q3**  
Verdict: TRUE — Using Q1 with the chosen δ gives σ_m(Z_deep) ≥ ε/σ₁(A₀) ≥ δ for every (A₀,Z_deep) with Z_full ∈ S_j, so {A' : Z_full ∈ S_j} ⊆ {A' : deep params ∈ G}; no counterexample exists once m ≤ min(M₂,N), while m larger makes S_j empty. — FACT

**Q4**  
Verdict: VALID — For F ≥ 0, indicator domination 1_{S_j} ≤ 1_G yields ∫_{S_j} F ≤ ∫_G F by monotonicity/Tonelli, and the row-split (z₀, deep params, A_cor) is a coordinate projection, hence measure-preserving and measurable, so the iterated integral over A_cor is well-defined. — FACT

**Q5**  
Verdict: VALID — Defining Z_f(z)=Z_deep(z) on G and a fixed full-rank V off G preserves the integral bound while enforcing (R),(P) everywhere; the needed measurability is the standard Borel functional-calculus fact that B ↦ 1_{[δ²,∞)}(B) is Borel for symmetric B=Z_deepZ_deepᵀ, so the strong-subspace projection U_s(z) is measurable on G. — FACT

**Q6 Overall**  
Verdict: LABOUR — The scheme is sound and provable; the most likely failure point is neglecting the range condition m ≤ min(M₂,N), under which the shell constraint would be void.
