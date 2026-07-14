<task>
Adjudicate a linear-algebra / measure-theory question that decides whether a change-of-variables
in a Laplace-integral resolution is TRUE and PROVABLE. Answer decisively; separate FACT from INFERENCE.
</task>

<setup>
Real matrices. A deep-linear product is factored as a head-split:

  Z_full = A0 · Z_deep

where
  A0     : M1 x M2   (the leading layer; a free integration variable over the box [-1,1]^{M1 x M2})
  Z_deep : M2 x N    (the product of the remaining deep layers; depends on "deep params")
  Z_full : M1 x N.

A row-embedding kappa : Fin u ↪ Fin M1 splits the M1 rows of A0 into u "pivot" rows (call them z0,
a u x M2 block) and b = M1 - u "corank" rows (call them A_cor, a b x M2 block). Correspondingly the
rows of Z_full split into pivot rows  Qp = z0 · Z_deep  (u x N)  and corank rows  Qb = A_cor · Z_deep
(b x N).

There is a "singular shell" restriction on the FULL product:
  Z_full ∈ S_j   :⟺   exactly j of the singular values of Z_full are < ε   (for a fixed j < r, ε>0).
Equivalently: Z_full has at least (min(M1,N) - j) singular values ≥ ε.

A downstream lemma ("corank weight bound") needs, on the deep factor Z_deep, BOTH of:
  (R) rank(Z_deep) ≥ m   for some m with b ≤ m ≤ M2, and
  (P) a Loewner PSD floor:  Z_deep Z_deepᵀ ⪰ δ² · U_s U_sᵀ,  where U_s : M2 x m has U_sᵀ U_s = I_m
      (an isometry onto an m-dim "strong" subspace), δ > 0.
The lemma's constant is uniform in A_cor, U_s, and the pivot data; A_cor ranges over the FULL box
(the shell restriction is NOT imposed on A_cor separately — only Z_full ∈ S_j is imposed).

Numbers you may use: entries of A0 lie in [-1,1], so σ_1(A0) ≤ ‖A0‖_F ≤ √(M1·M2).
</setup>

<questions>
Q1 [exact]. Is it TRUE that the top singular value factorization gives, for every index i,
   σ_i(Z_full) = σ_i(A0 · Z_deep) ≤ σ_1(A0) · σ_i(Z_deep)?
   State the exact inequality/theorem name and whether it holds for rectangular matrices.

Q2 [exact]. Consequence: on the shell Z_full ∈ S_j (so σ_{min(M1,N)-j}(Z_full) ≥ ε), does it follow that
   σ_{min(M1,N)-j}(Z_deep) ≥ ε / σ_1(A0) ≥ ε / √(M1·M2)?  Hence rank(Z_deep) ≥ min(M1,N) - j and a PSD
   floor (P) with δ = ε/√(M1·M2), m = min(M1,N) - j, U_s = top-m left singular vectors of Z_deep?
   Is this valid, and does it hold POINTWISE for each fixed (A0, Z_deep) with Z_full ∈ S_j?

Q3 [the crux, exact + inference]. The floor (R),(P) is a condition on Z_deep, which depends ONLY on the
   deep params — NOT on A_cor or z0. But the shell Z_full ∈ S_j couples A0 (= [z0; A_cor]) with Z_deep.
   Define G := { deep params : σ_m(Z_deep) ≥ δ } with δ = ε/√(M1 M2), m = min(M1,N)-j.
   CLAIM: the set { A' : Z_full ∈ S_j } (A' = (z0, A_cor, deep params)) is CONTAINED in { A' : deep params ∈ G }.
   i.e. Z_full ∈ S_j  ⟹  σ_m(Z_deep) ≥ δ. Is this containment TRUE? Give the proof or a counterexample.
   (Intuition to check: if σ_m(Z_deep) < δ then σ_m(Z_full) ≤ σ_1(A0)·σ_m(Z_deep) < √(M1M2)·δ = ε, so
    Z_full would have > (min - m) = j small singular values, i.e. NOT in S_j.)

Q4 [inference]. Given the containment in Q3, is the following domination valid for a nonneg integrand F ≥ 0?
   ∫_{A' : Z_full ∈ S_j} F(A')  ≤  ∫_{A' : deep params ∈ G} F(A')
   and can the RHS be written (after a measure-preserving row-split A' ↔ (z, A_cor), z = (z0, deep params))
   as  ∫_{z : deep(z) ∈ G} ∫_{A_cor} F  ?   Any measurability obstruction to defining G / restricting to it?

Q5 [inference]. To feed a downstream lemma that requires the floor to hold for ALL z (unconditionally),
   is it sound to define a PIECEWISE deep factor Zf(z) := Z_deep(z) on G, and Zf(z) := V (a fixed matrix
   with rank ≥ m and V Vᵀ ⪰ δ² U_s0 U_s0ᵀ) off G, so that (R),(P) hold for ALL z, while the domination
   ∫_{shell} F ≤ ∫_z (integrand built from Zf) still holds because the shell mass sits inside G where
   Zf = Z_deep? What is the one measurability lemma actually needed (measurable selection of U_s(z) =
   strong subspace / spectral projection of Z_deep(z))? Does Mathlib-style Borel functional calculus /
   measurable eigenprojection make U_s(z) measurable on G (where there is a spectral gap at δ²)?

Q6. Overall verdict: is the corrected statement (floor on Z_deep = Zf, with rescaled δ = ε/√(M1M2),
   realized via the shell⊆G containment + piecewise Zf) TRUE and PROVABLE (labour), or is there a genuine
   obstruction (reroute)? Name the single most likely failure point.
</questions>

<output_contract>
For each Q: verdict (TRUE/FALSE/valid/invalid), one-line justification, and FACT-vs-INFERENCE tag.
End with Q6 overall verdict (labour vs reroute) and the single most-likely failure point.
Do NOT assume my conclusion; I have deliberately withheld it.
</output_contract>

<grounding_rules>
- Singular value / Loewner / rank facts must be exact theorems (name them).
- If the Q3 containment is false, give an explicit small counterexample (M1,M2,N,j and matrices).
- Keep measure-theory claims at the level of "standard Tonelli / domain monotonicity / Borel selection";
  flag anything needing a non-standard disintegration.
</grounding_rules>
