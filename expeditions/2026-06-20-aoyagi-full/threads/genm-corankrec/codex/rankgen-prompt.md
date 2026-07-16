<task>
Scope-soundness check on a rankgen hypothesis for a determinantal "charge" integrability.

SETUP (self-contained). We integrate over a matrix parameter space a product of negative-power weights and want the Lebesgue integral finite. One weight is a "charge": det(Q Qᵀ)^(−a/2), where Q = A·Z is a b×N real matrix (Q Qᵀ is the b×b Gram), a,b are nonnegative integers, and Z ranges over an M₂×n real matrix parameter of GENERIC rank ρ = min(M₂,…) (a "deep tail min"). Near the locus where Q Qᵀ degenerates (det → 0), the charge det(QQᵀ)^(−a/2) blows up. The other weight is a coupled loss (E_top+E_tr)^(−q). A positive monomial measure factor (Schur/Vandermonde Jacobian, e.g. ∏ σ_i^{β_i−1} on the singular-value ray) LOWERS the effective exponent.

The claim under review restricts to scope "a + b + 1 ≤ ρ" (i.e. a+b ≤ ρ−1). An empirical exact scan found the charge becomes NON-integrable (drops the resolved codim below the required floor) when a+b ≥ ρ+1, and is dominated (inert) when a+b ≤ ρ−1.

QUESTION. An upstream module can only supply "b ≤ ρ" (a bound on the Gram dimension b alone), NOT the combined "a+b ≤ ρ−1". Is the combined bound on a+b genuinely necessary to control the charge's near-degeneracy singularity, or could a bound on b alone suffice in some regime? Concretely: in the integrability of det(QQᵀ)^(−a/2) near {det QQᵀ = 0} over a rank-ρ family, is the power exponent 'a' load-bearing (must a be bounded too), or is the singularity governed only by the corank/dimension b of the Gram? Give the abstract reason (how the a-th power interacts with the codimension of the degeneracy locus and the compensating monomial measure exponents), and state whether "b ≤ ρ" alone can ever be sufficient.
</task>

<output_contract>
1. VERDICT: is 'a' load-bearing? (yes/no + one line)
2. The abstract mechanism (exponent vs codimension-of-degeneracy-locus vs measure), 4-8 lines.
3. Whether "b ≤ ρ" alone can suffice in any regime, and if so which.
4. Flag every step that is inference vs standard fact.
Keep under ~250 words.
</output_contract>

<grounding_rules>
State plainly when a claim is a general integrability fact vs an inference about this specific charge. Do not invent the specific numeric floor; reason structurally.
</grounding_rules>
