<task>
A self-contained real-analysis question about a COUPLED integral: an inner integral over x of a power of a PSD quadratic form whose coefficients depend on an outer variable z, then integrated over z. I want the exact finiteness threshold for the coupled integral, and a check of whether a crude "smallest-singular-value" bound is valid. Do NOT read any files. Answer rigorously with thresholds + proof sketches.
</task>

<setup>
All matrices real. frobSq(A)=‖A‖²_Frobenius. Fix generic matrices Z (u×m→ actually m×n, size m×n, rank ρ, with ρ ≤ m and ρ ≤ n), and Q_b (b×n, full row rank b). Let Π = I_n − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b be the orthogonal projection off row(Q_b).

Outer variable: z, a u×m matrix, integrated over the box z ∈ [−1,1]^{u m} (dimension N = u·m).
Inner variables: x = (P, B, C) with P (u×u), B (u×b), C (a×u), integrated over a bounded box, P constrained invertible (a measure-zero exclusion).

Define Q(z) := z·Z  (u×n). The loss:
    f(z,x) := frobSq( [P | B] · [Q(z) ; Q_b] ) + frobSq( C · Q(z) · Π ),
where [Q(z);Q_b] is the (u+b)×n row-stack. Note f = ‖L(z)·vec(x)‖² for a linear map L(z) depending (linearly, through Q(z)=zZ) on z.

Inner integral:   g(z) := ∫_box f(z,x)^{−q} dx    (q>0 real).
Coupled integral: I := ∫_{z ∈ box} g(z) dz.

Facts you may use: for a rank-ρ₀ PSD quadratic form on a box containing 0 in the closure of its zero-set, ∫_box (form)^{−s} < ∞ iff s < ρ₀/2. And ∫_{ℝ^d or box near 0} ‖y‖^{−p} dy converges iff p < d.
Assume genericity of Z, Q_b throughout; assume ρ (=rank Z) ≥ u+b so that at generic z the relevant Grams are full rank. Write r_stack = rank[Q(z);Q_b] = u+b (generic), r_K = rank(Q(z)Π) = u (generic).
</setup>

<questions>
(1) As z → 0 (radially, z = δ·g for fixed generic g), determine the exponents: rank ρ₀ of the quadratic form f(z,·) at generic z; the number k of its eigenvalues that scale like δ² as z=δg→0; and hence the blow-up rate g(δg) ~ δ^{−P} with P = 2q − ρ₀ + k. Give ρ₀, k, and P in closed form in terms of u,a,b,q. (Hint: eigenvalues of the (u+b)×(u+b) Gram [Q;Q_b]-Gram split into b that stay O(1) and u that scale as δ²; the C-block Gram scales entirely as δ².)

(2) The coupled integral I: assuming the z→0 point degeneration dominates (the blow-up rate P is the same along all radial directions), state the exact finiteness condition I < ∞ in terms of P and N = u·m, and hence a condition on q, u, b, m.

(3) Validity of the crude bound: one might bound g(z) ≤ σ_min(L(z))^{−2q} · C₀ (σ_min = smallest singular value) and integrate that. But σ_min(L(z)) vanishes on the whole locus {rank[Q(z);Q_b] < u+b}, which for generic Z is a hypersurface (codim 1) in z-space, near which σ_min ~ dist. Show that ∫_z σ_min(L(z))^{−2q} dz then DIVERGES for 2q ≥ 1 (codim-1 locus), EVEN when the true coupled integral I converges. Conclude whether the crude σ_min bound is a valid route, and explain the discrepancy (why the true g(z) does NOT blow up on that codim-1 locus though σ_min does).

(4) For (3): at a generic point of the codim-1 locus {rank drops by exactly 1}, how many eigenvalues of f vanish (k'), and is the true local blow-up exponent P' = 2q − ρ₀ + k' positive or negative? Relate this to why g stays bounded there.
</questions>

<output_contract>
(1) closed forms ρ₀, k, P (expect P to simplify). (2) the I<∞ condition. (3) yes/no on the crude bound's validity + the mechanism of the discrepancy. (4) k' and the sign of P'. Concise, rigorous; flag any genericity assumption.
</output_contract>

<grounding_rules>
No files, no codebase — fully specified above. Distinguish proven vs assumed. If the "z→0 dominates" assumption in (2) needs a caveat (some intermediate-rank stratum could bind), say so and give the condition it would impose.
</grounding_rules>
