<task>
A self-contained RLCT (real-log-canonical-threshold) stratification question: I have a coupled integral over an outer matrix variable z and inner variables x, of a power of a sum of two squared-norms whose coefficients depend bilinearly on z. I want the EXACT binding stratum (which degeneration locus of z governs convergence) and the resulting threshold. Do NOT read files; fully specified below.
</task>

<setup>
Real matrices. Fix generic Z (m×n, rank ρ ≥ u+b), and Q_b (b×n, full row rank b, with row(Q_b) ⊆ row(Z)). Π = I_n − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b (projection off row(Q_b)). Let d := rank(ZΠ) = ρ − b.
Outer variable z: u×m matrix, box [−1,1]^{um} (dim N = um).
Inner x = (P,B,C): P (u×u, invertible), B (u×b), C (a×u), bounded box.
Q(z) := z·Z (u×n). Loss:
   f(z,x) = frobSq([P|B]·[Q(z);Q_b]) + frobSq(C·Q(z)·Π).
Inner: g(z) = ∫_box f(z,x)^{−q} dx (q>0). Coupled: I = ∫_box g(z) dz.
At generic z the loss quadratic (in x) has rank ρ₀ = u·(u+b) + a·u = u(u+a+b) (b eigenvalue-groups from Q_b stay O(1); the u from Q(z) and the C-block ones scale as z→0).
</setup>

<facts-you-may-use>
- RLCT of a rank-ρ₀ PSD quadratic on a box = ρ₀/2; ∫_box (that form)^{−s} < ∞ iff s < ρ₀/2, and as one eigenvalue-block scales like δ², g(δ·) ~ δ^{−P} with P = 2q − ρ₀ + k (k = #eigenvalues that vanish), when P>0.
- The blow-up locus is where g(z)→∞. On a stratum of codim c in z-space where k eigenvalues vanish (rate δ² transverse), the coupled contribution ∫ dist^{−P}·dist^{c−1} d(dist) converges iff P < c.
- Determinantal codim: for a generic u×w matrix, {rank ≤ u−ℓ} has codim ℓ(w−u+ℓ).
</facts-you-may-use>

<questions>
(1) Two candidate deep loci where the loss fully degenerates (k = u(u+a) eigenvalues vanish, P = 2q−ub):
    (i) A := {z : z·Z·Π = 0}  — note on A, z·Z lands in row(Q_b) (generically ≠0), forcing rank[Q(z);Q_b]=b AND C·Q(z)·Π=0.
    (ii) B := {z : z·Z = 0}  — the smaller locus where Q(z)=0.
   Compute codim(A) and codim(B) in z-space (u×m). Confirm A ⊇ B. On A (generic point, z·Z ≠ 0 but z·Z·Π=0), verify that indeed k = u(u+a) eigenvalues vanish at rate δ² (u² from the [P|B]-block since rank[Q(z);Q_b] drops by u, and a·u from the C-block). 
   Which locus BINDS (gives the stronger/tighter convergence condition), given both have the same pole P=2q−ub but different codim? State the binding condition 2q < (codim of binder) + ub, simplified.
(2) Intermediate strata: for ℓ = 1..u, the rank-(u−ℓ) stratum of the relevant degeneration loses k_ℓ = ℓ(u+a) eigenvalues. Using the determinantal codim for the locus {rank(z·Z·Π) ≤ u−ℓ} (z·ZΠ is effectively u×d), i.e. c_ℓ = ℓ(d−u+ℓ), the condition is 2q − ρ₀ + k_ℓ < c_ℓ. Compute φ(ℓ) = ρ₀ − k_ℓ + c_ℓ and find min over ℓ∈{1..u}. Is the min at ℓ=u (the deep locus A), or at some interior ℓ? Give min_ℓ φ(ℓ) in closed form (cases on the sign of the parabola's vertex). Is the deep locus A always the binder, or can an intermediate ℓ bind tighter?
(3) Caveat check: the [P|B]-block degeneration is governed by rank(z·Z) (width ρ), while the C-block by rank(z·Z·Π) (width d=ρ−b). Do these give DIFFERENT stratifications that must both be checked? If the true k_ℓ / c_ℓ differ from the single-width assumption in (2), state the corrected φ(ℓ).
</questions>

<output_contract>
(1) codim(A), codim(B), which binds, the binding condition simplified (expect either 2q < uρ [if A, codim u(ρ−b)] or a tighter form). (2) min_ℓ φ(ℓ) closed form + whether ℓ=u binds. (3) whether the two widths (ρ vs d) force a two-parameter stratification + the corrected condition. Concise, rigorous; flag assumptions.
</output_contract>

<grounding_rules>
No files. Distinguish proven vs assumed. If the answer depends on a genericity/transversality assumption about how the [P|B]-block and C-block degenerations coincide, state it explicitly and give the condition each way.
</grounding_rules>
