<task>
Adjudicate the SOUNDNESS of a two-brick decomposition of one Lean theorem into two isolated
`sorry`-bricks (F and D). You are a decorrelated second reviewer. I have NOT told you my conclusion;
adjudicate in either direction. Judge whether the two brick STATEMENTS are (i) each individually TRUE
and non-vacuous, and (ii) genuinely COMPOSE to a true parent theorem (not a pair that type-checks but
cannot both be filled). This is measure theory / linear algebra over real matrices; no code to run.

SETTING (deep-linear-network RLCT, per-shell domination). Widths M : Fin (L+3) → ℕ, all ≥ 1. Cut
u = t+j. Reduced chain redChain u M = (u, M₂, M₃, …, M_last) (DROPS M₁; position 0 = u). Tail chain
= (M₁, M₂, …, M_last). Deep factor Z_deep(z) = prod(dropHead(tailChain))(z-deep-layers): an M₂×n
matrix, M₂ = M 2, n = M_last. The head layer A'₀ is M₁×M₂; the full deep-tail product is
Z_full = A'₀ · Z_deep (an M₁×n matrix). a = M₀−u, b = M₁−u (corner block dims). ε' = ε/√(M₁·M₂).

weakEigCount δ W := # eigenvalues of W Wᵀ that are < δ². singularShell ε r j := { W | min(weakEigCount
ε W, r) = j }, r = min(M₀−t, M₁−t), j ∈ {0,…,r}. m := min(M₁,n) − j.

BRICK F (∀ measurable Zdeep : X → M₂×n matrices, m ≤ M₂, m ≤ n, ε' > 0): there exist measurable
Zf, U_sf with U_sfᵀU_sf = 1, rank(Zf z) ≥ m ∀z, Zf z (Zf z)ᵀ ⪰ ε'²·U_sf z (U_sf z)ᵀ ∀z (PSD floor),
and the AGREEMENT clause: ∀z, weakEigCount ε' (Zdeep z) ≤ M₂ − m → Zf z = Zdeep z.
Intended construction: on good set G = {z : weakEigCount ε' (Zdeep z) ≤ M₂−m}, set Zf=Zdeep and U_sf =
measurable m-frame of the ≥ε'²-eigenspace; off G, set Zf = fixed full-rank V (M₂×n, rank ≥ m,
V Vᵀ ⪰ ε'²·U_s0 U_s0ᵀ), U_sf = fixed orthonormal U_s0.

BRICK D (given F's frame data + gates hpiv, hcvg, hrange): there exist Ccrossf, sΓf, and FINITE C_hle
with shellSpineIntegrand(shell j) ≤ C_hle · coreIntegrand(k=[1], jc=[minAdm(redChain u M)−1], Zf,…).
The core RHS integrand, at each z, integrates over corner params a "corank weight"
∫_{A_cor} det((A_cor·Zf z)(A_cor·Zf z)ᵀ)^{−a/2} type term; the LHS spine integrand is the true DLN
per-shell integrand (using true Z_full = A'₀·Z_deep). Gates: hpiv : minAdm(redChain u M) ≤ u·ρ,
ρ = min(M₁,…,M_last); hcvg : a + b ≤ m; hrange : m ≤ M₂. D must internally (a) row-split A' ↔ (z,A_cor),
(b) reorganize the front layer via a P-radial blow-up giving pivot energy commonDivisor(v)²·frobSq(prod
(redChain u M) z) plus a finite reorganization constant, (c) use Ky-Fan σ_i(A'₀ Z_deep) ≤ σ_1(A'₀)
σ_i(Z_deep) with σ_1(A'₀) ≤ √(M₁M₂) on the box to show the shell ⊆ G, then invoke F's agreement clause
to replace Zf by Z_deep on the shell mass, then a banked PSD-monotone corank-weight bound.

QUESTIONS (answer each; label FACT vs INFERENCE):
Q1. Is F's statement TRUE and are its three ∀z conjuncts (rank ≥ m, PSD floor, agreement) jointly
satisfiable by the intended piecewise construction? Any hidden obstruction (e.g. measurable m-frame
selection when the ≥ε'² eigenspace dimension jumps)?
Q2. Is the agreement threshold "weakEigCount ε' Zdeep ≤ M₂ − m" the correct encoding of "≥ m singular
values of Zdeep are ≥ ε'" (i.e. z ∈ G), and does F's off-G branch make the agreement VACUOUSLY true
off G (so no conflict with the fixed V)?
Q3. On shell S_j with j < r (so weakEigCount ε Z_full = j exactly), does Ky-Fan + σ_1(A'₀) ≤ √(M₁M₂)
give weakEigCount ε' Z_deep ≤ M₂ − m (i.e. shell ⊆ G), for m = min(M₁,n) − j? Verify with the count
arithmetic (Z_full is M₁×n; # strong dirs = M₁ − j).
Q4. THE SATURATED SHELL j = r. Here weakEigCount ε Z_full ≥ r (could be > r), so the shell ⊆ G
containment can FAIL (e.g. Z_full = 0 at z = 0). Does this make D's statement FALSE at j = r (LHS
possibly divergent while RHS finite via the fake full-rank V off G)? OR is it saved because at j = r,
a = M₀−u = max(0,M₀−M₁) and b = M₁−u = max(0,M₁−M₀) so min(a,b) = 0 (empty corner / zero exponent),
making the corank weight trivially finite regardless of Z_deep's rank? Adjudicate whether min(a,b)=0
at j=r genuinely defuses the containment-failure concern.
Q5. Does the gate hpiv : minAdm(redChain u M) ≤ u·ρ (ρ = min(M₁,…,M_last)) correctly exclude the
witness M=(3,3,4,4), u=2 where the pivot-block absorbed integral is claimed to diverge
(minAdm(2,4,4)=7 > u·ρ = 2·3 = 6)? Is hpiv sufficient (not merely necessary) for C_hle < ⊤, including
at marginal equality u·ρ = minAdm (e.g. the equal-width anchor (3,3,3), u=2: 6 = 6)?
Q6. Do F and D genuinely COMPOSE: F's output tuple (Zf, U_sf, orthonormality, rank, floor, agreement)
is passed verbatim as D's frame hypotheses. Is there any way both bricks are individually true but the
composition still fails (a semantic gap the type-checker would not catch)?
</task>

<output_contract>
For each Q1–Q6: a one-line VERDICT (SOUND / DEFECT / UNCERTAIN) then ≤4 lines of reasoning. Then a
final HEADLINE: is the F+D decomposition CONTRACT-SOUND (both bricks true + genuine composition), or is
there a DEFECT (name it + the minimal repair). Label every claim FACT or INFERENCE.
</output_contract>

<grounding_rules>
Do not accept a claim because it "sounds standard" — check the count/dimension arithmetic explicitly
for Q3, Q4, Q5. Flag any place where you are inferring rather than deriving. If a question is
under-determined by what I gave, say so and state what extra fact would settle it.
</grounding_rules>
