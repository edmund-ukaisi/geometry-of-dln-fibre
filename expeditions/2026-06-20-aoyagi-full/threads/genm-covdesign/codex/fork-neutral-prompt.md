<task>
A convergence question from an RLCT computation (deep linear nets). Derive the answer from scratch,
exactly — do not assume any particular peeling method; I want the intrinsic behaviour.

SETUP. `A_0` (m₀×m₁) and a tail product `P = A_1···A_{L-1}` (m₁×m_L), all entries in unit boxes.
Loss `frobSq(A_0 P) = ‖A_0 P‖²`. Define the per-tail integrand
    g(A') = ∫_{A_0 ∈ [-1,1]^{m₀×m₁}} frobSq(A_0 P)^{-c'} dA_0.
We integrate `∫_{A'} g(A') dA'` over the tail box and ask whether it is finite for `c' < ½·minAdm(M)`
(`minAdm` a known positive integer; `M=(m₀,…,m_L)`). The concern is the behaviour of `g(A')` as `A'`
approaches the locus where `rank P` drops to `q−1` (for the relevant corank `q`).

QUESTIONS (exact):
1. Fix `P` with rank exactly `q`, and let its smallest nonzero singular value `σ_q → 0` (so `P →` a
   rank-`(q−1)` matrix). How does `g(P)` scale — `g(P) ≍ σ_q^{−α}` for what `α`? Derive `α` exactly.
   (Hint: `frobSq(A_0 P) = ∑_i σ_i² ‖A_0 u_i‖²` over the singular directions `u_i`; the `A_0`-integral is
   over a BOX. Consider what the collapsing direction `σ_q → 0` contributes: is
   `∫_{[-1,1]}(σ_q² z² + w)^{-c'} dz` bounded as `σ_q → 0`, or does it blow up like `σ_q^{-1}`? — i.e.
   does the box keep that direction bounded, or would only a whole-space Gaussian blow up?)
2. Given `α`, the outer integral `∫_{A'} g` near `{rank P ≤ q−1}` converges iff `α < D`, where
   `D = codim{rank(tail product) ≤ q−1}` in tail-parameter space. Using the geometric fact
   `minAdm(M) ≤ D + m₀(q−1)` (from: `{rank P ≤ q−1} ∩ {A_0 kills the (q−1)-dim image} ⊆` the zero-product
   locus of the full chain, whose codim is `minAdm(M)`), determine whether `α < D` holds for all
   `c' < ½·minAdm(M)`.
3. VERDICT: is `∫_{A'} g(A')` finite near `{rank P = q−1}` for `c' < ½·minAdm(M)` — i.e. is the deeper
   stratum an INTRINSIC divergence, or is it integrable? If integrable, is the singularity a genuine
   obstruction requiring a global simultaneous resolution of all rank strata, or is it a LOCAL
   (bounded-domain, per-stratum) matter?
</task>

<output_contract>
- Exact `α` (the σ_q-exponent of `g`), with the box-vs-whole-space distinction made explicit.
- Whether `α < D` for `c' < ½minAdm`, using the `minAdm ≤ D + m₀(q−1)` inequality.
- Definitive VERDICT: the deeper stratum {rank=q−1} is (a) integrable/local — a per-stratum bounded
  matter — or (b) a genuine obstruction needing global simultaneous rank-flag resolution. Choose one.
</output_contract>

<grounding_rules>
Exact estimates. Make the box-vs-whole-space point precisely: is `∫_{[-1,1]}(σ²z²+w)^{-c'}dz` bounded as
`σ→0`? That single 1-D fact decides whether the collapsing direction contributes `O(1)` (box) or `σ^{-1}`
(whole space), hence whether `g` blows up mildly or catastrophically. Do NOT assume a peeling scheme;
compute `g`'s intrinsic scaling.
</grounding_rules>
