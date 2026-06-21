# Decorrelated fidelity check: Zariski tangent = Jacobian kernel at a rational point

You are a commutative-algebra second opinion. Answer precisely and from first
principles; do NOT assume any particular formalisation is correct. Distinguish
what is a theorem (with hypotheses) from what is an inference/convention.

## Setup

Let `k` be a field (arbitrary — not assumed algebraically closed, not assumed
perfect, char arbitrary). Let `R = k[x_1, ..., x_n]` be a polynomial ring in
finitely many variables. Let `g_1, ..., g_m ∈ R` be a finite family, and
`I = (g_1, ..., g_m)` the ideal they generate. Let `A = R/I` (the coordinate
ring of the affine scheme `V(I)`). Let `a = (a_1,...,a_n) ∈ k^n` be a
**`k`-rational** point of `V(I)`, i.e. `g_i(a) = 0` for all `i`. Let
`m_a ⊂ A` be the maximal ideal of `A` corresponding to `a` (the kernel of the
evaluation/augmentation `A → k`, `f mod I ↦ f(a)`). Because `a` is `k`-rational,
the residue field `A/m_a = k`.

Form the Jacobian matrix `J = (∂g_i/∂x_j (a))_{i,j}` — an `m × n` matrix over
`k` (rows = generators, columns = variables). View it as a linear map
`J : k^n → k^m`.

## The questions

1. Is it a THEOREM that
      `dim_k ( (m_a/m_a^2) localized at m_a ) = dim_k ( ker J )` ?
   i.e. that the (local) Zariski cotangent-space dimension equals the dimension
   of the kernel of the Jacobian of the *given generators* evaluated at `a`.
   (Equivalently `dim_k(m_a/m_a^2) = n - rank J`, the cotangent space being the
   DUAL of the tangent space `ker J`, so the dimensions coincide.)

2. **What hypotheses does it need?** In particular:
   - Does it require `a` to be a *smooth*/regular point of `V(I)`? Or does it
     hold at singular points too?
   - Does it require `I` to be *radical* / `V(I)` *reduced*?
   - Does it require `k` algebraically closed or perfect?
   - Does it require the `g_i` to be a *minimal* / Gröbner / regular-sequence
     generating set, or does ANY finite generating family give the same
     `ker J` dimension?
   - Is `m × n` (more generators than variables, or fewer) an issue?

   I want a crisp verdict: is the dimension equality
   `dim_k(m_a/m_a^2 localized) = dim_k(ker J)` UNCONDITIONAL given only
   "`a` is a `k`-rational point of `V(I)`", or is some extra hypothesis
   (smoothness, radical, reduced, alg-closed, minimal generators) silently
   required for it to be TRUE?

3. Subtle point I want checked carefully: the Zariski cotangent space is usually
   defined as `m/m^2` where `m` is the maximal ideal of the LOCAL ring
   `O_{X,a} = A localized at m_a`. Is `dim_k` of that local `m/m^2` the same as
   `dim_k` of the *global* `(m_a / m_a^2)` computed in `A` itself? Under what
   conditions do these agree (residue field `= k`)?

4. The standard "conormal exact sequence" route: for `R ↠ A = R/I`, one has the
   right-exact sequence `I/I^2 → Ω_{R/k} ⊗_R A → Ω_{A/k} → 0`. Base-changing to
   the residue field `k = A/m_a` at the rational point, and using that the
   augmentation `A → k` splits (because `a` is rational), one identifies
   `m_a/m_a^2 ≅ k ⊗_A Ω_{A/k}` and the cotangent space as the cokernel of the
   transposed Jacobian `J^T : k^m → k^n`. Is this the correct/standard
   derivation, and is `dim coker(J^T) = n - rank(J^T) = n - rank(J) = dim ker(J)`
   the right bookkeeping? Is the splitting of the augmentation (rational point)
   genuinely WHAT makes `m_a/m_a^2 ≅ k ⊗_A Ω_{A/k}` hold unconditionally
   (i.e. without smoothness)?

Be explicit about any hidden hypothesis. If the equality is unconditional at a
rational point, say so and explain why no smoothness/radical assumption enters.
If it secretly needs one, give the minimal counterexample.
