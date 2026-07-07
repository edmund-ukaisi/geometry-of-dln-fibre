# Consult: Lean encoding of the SJState carrier + shared-divisor support map (DLN R1-UPPER)

You are a decorrelated design reviewer for a Lean 4 + Mathlib (v4.29) formalisation. I want a
red-team on ONE Lean encoding decision and ONE lemma statement. Exact-algebra + Lean-idiom review.
Do NOT re-litigate the underlying mathematics (it is separately adjudicated); focus on whether my
Lean encoding is FAITHFUL, NON-VACUOUS, and USABLE, and flag the sharpest risk.

## Background (the adjudicated math, taken as given)

We are proving finiteness of an integral `∫ frobSq(A0·Q)^{-c'}` (`c' < ½·minAdm`) via Aoyagi's
`(S,J)` normal-crossing resolution by a SEQUENCE of explicit single-radial blow-up charts (the "pure
R-BLOWUP" route — NOT the atom/Gram change-of-variables, which hits a res-of-sing wall). On each
terminal chart the loss becomes `∑_i b_i(u)²` where each `b_i` is a MONOMIAL in exceptional variables
`u_1,…,u_D`: `b_i(u) = ∏_ℓ |u_ℓ|^{e(i,ℓ)}`. Finiteness of `∫ (∑ b_i²)^{-c'}·(Jacobian ∏|u_ℓ|^{h_ℓ})`
is governed by the common monomial divisor `g = ∏_ℓ |u_ℓ|^{k_ℓ}`, `k_ℓ = min_i e(i,ℓ)`: factoring,
`∑ b_i² = g²·U`, `U ≥ 1` (one residual monomial is the chart's dehomogenised unit coordinate = 1), so
the integrand is `monomialIntegrand d k h c'·|U|^{-c'}`, integrable iff `c' < monomialThreshold d k h
= min_ℓ (h_ℓ+1)/(2 k_ℓ)`.

THE LOAD-BEARING DATUM (the adjudication's key correction): the map `e : Gen → Exc → ℕ` (which
exceptional `u_ℓ` divides which generator `b_i`, and to what order) is NECESSARY, not optional. Two
generators SHARING a divisor `u` give a different value than fresh-per-generator divisors:
`⟨δx, δy⟩` (shared δ, so `e = [[1,1,0],[1,0,1]]` over vars `[δ,x,y]`, `k_δ = min(1,1) = 1`) yields
`g = δ`, `∑b² = δ²(x²+y²)`, RLCT ½; whereas `⟨δ₁x, δ₂y⟩` (fresh, `k_{δ₁}=k_{δ₂}=0`) yields `g = 1`,
`∑b² = δ₁²x²+δ₂²y²`, RLCT 1. The `min_i` over the exponent matrix is exactly what separates them.

The banked Lean `monomialIntegrand d k h c u = (∏_j |u_j|^{h_j})·(∏_j |u_j|^{2 k_j})^{-c}` and
`monomialThreshold d k h` already exist and are consumed downstream.

## My proposed Lean encoding (the thing to red-team)

```lean
/-- The shared-divisor support map: exponent of exceptional var `ℓ` in generator `i`. -/
def SJSupport (numGen numExc : ℕ) := Fin numGen → Fin numExc → ℕ

/-- The common-divisor exponent of `u_ℓ`: `min_i e(i,ℓ)`. The `k` fed to `monomialIntegrand`. -/
def sharedDivisorExp {numGen numExc : ℕ} (e : SJSupport numGen numExc) (ℓ : Fin numExc) : ℕ :=
  ⨅ i, e i ℓ    -- Finset.inf' over the (nonempty) Fin numGen, or 0 if numGen = 0

/-- The generator monomial `b_i(u) = ∏_ℓ |u_ℓ|^{e(i,ℓ)}`. -/
def genMonomial {numGen numExc : ℕ} (e : SJSupport numGen numExc) (i : Fin numGen)
    (u : Fin numExc → ℝ) : ℝ := ∏ ℓ, |u ℓ| ^ (e i ℓ)

/-- The common divisor `g(u) = ∏_ℓ |u_ℓ|^{k_ℓ}`, `k_ℓ = sharedDivisorExp`. -/
def commonDivisor {numGen numExc : ℕ} (e : SJSupport numGen numExc) (u : Fin numExc → ℝ) : ℝ :=
  ∏ ℓ, |u ℓ| ^ (sharedDivisorExp e ℓ)
```

Target FACTORIZATION lemma (Phase 1 headline):

```lean
-- ∑_i b_i(u)² = g(u)² · (∑_i (b_i/g)²), with each b_i/g a genuine monomial (nonneg exponents).
theorem sumSq_genMonomial_eq_commonDivisor_sq_mul (e : SJSupport numGen numExc)
    (u : Fin numExc → ℝ) :
    (∑ i, (genMonomial e i u)^2)
      = (commonDivisor e u)^2 * (∑ i, (genMonomial (residualSupport e) i u)^2)
```
where `residualSupport e i ℓ = e i ℓ - sharedDivisorExp e ℓ` (nonneg since `k_ℓ ≤ e(i,ℓ)`).

## Questions (answer each; ≤ 250 words each)

1. **Is `e : Fin numGen → Fin numExc → ℕ` with `k_ℓ = ⨅_i e i ℓ` the RIGHT faithful minimal encoding
   of the shared-divisor support map?** Or is there a subtlety it misses (e.g. does faithfulness need
   more than the exponent matrix — the actual blow-up centres, the ORDER of blow-ups, sign data)? Is
   `min_i` (not, say, a per-pair gcd) the correct common-divisor operation for the `∑ b_i²` Newton
   polyhedron / `monomialThreshold`? The DATA-A `⟨δx,δy⟩` vs `⟨δ₁x,δ₂y⟩` distinction must come out
   right — confirm my `k` values (`k_δ=1` shared vs `k=0` fresh) are what the encoding produces.

2. **The factorization lemma.** `b_i(u) = ∏_ℓ|u_ℓ|^{e(i,ℓ)}`, `g = ∏_ℓ|u_ℓ|^{k_ℓ}`. Is
   `∑ b_i² = g²·∑(b_i/g)²` with `b_i/g = ∏_ℓ|u_ℓ|^{e(i,ℓ)-k_ℓ}` correct AND cleanly Lean-provable
   with `|u_ℓ|^{e} = |u_ℓ|^{k}·|u_ℓ|^{e-k}` (since `k ≤ e`, `pow_add`+`Nat.sub_add_cancel`)? Any trap
   when some `u_ℓ = 0` (then `|u_ℓ|^k` and `|u_ℓ|^{e-k}` factor fine for nat powers — confirm)?

3. **Connecting to `monomialIntegrand`.** With the residual sum `U = ∑(b_i/g)²`, the terminal
   integrand `(∑ b_i²)^{-c'}·(∏|u_ℓ|^{h_ℓ}) = (∏|u_ℓ|^{h_ℓ})·(∏|u_ℓ|^{2k_ℓ})^{-c'}·|U|^{-c'}
   = monomialIntegrand d k h c'·|U|^{-c'}` where `k = sharedDivisorExp e`. Is this identity exact
   (`(g²)^{-c'} = (∏|u_ℓ|^{k_ℓ})^{2·(-c')}` — watch `rpow`/`pow` and the `2k` vs `k` doubling)? Is
   the map `k_ℓ := sharedDivisorExp e ℓ` the correct `k` argument, i.e. is `commonDivisor² = ∏|u_ℓ|^{2k_ℓ}`?

4. **The relative chart lemma (Phase 2, the hardest bounded brick).** One `(S,J)` step: a single
   radial blow-up `Δ ↦ u•Δ` of the current corank block, plus a Z-independent unit block-elimination
   (banked: `frobSq_smul_mul`, `frobSq_schur_block_split`, `step3_blockFactor`). The NEW content is the
   LEDGER UPDATE: appending the fresh `u` to the support map and preserving the passive-prefactor
   invariant (earlier `u`'s multiply in, never divide). Given the pointwise `pref·frobSq((u•Δ)·Q) =
   (pref·u²)·residual` is already banked (`corankStep_prefactor`), what is the RIGHT shape for the
   ledger-update statement so it (a) stays faithful to "shared divisor across generators", (b) composes
   into a terminating recursion, (c) is provable? Flag the single sharpest risk in this step.

Answer concisely, question by question. If any encoding choice is WRONG, say so and give the fix.
