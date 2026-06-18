# Decorrelated review: θ-count bijection and integer-square equality case

I am auditing a Lean formalisation claiming the number of minimisers of an integer
quadratic program equals C(m, |δ|). Please reason about the MATH independently
(I do not need Lean — give me a pen-and-paper verdict). Hunt for a counterexample or
a gap; do not just agree.

## Setup

Fix integers m ≥ 1 and S ≥ 0. Define
  a = floor((2S + m) / (2m))   (Euclidean integer division, remainder in [0, 2m))
  δ = S − m·a.

Claim A (already believed): −m ≤ 2δ ≤ m−1, hence |δ| ≤ m.

We have a finite index set L of size m (call it "qipLow"). For a function
t : L → ℤ define the program: over all t with ∑_{i∈L} t_i = δ, minimise ∑_{i∈L} t_i².
The minimum value is |δ| (standard), attained.

## Crux 1 — Integer-square equality characterization

CLAIM: For ANY t : L → ℤ with ∑ t = δ and ∑ t² = |δ| (i.e. t attains the optimum),
  (i) every t_i ∈ {0, sign(δ)}, and
  (ii) exactly |δ| of the t_i are nonzero.

Proof sketch given: ∑(t²−|t|)=0 with each term ≥0 (since |x| ≤ x² for x∈ℤ) forces
each t_i² = |t_i|, so t_i ∈ {−1,0,1}. Let a' = #{t_i=1}, b' = #{t_i=−1}. Then
δ = a'−b' and |δ| = ∑|t_i| = a'+b'. So if δ>0 then b'=0 (all nonzeros are +1=sign δ),
if δ<0 then a'=0, if δ=0 then a'=b'=0. Nonzero count = a'+b' = |δ|.

QUESTIONS:
- Is this characterization correct for ALL three sign branches of δ, including δ=0
  (where sign(δ)=0 and the claim becomes "all t_i = 0")?
- Is there any t with ∑t=δ, ∑t²=|δ| that is NOT {0,sign δ}-valued? (counterexample hunt)
- Edge: does it rely on |δ| ≤ m? (i.e. could the "attained" hypothesis be vacuous if |δ|>m?)

## Crux 2 — Minimiser ↔ |δ|-subset bijection

The minimisers of the original QIP (call the feasible vectors e, with t_i = e-derived,
t : L → ℤ, ∑ t = δ at any minimiser) biject onto the |δ|-element subsets of L.

- FORWARD: minimiser e ↦ A_e := {i ∈ L : t_i ≠ 0}. By Crux 1, #A_e = |δ|.
- INVERSE: subset A (with A ⊆ L, #A = |δ|) ↦ e_A, where t-coordinate of e_A is
  [i ∈ A]·sign(δ) (so t_i = sign δ on A, 0 off A). This is feasible
  (∑ t = |δ|·sign δ = δ) and attains ∑ t² = |δ|.

CLAIM: these are mutually inverse.
- right inverse: A_{e_A} = A. Need: {i : t_i(e_A) ≠ 0} = A. Since t_i(e_A) = sign(δ)
  on A and 0 off A, this holds PROVIDED sign(δ) ≠ 0, i.e. δ ≠ 0. When δ=0, |δ|=0 so
  A=∅ and both sides are ∅ — does the argument still go through?
- left inverse: e_{A_e} = e. Need the e ↦ t map to be INJECTIVE on minimisers, i.e.
  recovering A_e = {t_i ≠ 0} and rebuilding gives back the same t, hence same e.
  This needs: at a minimiser, t_i is determined by whether t_i ≠ 0 (it equals sign δ
  when nonzero) — which is exactly Crux 1(i). And e is determined by t (the map
  e ↦ t is e_i = t_i + a − d_{i+1}, affine & injective). Off L, e_i = 0 both sides.

QUESTIONS:
- Is the δ=0 degenerate case handled (A=∅, unique minimiser, C(m,0)=1)?
- Is there a hidden assumption that the support A must be a PREFIX {0,...,|δ|−1}
  rather than an ARBITRARY |δ|-subset? The inverse e_A must be feasible & optimal for
  EVERY |δ|-subset A, not just the canonical prefix. Is that true? (i.e. does swapping
  which coordinates carry the sign-δ change feasibility or optimality?)
- Any failure mode where two distinct minimisers give the same support set, breaking
  injectivity?

Give a crisp verdict per crux: SOUND / BROKEN (+counterexample) / NEEDS-CAVEAT.
