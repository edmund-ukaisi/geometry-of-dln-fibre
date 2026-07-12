<task>
Two precise questions about a monomial-resolution carrier for an RLCT finiteness proof. Structural
reasoning only. DO NOT assume any "faithfulness" premise about the operations — derive what the
operations force.

## Objects (exact)
Generators `i` of a loss carry `gen_i(u,x) = (∏_ℓ |u_ℓ|^{supp(i,ℓ)}) · res_i(x)`, monomial in
exceptional coords `u`, times a LINEAR residual `res_i` in active variables `x`. Loss = `Σ_i gen_i²`.
Define `k_ℓ = min_i supp(i,ℓ)`, `commonDiv(u) = ∏_ℓ|u_ℓ|^{k_ℓ}`, and the per-generator LEFTOVER
`δ(i,ℓ) = supp(i,ℓ) − k_ℓ ≥ 0`. "UNIFORM support" means `δ ≡ 0` (every generator has `supp = k`).
Factoring: `loss = commonDiv(u)² · Σ_i ( (∏_ℓ|u_ℓ|^{δ(i,ℓ)}) · res_i(x) )²`.

## The three support-changing operations (exact semantics)
- RADIAL: prepend a fresh divisor dividing EVERY current generator to order 1 (`supp ↦ (1,…,1) ::: supp`).
  Preserves uniformity.
- ROW-MIX: replace the generators by linear combinations `res'_j = Σ_i R(j,i) res_i`, and SET the
  support to a chosen target `s'`. The rewrite `gen'_j = Σ_i R(j,i) gen_i` (monomial factors cleanly
  out of the combination) is VALID only when every old generator `i` with `R(j,i)≠0` has
  `supp(i) = s'(j)`. (If you mix generators of DIFFERENT support under one target, the identity fails
  — the combination is not a single monomial times a residual.)
- BLOCK-SPLIT: partition generators into a pivot set and a corank set; loss splits additively. No
  support change.

## The resolution (R-blow-up of a matrix-product loss)
Loss = `frobSq(A_0·A_1···A_{n-1})`. Each peel blows up the FRONT matrix only: `A_0 = u·V_0` (so the
radial `u` scales `A_0`, NOT the deeper factors `A_1,…`), splits `V_0` into a pivot core (rank t) and
a freed corank block `Γ` (dimension (M_0−t)(M_1−t)), yielding
`loss = u²·[ frobSq(pivotcore·A_1···) + frobSq(Γ·A_1···) ]`, then recurses on the reduced chain
`(t, M_2, …)` whose front matrix is `B = pivotcore·A_1`. The FREED corank term `frobSq(Γ·A_1···)` is
integrated at THIS peel (a separate finiteness lemma exists for it). At width-2 (a single matrix, no
deeper factors) no further blow-up is needed. There is also a genuine linear-algebra fact: the
residuals of the width-2 base read all M_0·M_1 entries of the single matrix (so they SPAN the full
M_0×M_1 block).

<questions>
State FACT vs JUDGEMENT throughout.
1. For the clean lower bound `loss ≥ commonDiv(u)² · frobSq(free block of dim M_0·M_1)` to hold at
   the width-2 base, is it ENOUGH that the residuals SPAN the M_0·M_1 block (a linear-algebra fact),
   or is UNIFORM SUPPORT `δ≡0` (equivalently: a spanning SUBSET of generators all with δ=0) ALSO
   required? Concretely: if the base generators span but a strict subset carries `δ>0` (a genuine
   `|u_ℓ|^{δ}` prefix), does dropping the δ>0 generators (they are ≥0) still leave a spanning
   δ=0 block, or can it lose rank? Give the decisive condition.
2. Consider the SUPPORT (the `supp`/`δ` data, NOT the residuals). Across the recursion, is the
   support of the STABLE carrier handed between peels (after each freed corank is integrated out)
   necessarily UNIFORM (`δ≡0`), or can/must a peel produce NON-uniform support? Reason from: (a) the
   radial scales only the front matrix, so a corank freed at peel j does NOT acquire peel-(j+1)'s
   radial — what does this force about whether a freed corank may be RETAINED as a generator through
   a later radial? (b) the row-mix identity is valid only when mixing same-support generators — does
   the R-blow-up ever need to mix different-support generators under one target? Conclude whether
   `δ≡0` on the stable carrier is (i) forced by the operations, (ii) achievable but a genuine
   obligation on how the peel is wired, or (iii) impossible / anisotropy unavoidable.
3. Distinguish two possible "anisotropies": (A) the RESIDUAL reads `Γ·Q` (a freed block times a
   deeper, rank-varying matrix `Q`) — a fact about `res_i` as linear forms; (B) the SUPPORT `δ` is
   non-uniform — a fact about the `u`-exponents. Are these independent? I.e., can a carrier have
   residual structure (A) present (`res = Γ·Q`) while support (B) is uniform (`δ≡0`)?
</questions>
</task>

<output_contract>
Three numbered answers, each 3-6 sentences, FACT/JUDGEMENT tagged. End with two one-line verdicts:
"CLEAN-BOUND NEEDS:" (span-only | uniform-support-too) and "STABLE-SUPPORT:" (forced-uniform |
obligation-on-peel | unavoidably-anisotropic). Be decisive; name the deciding property.
</output_contract>

<grounding_rules>
Ground in the operation semantics + the R-blow-up structure given. RLCT fact permitted: for a free
block of dimension N, `∫ frobSq(block)^{−c'} < ∞ ⟺ c' < N/2`. Do not assume operations are applied
"faithfully"; derive constraints from the stated validity conditions.
</grounding_rules>
