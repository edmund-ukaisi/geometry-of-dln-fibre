<task>
Lean 4 + Mathlib design question. I need the Lean-friendly shape of a bounded-domain ("box") corank
integral atom that stays UNIFORM as a coupling matrix degenerates in rank — the replacement for a
full-space atom that blows up on rank-drop strata.

CONTEXT. There is a BANKED full-space atom (works only when `R` has full row rank):
    ∫_{Γ ∈ ℝ^{p×q}} (w + ‖Γ·R + S‖²)^{−c'} dΓ  =  det(R Rᵀ)^{−p/2} · Cresid(pq,c') · w^{−(c'−pq/2)}   (c'>pq/2),
`R : q×n`, `G = R Rᵀ` posdef. When `R` drops row rank (`det G → 0`), the `det(R Rᵀ)^{−p/2}` factor blows
up — this is a known wall (the atom is scoped to the full-rank slice). BUT the actual integration domain
for `Γ` is a BOX `[−T,T]^{p×q}` (bounded), not all of ℝ^{p×q}. The banked ISOTROPIC box atom is:
    ∫_{Γ ∈ box(p,q,T)} (frobSq Γ + w)^{−c'} dΓ  ≤  Cresid(pq,c') · w^{−(c'−pq/2)}   (c'>pq/2, UNIFORM in T).

KEY FACT (elementary, decides everything): for a collapsing direction with singular value `σ→0`,
    ∫_{−1}^{1} (σ² z² + w)^{−c'} dz  →  2·w^{−c'}   (BOUNDED as σ→0),
whereas the whole line gives `∫_ℝ (σ²z²+w)^{−c'}dz = σ^{−1}·const·w^{−(c'−1/2)}` (blows up). So the box
keeps a collapsing eigendirection at O(1); only the whole-space Gaussian blows up like σ^{−1}.

WHAT I NEED. State + give the Lean proof route for a BOX corank atom
    ∫_{Γ ∈ box(p,q,T)} (w + ‖Γ·R‖²)^{−c'} dΓ  ≤  (a bound UNIFORM as R → rank-deficient),
valid for ALL `R : q×n` (any rank r ≤ q), c' below the EFFECTIVE-rank threshold `p·r/2`. Specifically:
1. Diagonalise: `‖Γ·R‖² = ∑_{i=1}^q σ_i² ‖Γ·(right sing vec)_i‖²` (σ_i = singular values of R). Split the
   `q` singular directions into STIFF (σ_i ≥ δ) and SOFT (σ_i < δ). Over the BOX, what does each
   contribute — the stiff ones a Morse peel (charge p·#stiff), the soft ones an O(1) box-length factor?
2. The resulting bound should be `Cresid(p·r, c') · (∏_{stiff} σ_i)^{−p} · w^{−(c'−pr/2)}` with the SOFT
   directions contributing only bounded box factors — NO `det(R Rᵀ)^{−p/2}` full-Gram blow-up. Confirm
   the exponent and that it is uniform as the soft σ_i → 0.
3. Which Mathlib bricks: SVD / `Matrix` polar or the existing `RRᵀ` sqrt (`RouteMSJGramSqrt`), the box
   change of variables, `PiLp.volume_preserving_toLp`, the isotropic box endpoint. What is the cleanest
   Lean statement (opaque `p,q,n,r`) and proof skeleton? Is a full SVD needed, or does an orthonormal
   completion of `R`'s row space + the box-caps-soft-direction bound suffice (avoiding eigenvalue
   analysis)?
4. Integration: the outer variable is `A'` (the tail params), and `R = Q_b(A')` (a reduced tail product)
   varies with `A'`; the box atom's bound is then integrated over `A'`. The soft-σ / rank-drop locus is
   `{det(R Rᵀ) = 0} = {rank Q_b < q}`, codim `D` in `A'`-space. Convergence of `∫_{A'} (box bound)`
   near that locus needs the box exponent `< D`. Sketch how the box bound's `A'`-scaling (via the σ_i(A'))
   integrates against codim `D`.
</task>

<output_contract>
- The exact box corank atom statement (uniform as R rank-drops), the effective-rank threshold, the
  bound with NO det(RRᵀ) blow-up, and which singular directions are peeled vs box-bounded.
- The cleanest Lean shape + Mathlib brick list + proof skeleton (SVD vs orthonormal-completion).
- The A'-integration sketch: box bound integrated against the rank-drop codim D.
- Flag anything you are unsure of (esp. the opaque-width Lean feasibility).
</output_contract>

<grounding_rules>
Exact estimates. The decisive point is the box-vs-whole-space σ^{−1} fact — make the atom's proof route
rest on it (the soft direction bounded by the box), not on a full-Gram Jacobian. If a full SVD is Lean-
painful, propose the lightest sufficient decomposition.
</grounding_rules>
