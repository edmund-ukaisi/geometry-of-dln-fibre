<task>
An RLCT-finiteness proof (deep linear networks). I need ONE strategic fork resolved rigorously; do not
default to "it should work" — chase the exact estimate to a verdict.

SETUP. `P = A_1···A_{L-1}` (`m_1×m_L`, tail product), `A_0` is `m_0×m_1`. Loss `frobSq(A_0 P)=‖A_0 P‖²`,
all factors in unit boxes. Fix corank `q≥1`, pivot minor `(ρ,κ)`. We integrate over the pivot chart
`{det P[ρ,κ] ≠ 0}` (rank `P ≥ q` there) and want
`J = ∫_{chart}∫_{A_0 box} frobSq(A_0 P)^{-c'} dA_0 dA'` finite for `c' < ½·minAdm(M)`.

Available: the strong IH gives finiteness of the box integral of any chain of SMALLER TOTAL WIDTH `Σ`
(so induction on `Σ=∑m_i`), at its own threshold `½·minAdm(·)`. The `A_0`-Schur-peel gives (exactly):
`frobSq(A_0P) = ‖X̃ B‖² + ‖X̃ E + W Z‖²`, `B=P[ρ,κ]`, `Z=D−CB⁻¹E` the Schur complement, `X̃`=pivot cols of
`A_0` (sheared), `W`=non-pivot cols of `A_0`. The residual `W·Z = W·Y_1···Y_{L-1}` is the product of the
chain `(m_0, redTail)`, `redTail=(m_1−q,…,m_L−q)` — SAME arity as M, but smaller `Σ` (so IH-reachable).

THE FORK (resolve definitively):
Restrict to the DOMINANT-MINOR sub-chart `V = {(ρ,κ) is the LARGEST q×q minor of P}` (finite cover of
`{rank≥q}`). Peel the `X̃` (m_0 q-dim) Morse block by the whole-space bound
`∫_{ℝ^{m_0 q}}(x^⊤(I⊗S)x + w)^{-c'} dx = (det S)^{-m_0/2}·C·w^{-(c'-m_0q/2)}` (`c'>m_0q/2`),
`S=[B E][B E]^⊤` (q×q). Then the reduced budget `s=c'−m_0q/2` satisfies `s<½·minAdm(m_0,redTail)` (an ℕ
lemma that holds).

QUESTION A (does the positive route close?): On `V`, integrate `∫_V (det S)^{-m_0/2}·[∫_W ‖WZ‖^{-2s} dW] dA'`.
Analyse the behaviour as `A' → {rank P = q−1}` (the sub-chart boundary, where the LARGEST minor → 0, so
`det B → 0`). Compute the exact net power of `det B`:
  (i) `det S ≍ ?` in terms of `det B` on `V`;
  (ii) `Z = D − CB⁻¹E ≍ ?` as `det B → 0` (note `B⁻¹ = adj(B)/det B`, and `adj(B)` has rank 1 when `B`
       has rank `q−1`);
  (iii) `∫_W ‖WZ‖^{-2s} dW ≍ ?` power of `det B` (what is `rank(Z)` near the boundary?);
  (iv) the whole-space `(det S)^{-m_0/2}` bound vs the ACTUAL box `∫_{X̃ box}(‖X̃B‖²+w)^{-c'}dX̃` when `S`
       has a vanishing eigenvalue (one Morse direction goes flat) — is the whole-space bound LOSSY there,
       i.e. does it overestimate, and does the box integral instead behave like a corank-`(q−1)` peel
       (effective Morse charge `m_0(q−1)`, not `m_0 q`)?
Then: is `∫_V (net power of det B) dA'` FINITE for `c'<½minAdm(M)`, or does the whole-space-peel bound
DIVERGE near `{rank=q−1}` (while the true `J` is finite because `J ≤ ∫_{full box} = finite`)?

QUESTION B (if the whole-space peel diverges): does this mean the per-corank front-peel cannot close, and
one must resolve the rank strata `q, q−1, q−2, …` SIMULTANEOUSLY (a rank-flag / iterated blow-up
resolution, à la a full (S,J) recursion), rather than one corank at a time? State whether the deeper
stratum `{rank=q−1}` is a genuine obstruction to the one-corank reduction, and what the minimal fix is.
</task>

<output_contract>
Definitive verdict on the fork: EITHER (i) the dominant-minor sub-chart + whole-space peel CLOSES (give
the exact net-`det B` exponent and show `∫_V |det B|^{-θ}` converges for `c'<½minAdm`, with `θ<1`), OR
(ii) it does NOT (show `θ≥1`, identify the whole-space bound as lossy at `{rank=q−1}`, and state that a
simultaneous rank-flag resolution is required). Exact powers, no hand-waving. Distinguish "the METHOD's
bound diverges" from "the true integral diverges" (the true `J` is finite — `J ≤ full box integral`).
</output_contract>

<grounding_rules>
Exact estimates. If the whole-space Morse bound `(det S)^{-m_0/2}` is lossy because a Morse eigenvalue
vanishes at `{rank=q−1}`, say so and compute the ACTUAL box behaviour (the flat direction is bounded by
the box → effective lower corank). The key question is whether the one-corank reduction's UPPER BOUND is
finite, not whether `J` is finite (it is).
</grounding_rules>
