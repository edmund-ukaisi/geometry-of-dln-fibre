# genm-subred — the submersion-reduction interface (ii): clean, or hidden content?

**Seat:** pen-and-paper (obstruction — adjudicating one truth-value, adversarially). **Task:** is
interface (ii) — the reduction of the DLN corank-Gram obligation `∫_{A'} det(Q_b Q_bᵀ)^{−a/2}`
(`Q_b = Y·A_{≥2}`) to the abstract free-`Q`-box core (`∫ det(QQᵀ)^{−a/2} < ⊤ ⟺ a < q−b+1`) — a CLEAN
composition `[Q-box core] ∘ [reduced-chain IH]` via a benign Jacobian `J(A_{≥2})`, or does `J` hide a
determinantal weight that recurses / walls? **NO Lean.** **Exact algebra:**
`codex/subred_{jacobian,threshold,recursion,exact,scan,rank}.py` (sympy residual-0 + SVD + threshold
scan). **Decorrelated:** `codex/subred-{prompt,answer}.md` (gpt-5.x, xhigh; my conclusion WITHHELD —
open-ended "compute `J`, is the outer integral clean, what is the exact threshold". It independently
produced the exact `J` in all three regimes, the `min(m,q)−b+1` threshold WITH a Gaussian/Bartlett
PROOF, the `(2,2,3)` Cauchy–Binet factorization, and the domain-shrinking cancellation).

---

## VERDICT: **HIDDEN-CONTENT.** `J` is a genuine determinantal weight; the composite threshold is `min(tail widths)−b+1`, NOT `q−b+1`; interface (ii) recurses into the operator-gated atom, one chain-length deeper.

Interface (ii) is **not** a clean reduction to `[free-Q-box core (a<q−b+1)] ∘ [loss-side reduced-chain
IH]`. Three exact facts, in order of load-bearing weight:

1. **The Jacobian is `J(A_{≥2}) = det⁺(A_{≥2}ᵀA_{≥2})^{−b/2}` (a corank-Gram weight), NOT a bounded
   unit.** Exact in all three shape regimes (residual-0 square, SVD general); it **blows up on the
   rank-deficient locus** `{rank A_{≥2} < min(M₂,q)}`.

2. **The proposed factorization `∫_{A_{≥2}} [free-core · J]` is not even a valid decomposition.** The
   free-core's `Q`-domain is the image `A_{≥2}·(Y-box)`, which **shrinks as `A_{≥2}` degenerates**, and
   the shrinking exactly cancels `J`'s blow-up. Pulling the core out as an `A_{≥2}`-independent constant
   gives the wrong answer already at `a=0` (Codex's `b=m=q=1` check).

3. **The true threshold is `a < min(M₂,…,M_last) − b + 1` — the MIN TAIL WIDTH, not `q=M_last`.** It is
   **strictly below** the free-`Q` value `q−b+1` exactly when an intermediate tail width is `< M_last`
   (the *twist* / product-lowering). The composite `∫ det(Q_b Q_bᵀ)^{−a/2} d(Y,A_{≥2})` **is** the
   corank-Gram integral of the shorter chain `(b, M₂, …, M_last)`, and it **recurses one chain-length
   deeper** into the operator-gated `(S,J)` product-rank-flag determinantal atom — NOT the loss-side
   reduced-chain IH (`redChain = (t, M₂,…,M_L)`, leading dim `t`, loss `frobSq`, a different object).

**This is not a wall to the RESULT** (RLCT `= ½·minAdm(M)` is true, cited Aoyagi, MC-confirmed
elsewhere) — the lowered threshold `min(tail)−b+1` is exactly the correct per-chart budget and is
consistent with the global `½·minAdm`. It is a wall to the **clean "free-core ∘ loss-IH" reduction**:
interface (ii) carries the recursive determinantal machinery, precisely the deeper-tail regeneration
the corner (`crnrt`) and twist-lemma (`deepstrat`) already exhibit one level up. It also **sharpens and
partly corrects `wtint`** (below).

---

## `J(A_{≥2})` computed exactly (Q1)

`Y : b×M₂`, `A_{≥2} = A₂⋯A_L : M₂×q`, `Q_b = Y·A_{≥2} : b×q`. The map `Y ↦ Y·A_{≥2}` is `b` copies of
`ℝ^{M₂} → ℝ^q`, `v ↦ v·A_{≥2}`. Let `r = rank(A_{≥2})`, singular values `σ₁,…,σ_r`. The forward
`br`-Jacobian is `(∏σ_i)^b = det⁺(A_{≥2}A_{≥2}ᵀ)^{b/2} = det⁺(A_{≥2}ᵀA_{≥2})^{b/2}`, so

> `J(A_{≥2}) = (∏σ_i)^{−b}`, i.e. `= |det A_{≥2}|^{−b}` (square `M₂=q`), `= det(A_{≥2}A_{≥2}ᵀ)^{−b/2}`
> (`M₂ ≤ q`), `= det(A_{≥2}ᵀA_{≥2})^{−b/2}` (`M₂ ≥ q`).

Verified residual-0 for the square case `(b,m,q) ∈ {(1,1,1),(1,2,2),(2,2,2),(2,3,3),(3,2,2)}`
(`subred_jacobian.py` Step 1: `dQ/dY det − det(A)^b = 0`), and by SVD for the non-square regimes
(`prod nonzero σ = √det⁺(Gram)`, `subred_jacobian.py` Step 2). **`J` is bounded only on charts
separated from `{rank A_{≥2} < min(M₂,q)}`; it is unbounded across that locus.** The full coarea
identity carries, besides `J`, an image/fiber factor (a moving `bM₂`-plane for `M₂<q`; a fiber-section
volume `V_{A,B_Y}(Q)` for `M₂>q`) — so `J` is *not* the whole transformed density (Codex Q1, verbatim).

---

## Not benign — the outer integral does not fold into the loss IH (Q2, the CRUX)

**`J` is a determinantal integral in its own right, and it is not what the loss-side IH covers.** As a
standalone function of a free `M₂×q` matrix, `∫ J dA_{≥2} < ⊤ ⟺ b < |M₂−q|+1`. But the *original*
`I(a)` is finite well past that, because the free-core's domain shrinks as `A_{≥2}` degenerates and
cancels `J`'s singularity — so the naive `[core]×[J]` split is invalid (Codex Q2; `b=m=q=1`:
`|t|^{−1}·∫_{−|t|}^{|t|}|Q|^{−a}dQ = 2|t|^{−a}/(1−a)`, the `|t|^{−1}` cancelled by the shrinking
interval).

The honest object: `I(a) = ∫ det(Q_b Q_bᵀ)^{−a/2} d(Y,A_{≥2})` **is the corank-Gram zero-product
integral of the composite chain `𝒞 = (b, M₂, M₃, …, M_last)`**. When `A_{≥2} = A₂⋯A_L` is itself a
product, `J = det⁺(Gram A_{≥2})^{−b/2}` is the SAME determinantal problem for the shorter product
`A₂⋯A_L` at exponent `b` — an exact **algebraic recursion**, one layer deeper (Codex Q2). This is the
operator-gated `(S,J)` product-rank-flag recursion (the deeper-tail regeneration, analogue of
`crnrt`'s corner and `deepstrat`'s twist), **not** the arity/loss-side reduced-chain IH
`RouteMBoxThresholdFinite (redChain t M)` — that IH is about the pivot chain `(t, M₂,…,M_L)` and the
loss `frobSq(B₀)`, a disjoint obligation (as `wtint` already established for the top stratum).

---

## The composite threshold is the min TAIL width — the twist (Q3)

For `b ≤ min(M₂,q)`, over a singularity-containing box:

> **`I(a) < ⊤ ⟺ a < min(M₂, …, M_last) − b + 1`.** (`= q−b+1` iff the tail does not contract below its
> last width; strictly smaller otherwise.)

- **Exact witnesses (no MC):**
  - `(b,M₂,q)=(1,1,2)`: `det(Q_bQ_bᵀ) = y²(a₁²+a₂²)`, so `det^{−a/2} = |y|^{−a}·(a₁²+a₂²)^{−a/2}`;
    `∫|y|^{−a}` needs `a<1`, `∫(a₁²+a₂²)^{−a/2}` needs `a<2` — **`a_c = 1`**, whereas free `q−b+1 = 2`.
    The narrow inner width `M₂=1` caps it (`subred_exact.py`, Codex Q3). Smallest twist witness.
  - `(2,2,3)`: Cauchy–Binet `det(Q_bQ_bᵀ) = det(Y)²·det(A_{≥2}A_{≥2}ᵀ)` (residual-0), factoring into
    `∫|det Y|^{−a}` (threshold 1) × free-`(2,3)` core (threshold 2) ⟹ **`a_c = 1`**, below free `2`.
  - 3-layer `(1,1,2,2)` / `(1,2,1,2)`: `a_c = 1` (a narrow *internal* width, not `M_last`, sets it;
    `subred_exact.py`, `subred_recursion.py`).
- **Decorrelated PROOF (Codex Q3):** Gaussian/Bartlett — `𝔼 det(Y A_{≥2}A_{≥2}ᵀ Yᵀ)^{−a/2} =
  M_{b,M₂}(a)·M_{b,q}(a)`, each factor finite `⟺ a < (dim)−b+1`; deep product `⟹ a < min_j(d_j−b+1)`.
  Plus the local model `det(XXᵀ) = u·‖z‖²`, `z∈ℝ^{n−b+1}`, `∫r^{n−b−a}dr` finite `⟺ a<n−b+1`.
- **MC scan** (`subred_scan.py`, guide only, calibrated on the free case): threshold tracks
  `min(M₂,q)−b+1` uniformly across 13 shapes — `m<q` cases strictly below free (e.g. `(1,1,3)→1` vs
  free 3, `(2,2,4)→1` vs free 3), `m≥q` cases equal free.

`minAdm`/RLCT identification (level separation): the load-bearing facts above are the *integrability
threshold* of the emitted weight, `= min(tail)−b+1`. Pinning that exactly to `½·minAdm(𝒞)` / the RLCT
of chain `𝒞` is the deeper-tail determinantal-resolution content (consistent with `crnrt`/`deepstrat`),
which this thread does not re-derive — I certify the threshold, not the full RLCT-`=½·codim` reading.

---

## The rank-deficient locus of `A_{≥2}` is NOT negligible (Q3)

- **`M₂ ≥ q`:** `{rank A_{≥2} < q}` is Lebesgue-null and imposes no extra threshold restriction (the
  divergence at `a = q−b+1` already occurs on an open set of full-rank `A_{≥2}`). BUT `J` genuinely
  blows up there, so it cannot be discarded in the change of variables — `J`'s blow-up must be paired
  with the shrinking image (only the product has analytic meaning). Handling it is the **dominant-minor
  cover of `A_{≥2}`** (`J` a unit on-chart) + the deeper recursion off-chart.
- **`b ≤ M₂ < q`:** the rank cap `rank A_{≥2} = M₂ < q` is **generic, not null** — this is the
  mechanism lowering the threshold to `M₂−b+1` (the effective core is `b×M₂`, not `b×q`). The further
  locus `{rank A_{≥2} < M₂}` is a deeper stratum, non-binding relative to `M₂−b+1`.
- **Deeper product with an internal width `< min(M₂,q)`:** `rank A_{≥2} < min(M₂,q)` becomes **generic**
  — the full-rank Jacobian formula is inapplicable and the narrow internal width enters the deep
  threshold `min_j(d_j−b+1)` (Codex Q4). The recursion is genuinely load-bearing here.

---

## Sharpening / correction of `wtint`

`wtint` asserted "`Y ↦ Y·A_{≥2}` is a submersion where `A_{≥2}` has rank `≥ b`, so the determinantal
variety pulls back with the **same codimension `q−b+1`**". **This over-claims exactly when `M₂ < q`**
(parallel to `wtint`'s Cat I over-claim that `catint` caught):

- `rank A_{≥2} ≥ b` (⟺ `Q_b` *can* reach full rank `b`) is **not** the submersion condition. A
  submersion onto `ℝ^{b×q}` needs `rank A_{≥2} = q` (⟺ `M₂ ≥ q`). For `b ≤ M₂ < q` the image is the
  `bM₂`-dim moving subspace `(row A_{≥2})^b ⊊ ℝ^{b×q}` — NOT onto.
- The correct pullback / good-stratum codimension is `rank(A_{≥2}) − b + 1 = min(M₂,…,M_last) − b + 1`
  (the rank of the *product* tail is the min width), `= q−b+1` **only** for a non-contracting tail.
- Consequently the Cat-I boundary (`wtint`/peelcert §B=2 COVER `a+b ≤ q`) should read **`a+b ≤
  min(M₂,…,M_last)`** — the min tail width, not `M_last`. `wtint`'s WALL (the Gram weight is an
  independent, non-absorbable obligation) **stands and is reinforced**; only its "same codim `q−b+1`"
  quantifier is wrong for contracting tails.

---

## Codex decorrelated read (my conclusion withheld — quoted)

> **Q2:** "No. … As a standalone function of a free `m×q` matrix, `J(A)` is itself a determinantal
> integral. … In particular, for `m=q`, `J=|det A|^{−b}` is never locally integrable for a positive
> integer `b`. Nevertheless the original integral can be finite because the transformed `Q`-domain
> shrinks. … Replacing that interval with a fixed 'free core' would give the wrong answer even at
> `a=0`." … "`J(A_tail) = det(A_tail A_tailᵀ)^{−b/2}` … is the same problem for the shorter product
> `A₂⋯A_L`, with new exponent `a′=b`. … It is not by itself a recursion for `I(a)`, because the
> image/fiber factors must be retained."
>
> **Q3:** "`I(a)<∞ ⟺ a < min(m,q)−b+1`. … The free `b×q` threshold survives exactly when `m≥q`. A
> narrower intermediate dimension lowers it." (proven via Bartlett: `𝔼 det(XXᵀ)^{−a/2}` finite `⟺
> a<n−b+1`, product `⟹ a<min_j(d_j−b+1)`.) `(2,2,3)`: "`det(QQᵀ)=det(Y)²det(AAᵀ)` … `a_c=1`, again
> below the free value 2."
>
> **Q4:** "For `m<q` … the loss also occurs for `A` bounded away from rank deficiency; it is caused by
> the effective `b×m` core, not by the null rank-drop locus. … If `A_tail` is a deeper product with an
> internal width below `min(m,q)`, then `rank A_tail < min(m,q)` is generic rather than null."

Fully decorrelated agreement (and at PROVEN level via Gaussian/Bartlett): the exact `J`, the
non-benign / invalid-factorization verdict, the `min(m,q)−b+1` threshold, the twist below free for
`m<q`, the standalone-`J` recursion, and the rank-deficient-locus reading.

---

## CLOSE

- **Firmest.** Interface (ii) is HIDDEN-CONTENT. `J(A_{≥2}) = det⁺(Gram A_{≥2})^{−b/2}` (exact,
  residual-0 / SVD), unbounded at `{rank A_{≥2} < min(M₂,q)}`, is a corank-Gram weight — not a benign
  factor, and the proposed `∫_A[free-core·J]` is an invalid factorization (the core's domain shrinks
  with `A` and cancels `J`). The composite is the corank-Gram integral of the shorter chain
  `(b,M₂,…,M_last)` with threshold **`a < min(M₂,…,M_last)−b+1`** (Gaussian/Bartlett PROOF + exact
  `(1,1,2)`, `(2,2,3)` witnesses), **strictly below** the free-`Q` `q−b+1` whenever the tail contracts
  (the twist). It recurses one chain-length deeper into the operator-gated `(S,J)` atom, not the
  loss-side IH. Sharpens `wtint`: good-stratum codim `= min(tail)−b+1`, Cat-I boundary `a+b ≤ min(tail)`.
- **Most likely to break / watch.** The threshold I certified is the *integrability of the emitted
  weight* (`= min(tail)−b+1`), NOT the full RLCT-`=½·codim` of chain `𝒞` — pinning it to `½·minAdm(𝒞)`
  is the deeper determinantal resolution (the `deepstrat`/`crnrt` twist-and-resolve content), not
  supplied here. A formaliser who routes interface (ii) through the free-`Q` core at `a<q−b+1` will
  **over-estimate the budget on any contracting-tail chart** (`M₂<M_last`) and the `½·minAdm(M)` headline
  silently fails there — the exact analogue of `crnrt`'s Trap W2 (free-leaf overestimate) and `catint`'s
  `q>b` gap.
- **Next.** (1) Formaliser: do NOT wire interface (ii) as `[free-Q core]∘[loss IH]`. Wire it as the
  dominant-minor cover of `A_{≥2}` (`J` = unit on-chart, free-core over the **rank `min(M₂,q)`** image,
  threshold `min(M₂,q)−b+1`) + the deeper corank-Gram recursion off-chart (the operator-gated atom,
  task #111). (2) The min-tail-width threshold `min(M₂,…,M_last)−b+1` is the new ℕ-lemma; front-load a
  contracting-tail chart (`M₂<M_last`, e.g. tail `(1,2)` giving `(b,1,2)`) so the twist is exercised, not
  a balanced case that hides it. (3) A reviewer on whether the DLN driver's actual `(t,ρ,κ)` charts ever
  present a contracting tail at the binding cut — if yes (permutation-invariance says the widths can be
  in any order, so yes), the twist is load-bearing, not a rare edge.
