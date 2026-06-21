<task>
Lean 4 + Mathlib v4.29 formalisation design review. I am designing the cleanest Lean route for ONE
inequality and a final arithmetic assembly. Decide the cleaner of two routes; flag traps. Diagnosis is
what I want, not code.

CONTEXT (all the following are PROVED, sorry-free, in our `DLNFibre.Core`):

Setting: `k` an algebraically closed field, `d : Fin (N+1) → ℕ` a dimension vector, `M` a quiver
representation (a "tuple" of matrices `M_i : k^{d(i+1)} → k^{d i}`, i = 0..N-1). The coordinate ring
of the representation space is `R = MvPolynomial (RepCoord d) k` where `RepCoord d = Σ i:Fin N,
Fin(d(i+1)) × Fin(d i)` (one variable per matrix entry; finite index, `Fintype`).

Objects and landed facts:
- `Z_M = canonicalCoord '' orbitRankLocus M` = the orbit closure, a subset of points `RepCoord d → k`.
- `I = vanishingIdeal Z_M = vanishingIdeal (orbitSet M)` is PRIME (landed, `[IsAlgClosed k]`).
  `A = orbitRing M := R ⧸ I` is a finite-type domain over `k`.
- `m_M := normalFormIdeal M` is the maximal ideal of `A` at the k-rational point `M`; residue field
  `A ⧸ m_M ≃ₐ[k] k` (landed: `residueFieldNormalFormEquiv`).
- LANDED `isSmoothAt_normalFormIdeal : IsSmoothAt k m_M` (A is formally smooth at m_M).
- LANDED M3 `finrank_cotangentSpace_eq_of_isSmoothAt`: for finite-type A over alg-closed k, m maximal,
  IsSmoothAt k m, `ringKrullDim (AtPrime m) = n` ⟹ `finrank κ(m) (CotangentSpace (AtPrime m)) = n`.
- LANDED L4d `ringKrullDim_localizationAtPrime_isMaximal_eq`: for `A = MvPolynomial (Fin n) k ⧸ I`
  (I prime) and m maximal, `ringKrullDim (AtPrime m) = ringKrullDim A`. (Stated over `Fin n` index.)
- LANDED L0: `height (vanishingIdeal Z) + varietyDim Z = Nat.card(RepCoord d)` for prime vanishingIdeal,
  with `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`. `codimRep coord Z := height
  (vanishingIdeal (coord '' Z))`.
- LANDED L2a `finrank_cotangentSpace_eq_finrank_ker_jacobian`: for `R = MvPolynomial σ k` (σ Fintype),
  a FINITE generating family `g : Fin m → R` with `Ideal.span (Set.range g)` (NOTE: the ideal is the
  SPAN of g, the augmentation maximal ideal `maxIdealAt g a` is over `span (range g)`), `a` a k-rational
  point with `eval a (g i) = 0`, THEN `finrank k (CotangentSpace (AtPrime (maxIdealAt g a))) =
  finrank k (ker (jacobian g a))`. The jacobian is `v ↦ (∑_x eval a (∂(g i)/∂x) v_x)_i`.
- LANDED reusable intrinsic lemma `finrank_cotangentSpace_localization_eq_cotangent`: for ANY k-algebra
  A and ANY maximal ideal p, `finrank κ(p) (CotangentSpace (AtPrime p)) = finrank κ(p) (p.Cotangent)`
  where `p.Cotangent = p/p²` (Mathlib `Ideal.Cotangent`). This does NOT require a span-generated ideal.
- `deformationδ M M : C⁰ → C¹` is a k-linear map; `range δ⁰ := LinearMap.range (deformationδ M M)` is
  the orbit's tangent space at M; `finrank C¹ = finrank(range δ⁰) + finrank Ext¹` (rank-nullity, landed).
  `δ⁰ φ = (φ_{i+1} M_i − M_i φ_i)_i`. `C¹ = ∏_i Matrix(d(i+1), d i, k)`, `finrank C¹ = Σ_i d(i+1)·d(i)`.
- LANDED A4 (the OTHER inequality direction, conditional on 2 named obligations): `varietyDim Z_M ≤
  finrank(range δ⁰)` via transcendence degree of `(orbitPullback M).range` (the image of the orbit-map
  pullback μ_M^*).

WHAT I MUST DESIGN (A6):
(1) The REVERSE inequality `finrank k (range δ⁰) ≤ varietyDim Z_M`, then combined with A4 ⟹ equality.
(2) The final arithmetic assembly L7: `codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`
    where `orbitLinearCodim M = finrank C¹ − finrank(range δ⁰)`.

Two candidate routes for the cotangent comparison in (1):

ROUTE INTRINSIC: chain `finrank(range δ⁰) ≤ finrank(m_M.Cotangent) = finrank(CotangentSpace(AtPrime m_M))
[the landed intrinsic localization-collapse lemma] = ringKrullDim(AtPrime m_M) [M3+smooth] =
ringKrullDim A = varietyDim [L4d]`. The crux is `finrank(range δ⁰) ≤ finrank(m_M.Cotangent)`. Idea:
build a k-linear injection `range δ⁰ ↪ (m_M.Cotangent)^*` (dual), OR a surjection `m_M.Cotangent ↠
(range δ⁰)^*`, via the cotangent–tangent pairing: a tangent direction `δ⁰ φ` ("v ∈ T_M Z_M") pairs with
`f̄ ∈ m_M/m_M²` by the directional derivative `d f_M(v)`, well-defined on m_M/m_M² and vanishing for
`f ∈ I = vanishingIdeal Z_M` (since `f ∘ μ_M ≡ 0` so the directional derivative along an orbit direction
is 0). This uses NO minors and NO radical — only `vanishingIdeal Z_M` directly. Question: is the cleanest
Lean realisation a derivation/`Ideal.Cotangent`-pairing, or does it still want the Jacobian/`L2a`?

ROUTE MINORS+WRINKLE: use L2a with `g = rankMinorSet M` (the determinantal minors cutting out Z_M
SET-theoretically). Then `finrank(ker Jac) = finrank(CotangentSpace(AtPrime (maxIdealAt g M)))`. BUT
`Ideal.span (rankMinorSet M)` equals `vanishingIdeal Z_M` only up to RADICAL, so `maxIdealAt g M` (over
span g) need not have the same localization/cotangent as `m_M` (over vanishingIdeal Z_M). This needs a
"WRINKLE" sub-lemma: the two local rings / cotangent spaces agree at the smooth point M (guarded by
smoothness ⟹ reduced at M). And separately `range δ⁰ ⊆ ker Jac` (orbit directions kill the minors'
gradients).

KEY SUB-QUESTIONS (answer each explicitly):
Q1. Which route gives the cleaner / shorter Lean proof at Mathlib v4.29, and WHY? In particular: does
    ROUTE INTRINSIC genuinely AVOID the radical/WRINKLE issue entirely (so the A5 "local ideals agree"
    sub-lemma is never needed)? Or is there a hidden obstruction making the intrinsic cotangent pairing
    harder than the Jacobian?
Q2. For ROUTE INTRINSIC, what is the cleanest Mathlib bricks to build the map `range δ⁰ →
    (m_M.Cotangent)^*` or the directional-derivative pairing? Consider: `Ideal.Cotangent`,
    `Ideal.toCotangent`, `KaehlerDifferential`, `Derivation`, `MvPolynomial.pderiv`, the conormal
    `kerCotangentToTensor`. What is the well-definedness obligation (vanishing on `f ∈ I` and on `m²`)
    and how is it discharged from `f ∈ vanishingIdeal (orbitSet M)` (= `f` vanishes on every orbit point
    `canonicalCoord (P•M)`)?
Q3. The inequality direction: I need `finrank(range δ⁰) ≤ finrank(m_M.Cotangent)`. A pairing/injection
    `range δ⁰ ↪ (m_M.Cotangent)^*` gives `finrank(range δ⁰) ≤ finrank((m_M.Cotangent)^*) =
    finrank(m_M.Cotangent)` (finite dim). Is `finrank V^* = finrank V` clean here (need m_M.Cotangent
    finite-dimensional over κ=k)? Or is a surjection the better shape? Flag if injectivity of the
    pairing map is the hard part (it should require exactly that `range δ⁰` lands in the tangent space
    `(I-annihilator)`, with no nondegeneracy needed for ≤).
Q4. L7 final arithmetic: I have `codimRep = Nat.card(RepCoord) − varietyDim` [L0], `varietyDim =
    finrank(range δ⁰)` [squeeze], and need `= finrank C¹ − finrank(range δ⁰) = orbitLinearCodim`. So I
    need `Nat.card(RepCoord d) = finrank C¹` (both `= Σ_i d(i+1)·d(i)`) and the ℕ∞ ↔ ℕ casting to be
    lossless. Confirm the cleanest way to: (a) prove `Nat.card(RepCoord d) = finrank C¹`; (b) handle the
    ℕ∞ subtraction `card − varietyDim` matching the ℕ subtraction `finrank C¹ − finrank(range δ⁰)`
    losslessly (the additive forms `height + varietyDim = card` and `finrank(range δ⁰) + Ext¹ = C¹` are
    available). Any pitfalls with `ENat.toNat` / `WithBot ℕ∞` / `varietyDim`'s `unbotD 0`?
Q5. Hypotheses ledger: confirm whether the REVERSE inequality (1) needs `[CharZero k]` at all, or only
    `[IsAlgClosed k]`. (A4's forward inequality needs CharZero via a separability step. The reverse
    `range δ⁰ ⊆ tangent` direction is "orbit tangent ⊆ Zariski tangent" — should be char-free. If so,
    `[CharZero k]` enters hVoigt ONLY through A4, and A6's reverse module is char-free.)
Q6. L4d is stated over `MvPolynomial (Fin n) k ⧸ I`, but `A = orbitRing M = MvPolynomial (RepCoord d) k
    ⧸ I` (index `RepCoord d`, a Fintype not `Fin n`). Is there a transport obligation (reindex via
    `Fintype.equivFin` / `renameEquiv`) to apply L4d to our A? How heavy is it (note L0's
    `height_add_ringKrullDim_quotient_eq_card` already did exactly this reindex for height+dim)?
</task>

<output_contract>
For EACH of Q1–Q6: a short verdict (1–3 sentences) + the load-bearing reason. Then:
- ROUTE RECOMMENDATION: INTRINSIC or MINORS+WRINKLE, one paragraph why, and whether A5/WRINKLE is needed.
- The single hardest sub-lemma of the recommended route, and its kill-condition.
- Any trap I have not named (especially: a way the intrinsic pairing could be SUBTLY WRONG — e.g.
  finrank V^* ≠ finrank V in infinite dim, a missing finite-dimensionality, a κ(m)=k vs general residue
  field confusion, an ℕ∞ truncation that loses information).
Be concise and concrete. Mark every claim as (fact, from Mathlib I know) vs (inference, my judgement).
</output_contract>

<grounding_rules>
Do not invent Mathlib lemma names with confidence; if you are unsure a lemma exists at v4.29, say
"likely exists / check". Prefer naming the API family (`Ideal.Cotangent`, `Derivation`,
`Module.finrank_dual`, etc.) over a guessed exact signature. The landed facts above are given as true;
build on them. Distinguish your inferences from facts you are sure of.
</grounding_rules>
