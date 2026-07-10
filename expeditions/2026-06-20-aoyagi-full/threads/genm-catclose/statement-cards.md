# genm-catclose — statement cards (Cat I good-stratum integrability)

Branch `genm-catclose-work` (off `origin/genm-catclose` @ `15927462`). Files uncommitted at
authoring time; controller pins the integration SHA.

The Cat I obligation is: the good-stratum weight integral `∫_{det(Q_b Q_bᵀ)>0} det(Q_b Q_bᵀ)^{−a/2}`
is finite when `a < q−b+1` (Cat I `a+b ≤ q`, i.e. `a ≤ q−b < q−b+1`). The route (catint cert) is the
Gram–Schur radial model `det(Q_b Q_bᵀ) = det(G_{b−1})·‖z‖²` recursed on `b`, with the `n`-dim radial
integrability `∫_{ball} ‖x‖^{−a} < ∞ ⟺ a < n` as the load-bearing recurring sub-lemma. This card
covers the bricks LANDED so far; the remaining pieces (P3-residual, P2, P4) are itemised at the end.

---

## Card 1 — radial integrability over a ball (the load-bearing sub-lemma)

> **Claim.** On `ℝ^n` (`n ≥ 1`), `x ↦ ‖x‖^{−a}` is (Lebesgue) integrable on any ball `ball 0 R`
> when `a < n`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.integrableOn_norm_rpow_neg_ball`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJRadialInt.lean`)
>   `{n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : a < n) (R : ℝ) : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖ ^ (-a)) (Metric.ball 0 R)`
> - **Gloss.** For the Euclidean space `ℝ^n` with `n ≥ 1`, if the real exponent `a` is `< n`, the
>   function `x ↦ ‖x‖^{−a}` (Real.rpow; Euclidean norm) is integrable on the open ball of radius `R`
>   (any `R`; empty when `R ≤ 0`).
> - **Proved.** The `⟸` (`a < n ⟹ integrable`), the finiteness we need, over the ball. Via Mathlib's
>   coarea reduction `integrable_fun_norm_addHaar` (radial ⟺ 1-D weighted power `∫_{Ioi 0} y^{n−1}·f`)
>   + `intervalIntegral.integrableOn_Ioo_rpow_iff` (near-0 power `∫_0^R y^s ⟺ −1 < s`; here
>   `s = (n−1)−a`, so the test is `a < n`).
> - **Assumed.** none (`n ≥ 1`, `a < n` are the stated hypotheses).
> - **Cited.** none (all Mathlib).
> - **Deferred.** the `⟹` (necessity) is not stated — not needed for finiteness.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

## Card 2 — `∫⁻`-finiteness corollary (the shape the recursion consumes)

> **Claim.** `∫⁻ x in ball 0 R, ofReal(‖x‖^{−a}) < ⊤` when `a < n`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.lintegral_norm_rpow_neg_ball_lt_top` (same file)
>   `{n} (hn : 1 ≤ n) {a} (ha : a < n) (R) : (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (‖x‖ ^ (-a))) < ⊤`
> - **Gloss.** The ENNReal lower-integral of `ofReal(‖x‖^{−a})` over the ball is finite for `a < n`.
> - **Proved.** Immediate from Card 1 via `IntegrableOn.setLIntegral_lt_top`.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free; clean-three.

## Card 3 — Gram Schur-complement determinant recursion (P3, algebraic backbone)

> **Claim.** Appending a row `w` to a matrix `A` whose Gram `A Aᵀ` is invertible multiplies the Gram
> determinant by the Schur-complement scalar `‖w‖² − (A·w)ᵀ (A Aᵀ)⁻¹ (A·w)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.det_gram_row_snoc`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGramSchur.lean`)
>   `{n q} (A : Matrix (Fin n) (Fin q) ℝ) (w : Fin q → ℝ) [Invertible (A * Aᵀ)] : (Matrix.of (Sum.elim A (fun _ : Unit => w)) * (Matrix.of (Sum.elim A (fun _ : Unit => w)))ᵀ).det = (A * Aᵀ).det * (w ⬝ᵥ w - (A *ᵥ w) ⬝ᵥ (⅟(A * Aᵀ) *ᵥ (A *ᵥ w)))`
>   (supported by `gram_row_snoc_eq_fromBlocks`, the block form of the Gram).
> - **Gloss.** `Q` is `A` with the extra row `w` (`Sum.elim` over `Fin n ⊕ Unit`). Then `det(Q Qᵀ) =
>   det(A Aᵀ) · (⟨w,w⟩ − ⟨A·w, (A Aᵀ)⁻¹ (A·w)⟩)`, via `Matrix.det_fromBlocks₁₁` (Schur complement).
> - **Proved.** The pure-matrix determinant identity (algebraic Schur complement), any `A`, `w`, with
>   `A Aᵀ` invertible.
> - **Assumed.** `[Invertible (A * Aᵀ)]` (the top-left Gram block invertible — the good-stratum case
>   `rank A = n`; the degenerate case is a separate branch, see Deferred).
> - **Cited.** none (all Mathlib).
> - **Deferred (the geometric identification, next brick).** the Schur scalar
>   `‖w‖² − (A·w)ᵀ(A Aᵀ)⁻¹(A·w)` equals `dist(w, rowspan A)² = ‖P_{V⊥} w‖²` — NOT proved here. That
>   identity (via `Submodule.starProjection` normal equations) + the `det(A Aᵀ)=0 ⟹ det(Q Qᵀ)=0`
>   degenerate branch are P3's geometric half.
> - **Status.** sorry-free; clean-three.

---

## Remaining pieces toward the core `∫⁻_{Q∈box} det(QQᵀ)^{−a/2} < ⊤` (Codex-informed plan)

Decorrelated design review (Codex gpt-5.x xhigh, `codex/decomp-{prompt,answer}.md`) confirms the
row-residual Schur recursion is the cheapest sorry-free route, and that **P2 and P3 are separate
bricks — not one comfortable tide**. Remaining, in dependency order:

- **P3-residual (geometric, highest risk).** `det(gram(u ⊕ w)) = det(gram u)·‖V⊥.starProjection w‖²`
  and `det(gram u)=0 ⟹ det(gram(u⊕w))=0`. Route (Codex): least-squares residual `r = w − ∑ cᵢ uᵢ`,
  `c = ⅟G *ᵥ y`, `yᵢ = ⟪uᵢ,w⟫`; show `G *ᵥ c = y`, `r ∈ Vᗮ`, `r = Vᗮ.starProjection w`, scalar `= ‖r‖²`.
  Mathlib: `Matrix.star_dotProduct_gram_mulVec`, `Submodule.eq_starProjection_of_mem_orthogonal'`,
  `real_inner_self_eq_norm_sq`.
- **P2 (uniform projection radial, medium risk).** `∃ C < ⊤, ∀ U (finrank ≥ r), ∫⁻_{ball} ofReal(‖U.starProjection w‖^{−a}) ≤ C`
  for `a < r`. **Codex CORRECTION (important):** the planned lower-bound-to-smaller-subspace route is
  WRONG — for `a>0`, `0^{−a}=0` in `Real.rpow`, so `‖P_U w‖ ≥ ‖P_W w‖` does NOT give the `ofReal`
  inequality at zeros. Instead: prove it for the ACTUAL projection via `Submodule.orthogonalDecomposition`
  + `OrthonormalBasis.measurePreserving_repr` + `setLIntegral_prod` (reduce to the landed radial lemma on
  the range coords × a bounded kernel-ball factor), then make `C` uniform by finite maximisation over
  ranks `d ∈ Icc r q`. No measurable family of rotations needed (each `U` handled pointwise).
- **P4 (Tonelli recursion, lower risk).** `F(Q') := ∫⁻_w ofReal(det(QQᵀ)^{−a/2})`; `F ≤ ofReal(det(G')^{−a/2})·C`
  (the `det(G')=0` case gives integrand `0`), then `∫⁻_{Q'} F ≤ C·∫⁻_{Q'} ofReal(det(G')^{−a/2})`, recurse
  on `b`; base `b=1`: `det = ‖row‖²`, the landed radial lemma with `n=q`. Split `a=0` first (integral =
  volume of box). Needs the measure-preserving `Matrix ≃ EuclideanSpace`-per-row plumbing
  (`EuclideanSpace.volume_preserving_measurableEquiv`, `volume_preserving_piFinSuccAbove`, `lintegral_prod`).

## Interfaces carried into the Cat I branch (NOT this thread's scope)

- **Absorption CoV** (`gammaPeelInner → det(corankGram)^{−a/2}`, i.e. integrate out `A0`) — controller-
  acknowledged separate wiring step (PeelCore/PeelMeas + Γ-Gaussian).
- **Product-structure reduction** `corankGram(A') = Q_b(A') Q_b(A')ᵀ` with `Q_b = Y·A_{≥2}` (a product of
  tail layers) → the abstract `Q`-box core. This is the wtint "submersion" reduction and is DLN-specific;
  it is an ADDITIONAL interface beyond the absorption CoV (flagged to controller).
