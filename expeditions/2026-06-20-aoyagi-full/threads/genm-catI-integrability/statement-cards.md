# genm-catI-integrability — statement cards (abstract Q-box integrability core)

Branch `genm-catI-integrability-work` (off `origin/genm-catclose-work` @ `8f67aeb5`, which merges
the P2 branch `genm-catI-p2-proj`). Controller pins the integration SHA.

The Cat I good-stratum obligation, in its **abstract, network-free (free-`Q`) form**: the weight
integral `∫⁻_{Q ∈ box} det(Q Qᵀ)^{−a/2}` over a box of `b×q` matrices (rows in `ℝ^q`-balls) is finite
when `a < q − b + 1`. Everything is in `∫⁻`/`ENNReal` (Tonelli unconditional). Three bricks + the
keystone.

---

## Card 1 — Gram determinant row-residual recursion (piece P3, geometric half)

> **Claim.** Prepending a row `w` to a family `u : Fin n → E` (`E` finite-dim real inner-product
> space) multiplies the Gram determinant by the squared residual of `w` off `span (range u)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.det_gram_cons`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGramResidual.lean`)
>   `{n} {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`
>   `(u : Fin n → E) (w : E) : (Matrix.gram ℝ (Fin.cons w u)).det = (Matrix.gram ℝ u).det * ‖(Submodule.span ℝ (Set.range u))ᗮ.starProjection w‖ ^ 2`
> - **Gloss.** `det(gram(w ∷ u)) = det(gram u) · ‖P_{V⊥} w‖²`, `V = span(range u)`, `P_{V⊥}` the
>   orthogonal projection onto `V⊥` (`Submodule.starProjection`).
> - **Proved.** UNCONDITIONAL (both branches). Good-stratum `det(gram u) ≠ 0`: Schur complement
>   (`det_fromBlocks₁₁`) + least-squares residual `r = w − ∑ cᵢ uᵢ`, `c = ⅟(gram u)·y`,
>   `yᵢ = ⟪uᵢ,w⟫`, normal equations `gram u ·ᵥ c = y`, `r = V⊥.starProjection w`, Schur scalar
>   `= ‖r‖²`. Degenerate `det(gram u) = 0`: shared kernel vector (`exists_mulVec_eq_zero_iff` +
>   `star_dotProduct_gram_mulVec`) kills both determinants.
> - **Assumed.** `[FiniteDimensional ℝ E]` (so `V⊥` has orthogonal projection; satisfied by
>   `EuclideanSpace`). No positivity/invertibility hypothesis.
> - **Cited.** none (all Mathlib).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced).

## Card 2 — uniform projection radial bound (piece P2)

> **Claim.** For `a < r`, `1 ≤ r ≤ q`, a single finite constant bounds the projection radial integral
> uniformly over all subspaces `U ⊆ ℝ^q` of dimension `≥ r`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.projection_rpow_lintegral_uniform`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJProjRadial.lean`)
>   `(q r : ℕ) (hr : 1 ≤ r) (hrq : r ≤ q) {a : ℝ} (ha : a < r) (R : ℝ) : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ U : Submodule ℝ (EuclideanSpace ℝ (Fin q)), r ≤ Module.finrank ℝ U → (∫⁻ w in Metric.ball 0 R, ENNReal.ofReal (‖U.starProjection w‖ ^ (-a))) ≤ C`
> - **Gloss.** `∃ C < ⊤, ∀ U (finrank ≥ r), ∫⁻_{ball R} ‖P_U w‖^{−a} ≤ C`.
> - **Proved.** For fixed `U`, transport by a single composite isometry
>   `E ≃ᵢ WithLp 2 (𝔼^d × 𝔼^e)` (`orthogonalDecomposition` ∘ the two coord reprs), measure-preserving
>   via `WithLp.volume_preserving_ofLp`; enlarge `ball` to `ball_d ×ˢ ball_e`, split, bound the radial
>   factor by `RouteMSJRadialInt.lintegral_norm_rpow_neg_ball_lt_top` (`a < r ≤ d`) and the volume
>   factor by a bounded ball. Uniform `C` = finite max over `d ∈ [r,q]`, `e ∈ [0,q]`.
> - **Route deviation (flagged for review).** The originally-planned transport through `↥U × ↥Uᗮ`
>   is unreachable (the submodule carries `Subtype.instMeasurableSpace`, not `borel ↥U`, so
>   `measureSpaceOfInnerProductSpace` never fires); folding both reprs into one composite isometry
>   keeps all measures on `E` and coordinate spaces. Same math, same bound. **p2rev** verifies this.
> - **Delivered by** teammate `p2proj` (`origin/genm-catI-p2-proj @ c2a68086`).
> - **Status.** sorry-free; clean-three (forced).

## Card 3 — the abstract Q-box integrability core (keystone)

> **Claim.** `∫⁻_{Q ∈ box} det(Q Qᵀ)^{−a/2} < ⊤` when `a < q − b + 1`, `Q` a `b`-tuple of
> `ℝ^q`-vectors in `R`-balls.
>
> - **Lean:** `DLNFibre.DLN.RLCT.qbox_lintegral_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJQBoxCore.lean`)
>   `{q : ℕ} {a : ℝ} : ∀ (b : ℕ), b ≤ q → a < (q : ℝ) - (b : ℝ) + 1 → ∀ (R : ℝ), (∫⁻ Q in Set.univ.pi (fun _ : Fin b => Metric.ball (0 : EuclideanSpace ℝ (Fin q)) R), ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2))) < ⊤`
> - **Gloss.** For `Q : Fin b → ℝ^q` ranging over the box `(ball 0 R)^b`, the `∫⁻` of
>   `det(gram Q)^{−a/2}` is finite whenever `a < q − b + 1`. `gram ℝ Q = Q Qᵀ` (Gram of the rows).
> - **Proved.** Tonelli row-recursion on `b`. Peel one row (`piFinSuccAbove` measure-preserving split
>   + `setLIntegral_prod_symm`); factor the Gram determinant by Card 1; bound the inner `w`-integral
>   uniformly by Card 2 (`dim V⊥ ≥ q − b + 1 > a`); outer integral is the `(b−1)`-row IH. Base
>   `b = 0`: empty Gram, `det = 1`, integrand `≡ 1`, integral `= vol(point) < ⊤`.
> - **Proved direction.** Only the `⟸` (finiteness for `a < q − b + 1`). Tightness (divergence at
>   `a ≥ q − b + 1`) is NOT claimed and not needed downstream.
> - **Non-vacuity.** Witnessed in-file (`example`): `q = 2, b = 1, a = 1 < 2`, where the integrand
>   `‖w‖^{−1}` has a genuine (non-removable) singularity and the integral is finite.
> - **Assumed / Cited.** none beyond Cards 1–2 (all Mathlib otherwise).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced fresh olean).

---

## Interfaces carried into the DLN Cat I branch (NOT this thread's scope)

Named for what they are (`name = content`), per controller guidance:

- **Absorption change-of-variables** (`gammaPeelInner → det(corankGram)^{−a/2}`, i.e. integrate out
  `A₀`) — a separate wiring step (PeelCore/PeelMeas + Γ-Gaussian).
- **Product-structure / atom-recursion interface** `corankGram(A') = Q_b Q_bᵀ`, `Q_b = Y·A_{≥2}`.
  This does **not** fold cleanly into `[this core] ∘ [loss IH]`: `J(A_{≥2}) = det⁺(gram A_{≥2})^{−b/2}`
  makes the composite recurse **one chain-length deeper** into the `(S, J)` atom (shorter chain,
  threshold `a < min(M₂,…,M_last) − b + 1 ≤ q − b + 1` for contracting tails). It is an
  **atom-recursion hypothesis** (task #111 / sjdecomp), NOT a fold. This abstract Q-box core is the
  **leaf** that recursion bottoms out on (the dominant-minor chart where `J = unit`).

## Files
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGramResidual.lean` (P3, Card 1) — new, ~200 LoC.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJProjRadial.lean` (P2, Card 2) — from `genm-catI-p2-proj`.
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJQBoxCore.lean` (keystone, Card 3) — new, ~180 LoC.
- Consumes the landed `RouteMSJRadialInt` (radial `∫⁻`) and `RouteMSJGramSchur` (superseded by the
  gram-native Schur in `RouteMSJGramResidual`). Not wired to the aggregator (controller integrates).
