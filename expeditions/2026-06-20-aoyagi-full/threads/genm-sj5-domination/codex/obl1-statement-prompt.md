# Consult: the faithful Lean statement of the b=1 "corank-integrability" lemma (Obl-1)

You are a decorrelated second reviewer on a Lean 4 / Mathlib formalisation. I am about to commit
~300-500 lines to prove ONE analytic lemma and want your read on the STATEMENT SHAPE and whether a
hidden non-uniformity kills it. This is a formalisation-shape question, not a soundness question (the
underlying math design is already settled and you-concurred elsewhere).

## Background objects (Lean, verbatim signatures)

Frobenius square: `frobSq (M : α → β → ℝ) := ∑ i, ∑ j, (M i j)^2`.

The freed corner loss, `b` corank cols, `a` corank rows, `t` pivot rows, `q` deep width:
```
freedSchurLoss (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) : ℝ :=
  frobSq (P * (Qp + P⁻¹ * B12 * Qb))                       -- pivot energy  w
    + frobSq (C * (Qp + P⁻¹ * B12 * Qb) + Γ * Qb)          -- corank energy
  where  P = x.1.1 (t×t, invertible on domain), B12 = x.1.2 (t×b), C = x.2 (a×t),
         Qp = Q.submatrix Sum.inl id (pivot rows), Qb = Q.submatrix Sum.inr id (corank rows)
```

Banked ATOM brick (per fixed x, Q; `a·b/2 < c'`, `Qb Qbᵀ` PosDef, pivot energy w>0):
```
freedSchurLoss_inner_peel_le :
  ∫⁻ Γ in s, ofReal ((freedSchurLoss x Γ Q)^(-c'))
    ≤ ofReal ( det(Qb Qbᵀ)^(-a/2) · Cresid (a·b) c'
                · (w + frobSq 0 + frobSq (C·Q̃ₚ·(1 - Qbᵀ(Qb Qbᵀ)⁻¹ Qb)))^(-(c' - a·b/2)) )
  where w = frobSq(P·Q̃ₚ), Q̃ₚ = Qp + P⁻¹ B12 Qb.
```
Banked BOUNDED brick (0 ≤ c', pivot energy w>0):
```
freedSchurLoss_inner_bounded_le :
  ∫⁻ Γ in s, ofReal ((freedSchurLoss x Γ Q)^(-c')) ≤ ofReal (w^(-c')) · volume s.
```
Underlying anisotropic atom (general params, w>0, pq/2<c'):
```
corankBlock_morsePeel_setLE (Apiv Ccross Qb) (hG : (Qb Qbᵀ).PosDef) (c') (hc' : pq/2<c') (w) (hw:0<w) (s):
  ∫⁻ Γ in s, ofReal ((w + frobSq Apiv + frobSq (Ccross + Γ·Qb))^(-c'))
    ≤ ofReal ( det(Qb Qbᵀ)^(-p/2) · Cresid (p·q) c' · (w + frobSq Apiv + frobSq(Ccross·(1-P)))^(-(c'-pq/2)) ).
```

Banked pieces available:
- `∫_{ball 0 R} ‖x‖^(-α) < ∞` for `α < n` (`lintegral_norm_rpow_neg_ball_lt_top`, EuclideanSpace (Fin n)).
- `∫_{matBox r n 1} det(X Xᵀ)^(-α/2) < ∞` for `α < n-r+1` (`detGram_lintegral_lt_top`).
- Isotropic NESTED bound: `∫_z ∫_{D∈matBox p q T} (frobSq D + W z)^(-c') ≤ Cresid·∫_z W(z)^(-(c'-pq/2))`
  (`matBox_corank_residual_absZ_le`, needs W z > 0, pq/2<c').
- Two-block radial split `∫_{ball×ball}(κ²‖p1‖²+σ²‖p2‖²)^(-c') ≤ σ^(-α')·C` for `2c'-du<α'<dv`
  (`twoBlock_radial_le`, C independent of σ on the bounded sector σ≤B).
- min-stretch `σ_min(Zᵀ)·‖x‖ ≤ ‖Zᵀ x‖` (`minStretch_mul_le`); addHaar ball scaling `vol(ball r)=r^n·vol(ball 1)`.
- `Q_b = A_cor · Z_deep` (front corank rows times deeper product), via `sjTail_factor_explicit`.
- `corank_survival_ae`: for a.e. free corank block `A`, `rank(A·Z)=b` (so `Qb Qbᵀ` PosDef a.e.).

## The target (design, pen-and-paper, already settled)

For a single corank row `b=1`, at a binding cut with `a ≤ M₂` (`M₂` = deep width of Z's row space),
`c' < ½·minAdm(M)`, the corank-block integral
```
G(w,Z) := ∫_{A_cor ∈ box (b×M₂)} [ ∫_Γ (freed-corner integrand)^(-c') dΓ ] dA_cor
        ≤ C · w^(-(c'-a/2))   (+ a harmless log(1/w) factor only when a = M₂),  C uniform in Z
          on the full-rank-tail chart {Z : top M₂-1 singular values ≥ c₀ > 0}
```
via a TWO-REGIME split at τ = σ_min(Q_b) vs √w:
- τ ≥ √w: atom brick, det(Q_bQ_bᵀ)^(-a/2) = τ^(-a) (b=1); ∫ τ^(-a) over the box is a finite constant
  (box-clipped, needs a<M₂; a=M₂ gives a log), giving the C·w^(-(c'-a/2)) atom part.
- τ < √w: bounded brick, w^(-c')·vol; vol{A_cor: τ<√w} ≲ (√w)^{M₂} = w^{M₂/2}, giving w^(-(c'-M₂/2)).
Both exponents < ½·minAdm(redChain), so the reduced IH closes.

## The crux I want your read on: the pivot energy `w` vs the integration variable `A_cor`

In `freedSchurLoss`, `w = frobSq(P·Q̃ₚ)` with `Q̃ₚ = Qp + P⁻¹·B12·Qb`, and `Qb = A_cor·Z`. So **`w`
depends on the integration variable `A_cor`** (through the `P⁻¹·B12·Qb` term) UNLESS `B12 = 0`. But the
design's `G(w,Z)` treats `w` as a FIXED parameter. Three candidate Lean statements:

- **(A) Model level, fixed params.** State over the atom shape with fixed `w>0`, fixed `Ccross`, `Apiv`;
  integrate `A_cor` (setting `Qb=A_cor·Z`); consume `corankBlock_morsePeel_setLE`. Conclusion
  `∫_{A_cor∈box} [∫_Γ (w + frobSq Apiv + frobSq(Ccross + Γ·(A_cor·Z)))^(-c')] dA_cor ≤ C·w^(-(c'-a/2)) + C'·w^(-(c'-M₂/2))`.
  Self-contained; the connection to freedSchurLoss (welding) + the fact that after an absorption CoV `w`
  is A_cor-independent is deferred to the assembly (Obl-2/3, "piece A").

- **(B) freedSchurLoss level, B12 = 0.** Take `x` with `P` a unit, `B12 = 0`, fixed pivot rows `Qp`;
  then `w = frobSq(P·Qp)` is genuinely A_cor-independent. Consume `freedSchurLoss_inner_peel_le`/`_bounded_le`
  directly. Loses the B12 coupling (which the general peel has; the design routes it through an absorption
  change-of-variables that is a separate obligation).

- **(C) freedSchurLoss level, general x, uniform pivot lower bound as hypothesis.** Keep general `x`;
  add hypothesis `∀ A_cor ∈ box, w₀ ≤ frobSq(P·Q̃ₚ(A_cor))`; conclude `≤ C·w₀^(-(c'-a/2)) + …`. But then
  `w₀` is a constant, not the reduced-comparator loss `frobSq(Γ'·Z_deep)` that the outer IH integrates —
  so this may not compose with the reduced IH (the outer integral needs `w = w(reduced params)`, a function).

## Questions

1. Which of (A)/(B)/(C) is the faithful, composable Obl-1 — i.e. which one is a genuine building block
   for the full hole (a triple integral `∫_{A'} ∫_{x} ∫_Γ (freedSchurLoss x Γ Q)^(-c') < ⊤`, `Q` from the
   tail product), where the outer IH provides `∫_{reduced params} w^(-(c'-a/2)) < ⊤` with `w = frobSq(Γ'·Z_deep)`?
   In particular: after the absorption CoV `(pivot layer rows) → Γ'` (Jacobian |det P|^{M₂}, A_cor-independent),
   is `w = frobSq(Γ'·Z_deep)` genuinely A_cor-independent, so that (A) with fixed `w` is the honest inner
   lemma and the `A_cor`-integral is cleanly separated? Or does the outer descent integrate `A_cor` jointly
   with `Γ'` in a way that (A) mis-states?

2. Is there a hidden non-uniformity in "C uniform in Z on {top M₂-1 singulars ≥ c₀}" for b=1? Specifically:
   the atom part needs ∫_{A_cor∈box} τ^(-a) dA_cor ≤ W(c₀,a,M₂) with W independent of Z. Via
   `‖A_cor·Z‖ ≥ c₀·‖A_cor‖` (min-stretch, if σ_min(Zᵀ)≥c₀) one gets ∫ τ^(-a) ≤ c₀^(-a)∫‖A_cor‖^(-a) < ∞
   (a<M₂). Does this reduction actually hold for a `1×M₂` block `A_cor` and `Z : M₂×q` with `q≥M₂`,
   σ_min ≥ c₀? Any subtlety when `Z` is `M₂×q` wide (rank M₂) vs square?

3. The a=M₂ log: is it cleaner to (i) restrict Obl-1 to `a<M₂` strict (clean uniform C, no log) and land
   that as the checkpoint, handling a=M₂ as a flagged follow-up, or (ii) carry the `(1+𝟙[a=M₂]log(1/w))`
   factor from the start? For the FIRST green checkpoint of the foundational estimate, which is the
   disciplined scope?

4. Any reason the two-regime split needs σ_min(Q_b) specifically (vs. splitting on `‖A_cor·Z‖ = τ` directly,
   which for b=1 equals σ_min(Q_b) since Q_b is a single row)? Confirm b=1 ⟹ τ = ‖Q_b‖ = σ_min(Q_b).

Answer concisely, focused on the statement decision and any non-uniformity landmine. Do not write Lean code.
