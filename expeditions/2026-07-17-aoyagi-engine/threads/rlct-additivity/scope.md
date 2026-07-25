# Direct-sum RLCT additivity — dependency scope (scout, 2026-07-25)

**Task (team-lead):** confirm whether direct-sum RLCT additivity is WIREABLE before the value-side
recursion (`rlct = ½·peelCodim + ½·minAdm(sub)`) relies on it. Scope + small pinning example, no deep
build. Elder's caveat-4 on the recursion-{R=0} witness.

## TL;DR VERDICT

**(a) BUILD — detail-at-scale — for the direction the recursion actually needs.** The lower-bound
recursion needs only **superadditivity** `rlctAt (f ⊕ g) 0 ≥ rlctAt f 0 + rlctAt g 0`, and that is the
*easy* direction: a.e. pointwise domination `(f+g)^{-(a+b)} ≤ f^{-a}·g^{-b}` + Fubini
(`Integrable.mul_prod`) + the block-split volume-preserving equiv
(`volume_preserving_piEquivPiSubtypeProd`). No Mellin, no Tauberian, no Beta-integral estimate, no
monument. Estimate ~6–9 lemmas. **One reusable sub-obligation is NOT in Mathlib** (see below).

**The general EQUALITY is NOT needed** (the RLCT upper bound `rlct ≤ ½·codim` is Watanabe-**cited**, so
subadditivity — the genuinely harder half — never has to be built). If it ever were needed, subadditivity
is the Thom–Sebastiani / Lin theorem: **cite** (Lin 2011) or a real (bounded, non-monument) analysis
build.

**Most important correction:** the integral identity in the brief —
`∫|f⊕g|^{-2s} = (∫|f|^{-2s})·(∫|g|^{-2s})` — **is FALSE**. For a *sum* `f⊕g = f+g`,
`(f+g)^{-c} ≠ f^{-c}·g^{-c}`; the integrand does **not** factor. Additivity is NOT a one-Fubini
corollary of a product integrand. The product structure that *does* exist lives in the Mellin/Laplace
transform (`t^{-c} = Γ(c)⁻¹∫₀^∞ u^{c-1}e^{-ut}du`), not in the raw integral — and that route needs a
Tauberian theorem Mathlib lacks.

---

## 1. Mathlib inventory

* **No RLCT / log-canonical-threshold / lct theory.** Confirmed (`rg` over `.lake/packages/mathlib`):
  zero hits for `log.?canonical | learning.?coefficient | rlct`. We built `rlctAt` ourselves
  (`Core/Analysis/RLCT/`). This part of the brief's expectation is correct.
* **Fubini / product integrals — all present** (`Mathlib/MeasureTheory/Integral/Prod.lean`):
  - `MeasureTheory.integrable_prod_iff` (:278) — the Fubini/Tonelli integrability characterization.
  - `MeasureTheory.Integrable.mul_prod` (:346, `[NormedRing L]`) — **the load-bearing lemma**: from
    `Integrable f μ`, `Integrable g ν` get `Integrable (fun p ↦ f p.1 * g p.2) (μ.prod ν)`.
  - `integral_prod` (:494), `integral_prod_mul` (:566) — the value-level Fubini (not needed for the
    inequality, listed for completeness).
* **Block-split volume-preserving equivs** (`Mathlib/MeasureTheory/Constructions/Pi.lean`):
  - `MeasureTheory.volume_preserving_piEquivPiSubtypeProd` (:739) — splits `(Fin D → ℝ)` over a
    predicate `p` into `({i // p i} → ℝ) × ({i // ¬p i} → ℝ)`, volume-preserving. **The idiomatic tool
    for the peel/residual coordinate split.**
  - `volume_preserving_piFinSuccAbove` (:825) — peel one coordinate (for a "one-square-at-a-time"
    inductive variant, if wanted).
  - `Equiv/Homeomorph.sumPiEquivProdPi` — `(Fin a ⊕ Fin b → ℝ) ≃ (Fin a → ℝ) × (Fin b → ℝ)` if you
    prefer the `Fin a ⊕ Fin b ≃ Fin (a+b)` framing.
* **1-D / radial thresholds** (only relevant to the *hard* equality direction, which we avoid):
  `intervalIntegral.integrableOn_Ioo_rpow_iff` (already used in `SumSq.lean`),
  `integrable_fun_norm_addHaar` (polar reduction), and
  `integrable_rpow_neg_one_add_norm_sq` / `integrable_one_add_norm`
  (`Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`) — `(1+‖x‖²)^{-r}` integrable iff
  `finrank < r`; this is exactly the Beta-integral finiteness the subadditivity/Beta-estimate route
  would need.
* **Mellin transform** exists (`Mathlib/Analysis/MellinTransform.lean`: `mellin`, holomorphy on strips
  from big-O decay) but there is **no Tauberian theorem** (pole ↔ Laplace/Mellin asymptotic), so the
  Mellin route to additivity is **not** supported end-to-end.

## 2. Our `rlctAt`, and why superadditivity is the easy direction

`RLCT.rlctAt K x = sSup { c | 0 ≤ c ∧ IntegrableAtFilter (fun y ↦ (K y)^(-c)) (𝓝 x) }`
(`Core/Analysis/RLCT/Local.lean:55`; `negPow K c y = (K y)^(-c)` via `Real.rpow`). `SumSq.lean` proves
`rlctAt (∑ yᵢ²) 0 = C/2`, so the **peel** (a nondegenerate quadratic of rank = peelCodim) already has
value `½·peelCodim`.

**Superadditivity (`≥`, the lower bound) — clean chain.** Let `a` be admissible for `f` at `x`
(`0 ≤ a`, `∫_U f^{-a} < ∞`) and `b` for `g` at `y`. Off the set `({f=0}×V) ∪ (U×{g=0})`, where `f,g>0`:

    f+g ≥ f > 0, exponent -a ≤ 0  ⟹  (f+g)^{-a} ≤ f^{-a}   (Real.rpow_le_rpow_of_nonpos)
    f+g ≥ g > 0, exponent -b ≤ 0  ⟹  (f+g)^{-b} ≤ g^{-b}
    multiply (all positive)       ⟹  (f+g)^{-(a+b)} ≤ f^{-a}·g^{-b}

`f^{-a}(x)·g^{-b}(y)` is integrable on `U×V` by `Integrable.mul_prod`; `(f⊕g)^{-(a+b)}` is a.e.
dominated by it, so integrable (`Integrable.mono'`). Hence `a+b` is admissible for `f⊕g`; taking `sSup`
gives `rlctAt f x + rlctAt g y ≤ rlctAt (f⊕g) (x,y)`. Transport the product structure to `Fin D → ℝ`
with `volume_preserving_piEquivPiSubtypeProd`. `Real.rpow_le_rpow_of_nonpos` is already used in
`LocalMono.lean:100`; the `sSup`/down-set plumbing rides `LocalMono.localAdmissibleExponents_downward`.

**The one sub-obligation not in Mathlib.** The domination bound **fails on `{f=0}∪{g=0}`** (there
`0^{-a}=0` on the RHS but the LHS is positive), so the a.e. step needs
**`vol({f=0}) = 0` and `vol({g=0}) = 0`**.
- For the **peel** `f = ∑zᵢ²`: `{f=0}` is a point/linear subspace of positive codim ⟹ trivially null.
- For the **residual** `g = R = ∑ Fⱼ²` (a sum-of-squares family; `R ≢ 0` in the pole regime):
  `{R=0} = ⋂{Fⱼ=0} ⊆ {F₁=0}` for a single nonzero `F₁`, so it reduces to **"the zero set of a nonzero
  polynomial in `n` real variables is Lebesgue-null."** Mathlib has this only for 1 variable
  (`Polynomial` finite-roots → null); the multivariate version is **absent** but is a clean reusable
  detail-at-scale lemma (induction on dimension: for a.e. `x₁`, `P(x₁,·)` is a nonzero polynomial ⟹ its
  zero set is null ⟹ Fubini). **This is the single genuine new brick.**

**Subadditivity (`≤`, the upper bound) — NOT needed, and genuinely harder.** `(f+g)^{-c} ≤ f^{-c}`
bounds the integrand the wrong way for a divergence proof; the honest route is the delicate scaling/Beta
estimate (`∫_{-δ}^{δ}(z²+a)^{-c}dz ≍ max(1, a^{½-c})`) or Thom–Sebastiani. Because `rlct ≤ ½·codim` is
Watanabe-**cited**, the value engine never needs this half. Do NOT build it speculatively.

## 3. The fork the controller should weigh (may make even this moot)

Route B is **ideal-level**: Object A (`IdealInvariance.rlctAt_sumSqFam_eq_of_germ_eq`, LANDED) reduces
`rlctAt` of a sum-of-squares family to its germ ideal, and the monomial-ideal RLCT `= lnmin` (charter C,
LANDED) reads the value off the Newton polyhedron / QIP. The residual `R` in the recursion is *itself* a
sum-of-squares family (tube-cover probe: `R = ‖Y_row0‖² + δ₂²‖Y_row1‖² + …`). So the recursion can very
plausibly stay in the sum-of-squares-family world and get "additivity" as **combinatorial additivity of
`lnmin` under disjoint-variable union of monomial families** — pure QIP/Newton-polyhedron combinatorics,
no analysis, no null-set lemma. If that holds, the analytic `rlctAt` superadditivity is **not on the
critical path at all**; the elder's caveat-4 is discharged combinatorially. Recommend a quick check of
whether `CThetaValue.lnMval_min` / `qipM` already has (or cheaply admits) `lnmin(M₁ ⊔ M₂) = lnmin M₁ +
lnmin M₂` for independent blocks before committing to the analytic build.

## 4. Pinned contracts (durable; NOT proved)

```lean
namespace RLCT
open MeasureTheory

/-- Direct sum of germs on disjoint coordinate blocks (subset form). -/
noncomputable def directSumOn {D : ℕ} (p : Fin D → Prop) [DecidablePred p]
    (f : ({i // p i} → ℝ) → ℝ) (g : ({i // ¬ p i} → ℝ) → ℝ) : (Fin D → ℝ) → ℝ :=
  fun w ↦ f (fun i ↦ w i.1) + g (fun i ↦ w i.1)

/-- SUPERADDITIVITY — the lower-bound direction the value recursion consumes.
    Needs: f,g ≥ 0 measurable; the block-null hypotheses `vol {f=0}=0`, `vol {g=0}=0`
    (trivial for the quadratic peel; the residual case rides the poly-null lemma). -/
theorem rlctAt_directSumOn_ge {D : ℕ} (p : Fin D → Prop) [DecidablePred p]
    (f : ({i // p i} → ℝ) → ℝ) (g : ({i // ¬ p i} → ℝ) → ℝ)
    (x : {i // p i} → ℝ) (y : {i // ¬ p i} → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (hfnull : volume {z | f z = 0} = 0) (hgnull : volume {z | g z = 0} = 0) :
    rlctAt f x + rlctAt g y
      ≤ rlctAt (directSumOn p f g) (fun i ↦ if h : p i then x ⟨i,h⟩ else y ⟨i,h⟩) := by
  sorry -- a.e. domination (f+g)^{-(a+b)} ≤ f^{-a}·g^{-b} + Integrable.mul_prod
        -- + volume_preserving_piEquivPiSubtypeProd + LocalMono down-set + csSup

/-- The reusable brick Mathlib is missing (multivariate poly null zero-set). -/
theorem measure_zero_setOf_eval_eq_zero {n : ℕ} {P : MvPolynomial (Fin n) ℝ} (hP : P ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  sorry -- induction on n: 1-var finite roots + Fubini
end RLCT
```

## 5. Kill-condition (stated before hunting confirmations)

*Claim under test:* superadditivity `rlctAt(f⊕g) ≥ rlctAt f + rlctAt g` holds for all nonneg germs with
null zero-sets. **Kill:** a nonneg germ pair on independent blocks with `rlctAt(f⊕g) < rlctAt f + rlctAt
g`. Checked, survives: `∑zᵢ² ⊕ ∑wⱼ²` (→ `(k+m)/2`), `|x|⊕|y|` (→ `2`), `z² ⊕ w⁴` (→ `½+¼=¾`,
quasi-homogeneous). All equal the sum, so `≥` holds. The domination proof is exponent-agnostic (uses only
`f,g≥0`, exponents `≤0`), so no dimension/degeneracy edge case breaks the `≥` inequality — the ONLY
crack is the null-set hypothesis, which fails exactly when `f≡0` or `g≡0` (out of the pole regime).

## 6. Reflection

- **Most likely to advance:** the fork in §3 — if `lnmin` is combinatorially additive on disjoint blocks
  (very plausible from the QIP structure), the analytic build is off the critical path and caveat-4 is
  discharged for free.
- **Most likely to break:** the `measure_zero_setOf_eval_eq_zero` brick — not conceptually hard, but the
  multivariate induction + Fubini plumbing is the real (bounded) labour; if the residual germ is only
  *analytic* not polynomial in some framing, the lemma must be stated for real-analytic (still true,
  slightly more setup).
- **Next computation that clarifies:** grep `CThetaValue.lean`/`qipM` for an existing disjoint-union
  `lnmin` additivity; if absent, pin it and decide analytic-vs-combinatorial before any build.
