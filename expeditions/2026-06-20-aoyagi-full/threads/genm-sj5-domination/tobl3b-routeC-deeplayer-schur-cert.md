# T-Obl3b Route-C (deep-layer rational Gram–Schmidt frame chart) at (3,2,3): **MODERATE — CLOSES cleanly**

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.** Exact symbolic algebra
(sympy) for every load-bearing identity (`/tmp/verify_codex.py`, `/tmp/schur323*.py`, `/tmp/scope_check.py`
— reproduce the same steps); Monte-Carlo only as a threshold guide. Decorrelated `local-codex-consult`
(xhigh, my tentative conclusion WITHHELD — prompt framed "adjudicate either way"):
`codex/tobl3b-routeC-deeplayer-{prompt,answer}.md`.

**The ONE truth-value.** Does ROUTE C — a deep-layer polynomial Schur-flag change-of-variables (peeling
`A₁`'s OWN corank via a chart on Mathlib's banked `MeasureTheory.Function.Jacobian` CoV, NO
Stiefel/Haar/Wishart/SVD density) — CLOSE the `s≥2` waist box integral at `½·minAdm`, cleanly (MODERATE),
or hit Lean-friction / a wall (HEAVY / WALL)?

---

## ★ HEADLINE VERDICT — **MODERATE (clean route-C, buildable) for the (3,2,3) anchor and ALL `s=2` waists.**

Route C closes the `(3,2,3)` waist box integral at the TIGHT threshold `c < ½·minAdm(3,2,3) = 5/2`, using
ONLY the banked general-Jacobian CoV + affine shears + the banked qPeel engine — **no SVD, no Wishart, no
Stiefel, no Haar, no eigenvalue density.** The chart is a **rational orthogonal-frame flag** with a
`det`-power Jacobian, verified exact end-to-end. The `s≥3` waists have a precisely-scoped boundary
(below): tight when the ambient truncation caps the Vandermonde repulsion, UNDERSHOOTS otherwise.

**Correction of my prior lean (and the recon's kill-condition).** My first pass concluded the deep-layer
Schur chart leaves an irremovable cross term and route C therefore forces the SVD density (HEAVY). **That
was a WRONG-SHEAR artifact.** I sheared `A₁`'s rows by the *LU pivot ratio* `d/a` (makes `A₁` triangular,
does NOT orthogonalise the rows → cross term survives). The correct move — found by the decorrelated Codex
and then verified here exactly — is the shear by the **Gram–Schmidt ratio** `ℓ/a = ⟨ρ₁,ρ₂⟩/‖ρ₁‖²`, i.e.
the *rational* `LDLᵀ` congruence of the deep Gram `G`. This IS a diagonalisation of `G`, but by a
**triangular (rational) transform, not the orthogonal eigen-frame** — so it stays polynomial and dodges
the Stiefel/Haar void. The recon's kill-condition ("if a rank-2 deep-layer Schur chart cannot be written
as a Jacobian-CoV with a `det`-power Jacobian in one module, route C is not moderate") is **met on the
YES side**: the chart below is exactly such a module.

---

## Part 1 — The verified `(3,2,3)` chart (`A₀` is `3×2`, `A₁` is `2×3`, `minAdm=5`, target `5/2`)

### 1.0 The structural fact the whole route rests on (exact)

`‖A₀A₁‖_F² = tr(M·G)`, `M = A₀ᵀA₀ ∈ Sym₊(2)` (front Gram), `G = A₁A₁ᵀ ∈ Sym₊(2)` (deep Gram). The loss
depends on `A₁` ONLY through the `s×s` Gram `G`, and on `A₀` only through `M`. [DERIVED, `schur323.py` (A).]
Consequence used below: diagonalising `G` (making the two deep rows orthogonal) makes `tr(M·diag(Λ))`
**block-additive automatically**, because the trace against a diagonal `Λ` reads only the diagonal of
`L̃ᵀ M L̃`, and those diagonals are honest squared norms `‖A₀·L̃eⱼ‖²`. One does NOT need `M` and `G`
simultaneously diagonal — only `G` diagonal. **This is the insight that unlocks route C.**

### 1.1 The chart map `Φ` — a rational orthogonal frame + radial flag on `A₁` (2×3)

Coordinates `(a, ℓ, w, p, q, t)` (6 = dim `A₁`). Rational **orthogonal** (not orthonormal) frame of `ℝ³`:

    n  = (1, p, q),   f₁ = (−p, 1, 0),   f₂ = (−q, −pq, 1+p²).

[DERIVED, `verify_codex.py` (i)] `⟨n,f₁⟩=⟨n,f₂⟩=⟨f₁,f₂⟩=0`; `‖n‖²=D:=1+p²+q²`, `‖f₁‖²=1+p²`,
`‖f₂‖²=(1+p²)D`. Rows of `A₁`:

    ρ₁ = a·n,     ρ₂ = ℓ·n + w·(f₁ + t·f₂).

`(p,q)` chart the direction of `ρ₁` (dominant-first-coordinate sector, `|p|,|q|≤1`), `a` its radial;
`t` charts the direction of the part of `ρ₂` orthogonal to `ρ₁`, `w` its radial; `ℓ` is the
`ρ₁`-component of `ρ₂` (the Gram–Schmidt-removable part, since `ℓ/a = ⟨ρ₁,ρ₂⟩/‖ρ₁‖²`).

### 1.2 The Jacobian is a `det`-power monomial (the load-bearing charge)

[DERIVED, `verify_codex.py` (iii), exact 6×6 determinant]

    |det DΦ| = a²·w·(1+p²)·D.

The `a²` and `w¹` are the radial powers (`ρ₁∈ℝ³`: 1 radial + 2 angular ⇒ `a^{3−1}`; `ρ₂`-orthogonal part
in the 2-plane `⊥n`: 1 radial + 1 angular ⇒ `w^{2−1}`); `(1+p²)D` is the bounded frame factor. This is
the "`det(pivot)`-power Jacobian on `MeasureTheory.Function.Jacobian`" the brief asked for — **NOT** a
Vandermonde/Stiefel density.

### 1.3 The loss is EXACTLY block-additive in this chart (no cross term)

With the front-column Gram–Schmidt shear `g := x + (ℓ/a)·y` (`A₀ = [x | y]`, `x,y ∈ ℝ³` its columns;
`(x,y)↦(g,y)` is a translation at fixed `ℓ,y` — Jacobian 1):

    L = ‖A₀A₁‖² = D·a²·‖g‖²  +  (1+p²)(1+D·t²)·w²·‖y‖².      [DERIVED, verify_codex.py (ii), = 0 residual]

No cross term. Compare the WRONG LU shear, which leaves `L = ‖ρ₁‖²‖g‖² + ‖W‖²‖a₂‖² + 2⟨g,a₂⟩(bW₁+cW₂)`
with a **sign-indefinite** cross term and `inf(L/blockadditive)=0` (`schur323.py` (C),(D)) — that is why the
LU shear cannot feed qPeel and the Gram–Schmidt shear can.

### 1.4 Feeding the banked qPeel — the charge adds to `½·minAdm` TIGHT

Since `D≥1` and `(1+p²)(1+Dt²)≥1`, `L ≥ a²‖g‖² + w²‖y‖²`, so `L^{−c} ≤ (a²‖g‖²+w²‖y‖²)^{−c}`; and the
Jacobian `a²w(1+p²)D ≤ 9·a²w` on the sector (`D∈[1,3]`, `(1+p²)D∈[1,9]`). The `ℓ` variable decouples
(only in `g`, integrates to a constant); `p,q,t` are on a bounded box with a bounded integrand
(`∫dpdqdt = const`). What remains is exactly

    const · ∫ (a²‖g‖² + w²‖y‖²)^{−c} · a²·w · da dw dg dy  =  const · qPeelIntegral 2 ![2,1] ![2,2] T c

with radials `u=(a,w)`, deep blocks `g,y ∈ ℝ³` (`Uᵢ=‖·‖²`, `mᵢ+1 = 3`), Jacobian powers `h=(2,1)`.
Banked `RouteMSJCorankQ.qPeelIntegral_lt_top` gives finiteness for

    c < ½·Σᵢ(hᵢ+1) = ½·((2+1)+(1+1)) = 5/2 = ½·minAdm(3,2,3),   gates hᵢ≤mᵢ: 2≤2, 1≤2  ✓  [TIGHT]

The gate holds with NO truncation for `(3,2,3)` (`x=z=3`); `minAdm = Σⱼ min(x,z+s+1−2j) = 3+2 = 5`
(`schur323b.py`). MC threshold probe of the full box integral trends to `≈5/2` (`schur323c.py`, noisy at
small `t`) — the math does not wall below `5/2`, so the label is MODERATE/HEAVY, never WALL.

---

## Part 2 — Why this avoids BOTH the front-Schur pivot wall AND the SVD density (task item 3)

- **Avoids the front-Schur wall** (`RouteMSJCorankPeel.corankBlock_morsePeel_eq`, which needs `Qb·Qbᵀ`
  PosDef and dies on the waist). That atom peels the FRONT factor's corank against a *deep-derived*
  coupling `Qb`, needing `Qb` full row rank — which FAILS because the deep layer is rank-deficient on the
  waist. Route C instead **peels the DEEP factor's own frame** and diagonalises its own Gram `G`; there is
  no rank-deficient coupling to invert — the "coupling" is the clean rational frame. Structurally sidesteps
  the PosDef gate. [The chart peels `A₁`'s corank, not the `A₀·A₁` corner — as required.]
- **Avoids the SVD/Wishart density.** Removing the cross term needs `G` diagonal, but via the
  **triangular** `LDLᵀ`/Gram–Schmidt transform (rational), NOT the **orthogonal** eigen-frame (which would
  be the rectangular SVD `A₁ ↦ (σ,U∈O(s),V∈Stiefel V_s(ℝ^z))` whose Jacobian is the Weyl/Vandermonde
  density Mathlib lacks — `svd-density-mathlib-recon.md`). [The eigen-route diagonalises via
  `verify` `schur323d.py`; the triangular route achieves the same block-additivity without it.] The
  direction sphere is covered by a FINITE atlas of rational affine charts (dominant-coordinate sectors),
  replacing the global Stiefel frame bundle — the standard "affine-chart atlas" bypass of the Stiefel void.

### The flag recursion terminates cleanly (task item 3)

Depth `≤ s`: pivot `ρ₁` (rational frame, Jac `det`-power), Gram–Schmidt the remaining `s−1` rows against
it (Jac-1 shears), recurse on the `(s−1)×(z−1)` orthogonal residual, terminating at the `s=1` leaf
(a single row = product of two Morse integrals, consumed by `sumSqND_box_lt_top` inside qPeel). Each level
is a `det(pivot)`-power Jacobian on the banked `MeasureTheory.Function.Jacobian` CoV — no Stiefel/Haar.

---

## Part 3 — Width-general scope: `s=2` tight everywhere; `s≥3` has a precise undershoot boundary (task item 4)

[DERIVED, `scope_check.py`, exact] The one-row-at-a-time flag delivers raw powers `hⱼ = z−j`
(`j=1..s`), so after the ambient truncation `h̃ⱼ = min(z−j, x−1)` the chart charge is
`Σⱼ min(x, z+1−j)`. The SVD/Weyl route delivers `hⱼ^{SVD} = z+s−2j` (extra `s−j` per row = the
**Vandermonde inter-singular-value repulsion**), giving `Σⱼ min(x, z+s+1−2j) = minAdm`.

| regime | flag charge vs `minAdm` | verdict |
|---|---|---|
| `s=1` | equal, always | tight (also the banked route-0 product-of-Morse) |
| `s=2`, ALL widths | equal WITH correct orientation | **tight — route C MODERATE** |
| `s≥3`, small `x` (e.g. `(3,3,4)`, `(4,3,5)`) | equal (truncation caps the repulsion) | tight |
| `s≥3`, large `x` (e.g. `(4,3,4)`: 9<10; `(5,4,6)`: 17<18) | **UNDERSHOOTS by the uncapped repulsion** | route C insufficient |

- **Orientation matters for `s=2`, `x≠z`.** Peel the factor whose ROWS live in the larger ambient (blocks
  land in the smaller): peel `A₁` when `x≤z`, peel `A₀ᵀ` (transpose, legitimate by the `(C,θ)`
  permutation/transpose invariance) when `x≥z`. Either gives `minAdm` at `x=z`. For the anchor `x=z=3` it
  is moot. [`scope_check.py`: `(4,2,3)`,`(3,2,4)`,`(5,2,3)` all tight via the max-orientation.]
- **`s≥3` large-`x` is the genuine boundary.** The triangular Cholesky/Gram–Schmidt pivots are NOT the
  eigenvalues; they reproduce the staircase `z−j` but miss the eigenvalue-separation charge `∏|σᵢ²−σⱼ²|`.
  When `x` is large enough to "see" past the truncation, the flag undershoots the true `minAdm/2`. The
  integral is still finite up to `minAdm/2` (fact), so this is a **chart insufficiency, not a wall** —
  recovering tightness needs a repulsion-capturing refinement (a nested residual blow-up separating the
  pivots — OPEN, plausibility uncertain) or the SVD/Weyl density (HEAVY). Decorrelated Codex independently
  flagged this exact `s≥3` boundary (its Q5).

---

## Part 4 — VERDICT + build-path

### **MODERATE (clean route-C, buildable now) for the `(3,2,3)` anchor and all `s=2` waists.**
### **`s≥3` large-`x`: route C UNDERSHOOTS — escalate (repulsion chart OPEN, else SVD density HEAVY).**

**Build-path (dependency order) — the `s=2` module.** BANKED unless flagged NEW.
1. `L = tr(M G)` and the block-additive chart identity
   `L = D a²‖g‖² + (1+p²)(1+Dt²)w²‖y‖²`, `g = x+(ℓ/a)y`. [NEW, `ring` after expansion — verified exact.]
2. The rational frame `Φ` (`n,f₁,f₂` orthogonal; `|det DΦ| = a²w(1+p²)D`). [NEW: orthogonality/norms by
   `ring`; the 6×6 determinant by explicit `ring`/`Matrix.det` — some labour, no new primitive. Verified.]
3. Change of variables via `MeasureTheory.Function.Jacobian.lintegral_image_eq_lintegral_abs_det_fderiv_mul`
   on the sector chart; front shear `(x,y)↦(g,y)` via `measurePreserving_add_right`. [BANKED CoV +
   MP-shear pattern; box-enlargement `≤` for the shear-image box.]
4. Bound the frame factors (`D∈[1,3]`, `(1+p²)D≤9`), decouple `ℓ`, `∫dpdqdt = const`; assemble the
   `L ≥ a²‖g‖²+w²‖y‖²` majorant. [NEW, elementary bounds.]
5. Finite rational-chart atlas covering `A₁` up to null sets (dominant-coordinate × sign × pivot-row ×
   `f₁↔f₂` residual sectors). [NEW, measurable-cover pattern, analogous to the banked
   `RouteMSJShellCover.lintegral_le_sum_finCover`.]
6. `RouteMSJCorankQ.qPeelIntegral_lt_top 2 ![2,1] ![2,2] T c` for `c<5/2`. [BANKED, sorry-free.]

**Banked vs new split.** BANKED: `qPeelIntegral_lt_top` (the whole Morse-corner engine, exact
`h=(2,1),m=(2,2)→5/2`), Mathlib general-Jacobian CoV + orthogonal/affine CoV, `sumSqND_box_lt_top`, the
finite-cover assembly, the `frobSq`/`tr(MG)` API. NEW (all `ring`-checkable or banked-pattern, NO new
Mathlib primitive): the rational frame chart `Φ` + its `det`-power Jacobian (item 2), the block-additive
loss identity (item 1), the frame-factor bounds + `ℓ`-decoupling (item 4), the rational-chart atlas
(item 5). **This is strictly cheaper than the SVD density** (which needs Stiefel + Haar + the Weyl
Jacobian, all absent) — route C is the right base-case route for `s≤2`.

**Recommendation to the controller.** Wire the `s≤2` 3-width waist base case via route C (this chart) —
MODERATE, no density. For the `s≥3` large-`x` waists (`(4,3,4)`-type), do NOT force route C: either open a
short follow-on for a repulsion-capturing rational refinement, or accept the SVD/Weyl density there. The
`s=1` leaf remains the banked route-0 product-of-Morse. Note `minAdm`'s permutation invariance lets you
orient the chart (peel `A₁` vs `A₀ᵀ`) — exploit it for `x≠z`.

---

## Close

- **Firmest result.** Route C **CLOSES the `(3,2,3)` waist at the TIGHT `5/2`**, verified by exact symbolic
  algebra end-to-end: `L = tr(MG)`; the rational Gram–Schmidt frame chart with `|det DΦ| = a²w(1+p²)D`;
  the exactly block-additive `L = Da²‖g‖² + (1+p²)(1+Dt²)w²‖y‖²`; feeding banked
  `qPeelIntegral_lt_top` with `h=(2,1),m=(2,2)`, gates holding, threshold `5/2`. Decorrelated Codex derived
  the same closing chart independently; I verified its every load-bearing identity (my rubber-stamp guard:
  the `a²w` charge and the zero-cross-term identity were re-derived, not trusted).
- **Most likely to break it.** (i) The rational-chart ATLAS exhaustiveness (does the finite dominant-sector
  cover truly hit every `A₁` up to null sets, with the frame factors bounded on each sector?) — standard
  but must be discharged, not waved. (ii) The `s≥3` large-`x` undershoot is real (exact-confirmed) — if the
  base case must cover those uniformly, route C alone is insufficient there and the verdict for THOSE
  widths is HEAVY. (iii) The 6×6 `det DΦ = a²w(1+p²)D` in Lean (opaque-width `Matrix.det`) may want the
  explicit-index `have`+`exact` pattern from `lean/CLAUDE.md`.
- **Next construction / consult.** (a) Formaliser: prototype the `s=2` module (items 1–6) — the `ring`
  identities are done here; the atlas cover is the main new labour. (b) Pen-and-paper follow-on (if the
  controller needs `s≥3` large-`x`): does a nested residual blow-up recover the Vandermonde repulsion
  charge rationally, or is the SVD/Weyl density forced there? That is the one open question this cert
  leaves — cleanly scoped to `s≥3`, `x > z+1−j` widths.
