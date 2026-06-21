import DLNFibre.DLN.RLCT.Validate.Case222Cover
import DLNFibre.DLN.RLCT.Validate.Case222Lemma2

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Resolution` — the `(2,2,2)` concrete resolution cover

The top-level `(2,2,2)` assembly: the explicit loss `myF222 = ‖A·B‖²` in flat coordinates
(`a00=x0..b11=x7`), its resolution chart tree, and the RLCT value
`rlctAtOn myF222 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)` (the cover-form; `fm`'s `⨅ = 3/2` wraps it).

The architecture (Codex 2026-06-21, asymmetric): everything at the lintegral level (the blow-up nodes
are NOT homeomorphisms — only `lemma2Hom` is, entering as a single-chart change-of-variables inside an
integral, never an `rlctAtOn` transport). The `≤` direction needs only ONE binding leaf chart
(`rlctAtOn_le_of_box_diverges` + `monomialIntegrand_lintegral_box_eq_top`); the `≥` direction needs
the full `Σ_24` cover (all leaves finite below `⨅` ⟹ `U`-integral finite, `cover_integral_lt_top_iff`).

The chart tree (`r1-222-cover-handoff-split.md`): step-1 (A-pivot blow-up, `|det| = x³`) → Lemma-2
(`lemma2Hom`, regular change, `|det| = 1`) → step-2 (`{E,F0,δ}`-pivot blow-up, `|det| = s²`) →
[`δ`-branch: step-3 (4-block blow-up, `|det| = u³`)]. 8 unit leaves + 16 block leaves = 24.

This file is built incrementally (each node factorization a committable sub-lemma). Currently:
`myF222` + the step-1 A-pivot factorization (`myF222 ∘ φ₁ = x² · Q`).
-/

open MeasureTheory
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

/-- The explicit `(2,2,2)` loss in flat coordinates `(a00,a01,a10,a11,b00,b01,b10,b11) = (x0,…,x7)`:
`myF222 = ‖A·B‖²` for `A = [[x0,x1],[x2,x3]]`, `B = [[x4,x5],[x6,x7]]`. The function whose RLCT the
cover computes; the seam (`rlctAtOn_dlnLoss222_transport`) identifies `dlnLoss H222 0 = myF222 ∘ e222`.
-/
noncomputable def myF222 (x : Fin 8 → ℝ) : ℝ :=
  (x 0 * x 4 + x 1 * x 6) ^ 2 + (x 0 * x 5 + x 1 * x 7) ^ 2
    + (x 2 * x 4 + x 3 * x 6) ^ 2 + (x 2 * x 5 + x 3 * x 7) ^ 2

/-- **Step-1 A-pivot chart** `φ₁` (pivot `a00 = y0`): `a00 = y0`, `a01 = y0·y1`, `a10 = y0·y2`,
`a11 = y0·y3`; `B` (slots `4..7`) passes through. The blow-up of the `A`-block along the `a00`
direction (Jacobian `y0³`). -/
noncomputable def step1A (y : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![y 0, y 0 * y 1, y 0 * y 2, y 0 * y 3, y 4, y 5, y 6, y 7]

/-- **Step-1 factorization.** Pulling `myF222` back through the A-pivot chart factors out the pivot
square: `myF222 (φ₁ y) = y0² · Q(y)`, where `Q = ‖Â·B‖²` (`Â = [[1,y1],[y2,y3]]`) is the residual the
Lemma-2 node resolves. The `y0`-exceptional divisor (`k = 1`, `h = 3` after the `³`-Jacobian; axis
ratio `2`). Pure algebra (`ring` after the chart substitution). -/
theorem myF222_step1A (y : Fin 8 → ℝ) :
    myF222 (step1A y)
      = (y 0) ^ 2 * ((y 4 + y 1 * y 6) ^ 2 + (y 5 + y 1 * y 7) ^ 2
          + (y 2 * y 4 + y 3 * y 6) ^ 2 + (y 2 * y 5 + y 3 * y 7) ^ 2) := by
  unfold myF222 step1A
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
    Fin.isValue]
  ring

/-- The step-1 residual `Q = ‖Â·B‖²` on the seven non-pivot coordinates `(t1,t2,t3,b00,b01,b10,b11) =
(v0..v6)`: `(b00+t1·b10)² + (b01+t1·b11)² + (t2·b00+t3·b10)² + (t2·b01+t3·b11)²`. The factor the
Lemma-2 node resolves (the `Q` bracket in `myF222_step1A`, reindexed `y1..y7 ↦ v0..v6`). -/
noncomputable def step1Residual (v : Fin 7 → ℝ) : ℝ :=
  (v 3 + v 0 * v 5) ^ 2 + (v 4 + v 0 * v 6) ^ 2
    + (v 1 * v 3 + v 2 * v 5) ^ 2 + (v 1 * v 4 + v 2 * v 6) ^ 2

/-- The resolved quadratic on the Lemma-2 output coordinates `(t1,E,F0,δ,q,G,H)` (slots `0..6`):
`E² + F0² + (q·E + δ·G)² + (q·F0 + δ·H)²` — the normal form whose vertex `{E=F0=δ=0}` step-2 blows
up. -/
noncomputable def resolvedForm (w : Fin 7 → ℝ) : ℝ :=
  (w 1) ^ 2 + (w 2) ^ 2 + (w 4 * w 1 + w 3 * w 5) ^ 2 + (w 4 * w 2 + w 3 * w 6) ^ 2

/-- **Lemma-2 resolution (the regular-change identity).** The step-1 residual `Q` equals the resolved
form read in the Lemma-2 coordinates: `step1Residual v = resolvedForm (lemma2Fwd v)`. This is the
det-(`−1`) regular change of variables (sympy-verified, `r1_222_lemma2_explicit.py`); pure algebra
(`ring`). Since `lemma2Hom` is a measure-preserving homeomorphism (`measurePreserving_lemma2Hom`), the
residual integral transports across it — the splice between step-1 and step-2 (at the lintegral level,
NOT an `rlctAtOn` transport). -/
theorem step1Residual_eq_resolvedForm (v : Fin 7 → ℝ) :
    step1Residual v = resolvedForm (lemma2Fwd v) := by
  unfold step1Residual resolvedForm lemma2Fwd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- **Step-2 E-pivot chart** `φ₂` (pivot `E = z1`): `E = z1`, `F0 = z1·z2`, `δ = z1·z3`; `q, G, H`
(slots `0,4,5,6`) pass through. The blow-up of the resolved form's vertex `{E=F0=δ=0}` along the `E`
direction (Jacobian `z1²`). The `E`/`F0`-pivot branches give UNIT leaves; the `δ`-pivot branch needs
step-3. -/
noncomputable def step2E (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![z 0, z 1, z 1 * z 2, z 1 * z 3, z 4, z 5, z 6]

/-- **Step-2 E-pivot factorization (the UNIT leaf).** Pulling the resolved form through the E-pivot
chart factors out the pivot square against a **unit**: `resolvedForm (φ₂ z) = z1² · U`, where
`U = 1 + z2² + (q + δ̂·G)² + (q·v + δ̂·H)²` (here `z2 = F0/E`, `z3 = δ/E`, `z4 = q`, …) satisfies
`U ≥ 1 > 0` everywhere (a sum of `1` and squares) — so the leaf integrand is `monomial · unit` with
`|unit|` bounded below by `1`, feeding `integrableOn_monomial_mul_unit_iff` (the `0 < a` hypothesis,
`a = 1`). The `z1`-exceptional divisor (`k = 1`, `h = 2` after the `²`-Jacobian; axis ratio `3/2` —
the binding divisor). Pure algebra (`ring`). -/
theorem resolvedForm_step2E (z : Fin 7 → ℝ) :
    resolvedForm (step2E z)
      = (z 1) ^ 2 * (1 + (z 2) ^ 2 + (z 4 + z 3 * z 5) ^ 2 + (z 4 * z 2 + z 3 * z 6) ^ 2) := by
  unfold resolvedForm step2E
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- The step-2 E-pivot residual `U = 1 + z2² + (q+δ̂G)² + (qv+δ̂H)²` is `≥ 1`, hence bounded below by a
positive constant (`a = 1`) — the unit-leaf nonvanishing input to `integrableOn_monomial_mul_unit_iff`.
-/
theorem step2E_unit_ge_one (z : Fin 7 → ℝ) :
    (1 : ℝ) ≤ 1 + (z 2) ^ 2 + (z 4 + z 3 * z 5) ^ 2 + (z 4 * z 2 + z 3 * z 6) ^ 2 := by
  nlinarith [sq_nonneg (z 2), sq_nonneg (z 4 + z 3 * z 5), sq_nonneg (z 4 * z 2 + z 3 * z 6)]

end DLNFibre.DLN.RLCT
