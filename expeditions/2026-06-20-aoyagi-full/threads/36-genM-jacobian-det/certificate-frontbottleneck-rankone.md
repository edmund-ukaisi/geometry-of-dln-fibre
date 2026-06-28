# Certificate — the FRONT-BOTTLENECK → RANK-ONE-COLUMNS bridge (the ∀M-(1,1)-smeared front fact)

**Seat:** pen-and-paper, WITNESS direction. **Level:** R1-LOWER smeared branch — the front-bottleneck
→ rank-one structural fact feeding the landed `scalarGram_cancel_of_rankOneColumns`. **Date:** 2026-06-28.
**Gate:** exact-rational/symbolic sympy validation over the full 34-case `(1,1)` family (+ 426-case
wider grid) + a DECORRELATED local-Codex consult (`codex/frontrank-{prompt,answer}.md`, LANDED,
independent of `genM11-arch`). BUILD-READY for a formaliser; no Lean committed.

Scripts (durable, re-runnable): `scripts/` + `/tmp/family11_mechanism{,2}.py`,
`/tmp/family11_outer.py`, `/tmp/family11_unify.py`, `/tmp/family11_chart_match.py`,
`/tmp/family_21_12b.py`, `/tmp/verify_codex_correction.py`, `/tmp/wider_grid.py`. (The thread-local
durable copy is in `scripts/`; the `/tmp` ones reproduce on run from the scripts dir's
`witness_tide_validated.py`.)

---

## 0. Headline — the mechanism is a LITERAL `Fin 1` outer product, NOT rank theory

Decisively pinned (sympy 34/34 + Codex independent FACT-verdict): the front product `P` has
rank-one columns because it **factors through a width-1 inner dimension** — `P = U · V` with
`U : Fin m0 × Fin 1` and `V : Fin 1 × Fin m1`, obtained by associativity of the chain product split
at a width-1 layer. The columns of `P` are then `V`-entry-scaled copies of the single column `U`,
proved by the LITERAL outer-product identity

    (U · V) i j = U i 0 · V 0 j        (Matrix.mul_apply + Fin.sum_univ_one).

There is **no `rank(A·B) ≤ min` argument anywhere** — the cleanest Lean target is the `Fin 1`
factorization. (Codex, decorrelated, returns the same verdict (a)-not-(b) as FACT.)

**Codex's load-bearing correction (preserved):** "every column of `P` is a multiple of column `0`"
is FALSE without an off-pole hypothesis. Counterexample `P = [0  1]`: it factors through `Fin 1`
(`U = [1]`, `V = [0, 1]`), but column `1` is not a scalar multiple of column `0 = 0`. The
unconditional factorization gives columns as multiples of the HIDDEN column `U`, not of `P.col 0`.
To normalize to `c₀ = P.col 0` one needs `V 0 0 ≠ 0`, which the consumer's `‖c₀‖² ≠ 0` supplies
exactly (`‖c₀‖² = (V 0 0)² · ‖U‖²`, so `‖c₀‖² ≠ 0 ⟺ V 0 0 ≠ 0 ∧ U ≠ 0`). This matches the landed
lemma's design (it takes `hP₂ : P₂ i j = μ j · c₀ i` as a HYPOTHESIS and `hc : ∑ (c₀ i)² ≠ 0`).

---

## 1. The boundary-smeared point + where the width-1 bottleneck sits (as a function of M)

The chart point (from `certificate-genM-smeared.md` §2; the `(1,1)` slice has `r = Text(L) = 1`,
`c = M_L = 1`, `m1 = M_{L−1}`, `s = m1 − 1`, `minAdm = r·c = 1`, weight-1 so NO radial):

    front  = (A⁰, …, A^{L−2})  free generic,   P := A⁰·A¹···A^{L−2}  (M_0 × m1),
    P₁ := P[:, 0:1]  (the single pivot column),  P₂ := P[:, 1:m1]  (the s = m1−1 residual columns),
    Λ₀ := (P₁ᵀP₁)⁻¹ P₁ᵀ P₂   (1 × s, the SCALAR routing, b/a-form),
    A^{L−1} := [ z·H̄ − Λ₀·S_bot ; S_bot ]   (m1 × 1; H̄ is 1×1 with the (0,0) entry the z-pivot).

The deepest product telescopes (`P₁·Λ₀ = P₂` cancels the shear): `P·A^{L−1} = z·P₁·H̄`, so
`F = z²·‖P₁H̄‖² = z²·U`. The front fact this certificate adjudicates is exactly `P₁·Λ₀ = P₂`,
supplied to the landed `scalarGram_cancel_of_rankOneColumns` via the rank-one-columns form of `P`.

**Where the width-1 layer sits — `p* := first index in {0,…,L−1} with M_{p*} = 1`** (EXACT,
34/34, + wider-grid 426/426, 0 violations of `min(M_0,…,M_{L−1}) = 1`). The `(1,1)` family splits
cleanly into TWO sub-cases by `p*` (and both reduce to the SAME `Fin 1` mechanism):

| sub-case | count | where the bottleneck is | `P` shape | `U`, `V` |
|----------|-------|--------------------------|-----------|----------|
| `M_0 = 1` (`p* = 0`) | 14 | the OUTPUT row count | `1 × m1` (single row) | `U = I₁`, `V = P` |
| inner `M_{p*} = 1`, `M_0 > 1` (`p* ∈ {1,2}`) | 20 | an inner layer | `m0 × m1`, genuine outer product | `U = A⁰···A^{p*−1}` (m0×1), `V = A^{p*}···A^{L−2}` (1×m1) |

`p*`-distribution (L, p*): (2,0):2, (3,0):4, (3,1):4, (4,0):8, (4,1):8, (4,2):8. **`p*` is NEVER
`L−1`** (the smeared condition `r < m1` forces `m1 ≥ 2 > 1 = M_{p*}`, so the bottleneck is never the
LAST front width; the right factor `V` always has ≥ 1 genuine layer). The `p* = 0` corner is handled
uniformly by `U = I₁` (empty prefix product) — no special-casing needed.

---

## 2. The exact statement + ALL hypotheses (the bridge), with `c₀`/`μ` explicit

**Off-pole non-degeneracy:** `hc : (∑ i, (c₀ i)²) ≠ 0` where `c₀ = P.col 0`. Equivalent to
`V 0 0 ≠ 0 ∧ U ≠ 0` (the `1×1` front Gram `P₁ᵀP₁ = ‖c₀‖²` is invertible). This is a Lebesgue-null
hypersurface complement; the chart's `cov`/`leaf_integrand` only see it off the pole (a.e.).

**`c₀` and `μ` in terms of M's coordinates** (verified exact, `/tmp/verify_codex_correction.py`):
from `P = U·V` (`P i j = U i 0 · V 0 j`):

    c₀ i  = P i 0   = (V 0 0) · (U i 0)            (column 0 of P)
    μ j   = (V 0 j) / (V 0 0)                       (so μ 0 = 1)
    P i j = μ j · c₀ i      ⟺  U i 0 · V 0 j = (V 0 j / V 0 0) · (V 0 0) · (U i 0)   ✓ (needs V 0 0 ≠ 0)
    ‖c₀‖² = (V 0 0)² · ∑ i (U i 0)²

For the chart's `P₂` (residual columns `r..m1−1` of `P`, 0-indexed as `j` in `Fin s`): `P₂ i j =
P i (j+1) = μ_{j+1} · c₀ i`, i.e. the consumer's `μ` is `(fun j => V 0 (j+1) / V 0 0)`. EXACT match
to the landed `scalarGram_cancel_of_rankOneColumns` signature, 34/34 (`/tmp/family11_chart_match.py`).

---

## 3. The MINIMAL Lean-targetable bridge lemma (build-ready signature + route)

Two lemmas. The first is GENERIC pure linear algebra (rank-free, short); the second is the cast-heavy
specialization to `P = frontProd M`. **The real cost is the SECOND**, not the Fin-1 algebra (Codex
FACT, corroborated): proving `prod (front widths) (front params) = U · V` after splitting the
left-associated dependent-width `prodAux` at `p*` — that is where `Matrix.reindex` / `finCongr` /
reassociation overhead lives. The `RouteMFrontPeel` kernel (`mul_three_reassoc`, `Atail_apply`,
`prodAux_front_peel`, `reindex_finCongr_mul`, the equiv-level `finCongr_refl` + `reindex_refl_refl`
collapse) is the existing infrastructure for exactly this — the split-at-`p*` is its `k`-fold
generalization (peel `p*` front layers into `U`, leave the rest as `V`).

### 3a. Generic bridge (rank-free; sits beside `scalarGram_cancel_of_rankOneColumns`)

```lean
/-- A matrix that factors through a `Fin 1` inner dimension has, off the pole `‖col 0‖² ≠ 0`,
    rank-one columns normalized to column 0: `P i j = μ j · c₀ i` with `c₀ = P.col 0`, `μ 0 = 1`. -/
theorem rankOneColumns_of_factorsThroughOne
    {rows : Type*} [Fintype rows] {m1 : ℕ} (hm1 : 0 < m1)
    (P : Matrix rows (Fin m1) ℝ)
    (U : Matrix rows (Fin 1) ℝ) (V : Matrix (Fin 1) (Fin m1) ℝ)
    (hP : P = U * V)
    (hc : (∑ i, (P i ⟨0, hm1⟩) ^ 2) ≠ 0) :
    ∃ (c₀ : rows → ℝ) (μ : Fin m1 → ℝ),
      c₀ = (fun i => P i ⟨0, hm1⟩) ∧ μ ⟨0, hm1⟩ = 1 ∧
      ∀ i j, P i j = μ j * c₀ i := by
  refine ⟨fun i => P i ⟨0, hm1⟩, fun j => V 0 j / V 0 ⟨0, hm1⟩, rfl, ?_, ?_⟩
  · -- μ ⟨0,_⟩ = (V 0 0)/(V 0 0) = 1, using V 0 0 ≠ 0 from hc
    sorry
  · intro i j
    -- P i j = U i 0 · V 0 j ; c₀ i = U i 0 · V 0 0 ; div_mul_cancel via V 0 0 ≠ 0
    sorry
```

Proof skeleton (all exact, validated): `hP ▸ Matrix.mul_apply` + `Fin.sum_univ_one` give
`P i j = U i 0 * V 0 j`. From `hc`: `‖c₀‖² = (V 0 ⟨0,_⟩)² · ∑ (U i 0)² ≠ 0`, so `V 0 ⟨0,_⟩ ≠ 0`
(else the sum is 0). Then `μ ⟨0,_⟩ = V 0 ⟨0,_⟩ / V 0 ⟨0,_⟩ = 1` (`div_self`); and
`μ j · c₀ i = (V 0 j / V 0 ⟨0,_⟩) · (U i 0 · V 0 ⟨0,_⟩) = V 0 j · U i 0 = P i j`
(`div_mul_cancel₀` with `V 0 ⟨0,_⟩ ≠ 0`, then `mul_comm`). Mathlib: `Matrix.mul_apply`,
`Fin.sum_univ_one`, `div_self`, `div_mul_cancel₀`, `mul_comm`, `Finset.sum_eq_zero` /
`pow_eq_zero_iff` for the `V 0 0 ≠ 0` extraction.

This composes DIRECTLY with the landed `scalarGram_cancel_of_rankOneColumns`: take its `c₀`, `μ` (the
`μ` restricted to the residual columns), `hc`, `P₁ = P[:, 0:1]`, `P₂ = P[:, 1:]`. The `hP₂` it
demands is exactly the `∀ i j, P i j = μ j · c₀ i` this bridge produces (re-indexed to `P₂`).

### 3b. The cast-heavy specialization `frontProd M = U · V` (the genuine work)

```lean
/-- The front product `frontProd M A := prodAux M A (L−1) …` (size M_0 × M_{L−1}) factors through the
    width-1 layer at `p* = first index with M_{p*} = 1`: `frontProd M A = U * V` with U the prefix
    product A⁰···A^{p*−1} (M_0 × 1) and V the suffix A^{p*}···A^{L−2} (1 × M_{L−1}). -/
theorem frontProd_factorsThroughOne
    (M : Fin (L + 1) → ℕ) (A : Params M) (hL : 2 ≤ L)
    (p : ℕ) (hp : p < L) (hp1 : M ⟨p, by omega⟩ = 1)         -- the width-1 layer
    … (reindex/width equalities) … :
    ∃ (U : Matrix (Fin (M 0)) (Fin 1) ℝ) (V : Matrix (Fin 1) (Fin (M ⟨L-1,_⟩)) ℝ),
      frontProd M A = (reindex …) (U * V)
```

Route: split `prodAux M A (L−1)` at `p` via the `prodAux_front_peel` kernel generalized to peel `p`
prefix layers (the prefix is `prodAux` over the first `p` layers → `M_0 × M_p = M_0 × 1`; the suffix
is the running product from layer `p` → `M_p × M_{L−1} = 1 × M_{L−1}`), then collapse the `Fin (M_p)`
inner type to `Fin 1` via `finCongr hp1` at the equiv level (`finCongr_refl` + `reindex_refl_refl`,
the documented kernel — `lean/CLAUDE.md` "Dependent-dimension matrix reassociation"). The
`mul_three_reassoc` / `reindex_finCongr_mul` handles the reassociation `(prefix · A^p) · suffix =
prefix · (A^p · suffix)` that `rw [Matrix.mul_assoc]` cannot match through dependent widths.

**This is the genuine fresh-infrastructure piece** (the architecture cert §3 residual-1). It is NOT
a parametrization of the `(1,2,1)` template — it is the generic prefix-split of `prodAux` at an
arbitrary width-1 position, reusing the `RouteMFrontPeel` cast kernel. Sizing: comparable to
`prodAux_front_peel` itself (one induction on the prefix length `p`, the same cast bookkeeping).

---

## 4. (2,1) and (1,2) families — extension read

**ALL THREE families use the SAME front-bottleneck mechanism** (factor through `Fin r` at the first
width-`r` position `p*`), differing only in `r` (the inner dimension) and `c` (the radial block).
Verified exact (`/tmp/family_21_12b.py`, 6/6 each + 34/34 for (1,1)):

| family | r | c | front fact | front bridge | NEW vs (1,1) front |
|--------|---|---|------------|--------------|--------------------|
| (1,1) ×34 | 1 | 1 | `P = U·V`, `Fin 1` inner; rank-one COLUMNS | §3 (scalar Gram) | — |
| (1,2) ×6  | 1 | 2 | `P = U·V`, `Fin 1` inner; rank-one COLUMNS | **SAME §3 scalar-Gram bridge** | radial is 1×2 (deepest factor), front fact IDENTICAL |
| (2,1) ×6  | 2 | 1 | `P = U·V`, `Fin 2` inner; cols in span of first 2 | NEEDS a `Fin 2` / 2×2-Gram analogue | rank-2 (`Fin 2` factorization, 2×2 Gram inverse) |

- **(1,2) reuses the §3 scalar-Gram front bridge VERBATIM** (`r = 1`, so the same rank-one-columns
  fact and the same `scalarGram_cancel_of_rankOneColumns`). The `c = 2` changes only the deepest
  factor's column count (the radial block `pivotBlowupOn`), NOT the front. So the recalibration
  (Option-A substrate + front-bottleneck bridge) extends to (1,2) at the front with ZERO new front
  math; the (1,3,2) validate-small already lands the rate (`certificate-genM-smeared-lift-route.md`
  §3).
- **(2,1) needs a `Fin 2` analogue** of §3: `P = U·V` through `Fin 2` (`U : m0×2`, `V : 2×m1`), then
  "columns in span of the first 2" + the 2×2 Gram cancellation `P₁·Λ₀ = P₂` (the (2,3,1) structure,
  already a banked validate-small). The same factor-through-`Fin r` mechanism (split at first
  width-2 position, `p* = 0` ⟹ `U = I₂`), so the GENERIC bridge §3a generalizes to `Fin r`
  (replace `Fin 1` by `Fin r`, the scalar Gram by the `r×r` Gram) — but the (2,1) `scalarGram`
  consumer must be the matrix-Gram lemma, not the landed scalar one. `r ≤ 2` throughout (max), so the
  Gram is at most 2×2.

**Sizing the whole smeared branch:** the front-bottleneck → factor-through-`Fin r` bridge is needed
by ALL THREE families (it is the Option-A substrate's front fact, not a template parametrization).
(1,1) and (1,2) share the scalar (`r=1`) bridge exactly; (2,1) needs the `r=2` Gram analogue. The
recalibration (architecture cert §0 — "the validate-small architecture does NOT generalize; needs the
CLEAN Option-A substrate + a front-bottleneck bridge") EXTENDS to all three families. None is a
genuine fixed-shape template parametrization at the front.

---

## 5. PROVED / TO-BUILD / CITED

- **PROVED (exact + exhaustive):** mechanism = literal `Fin 1` factorization, not rank theory
  (34/34 + Codex FACT); `min(M_0,…,M_{L−1}) = 1` for the (1,1) family (34/34 + 426/426 wider);
  `p* = first width-1 position`, never `L−1` (426/426); `P = U·V` through `Fin 1` at `p*` (34/34);
  `c₀ = (V 0 0)·U`, `μ_j = V 0 j / V 0 0`, `‖c₀‖² = (V 0 0)²‖U‖²` (exact); the chart `P₁/P₂` split
  matches the landed `scalarGram_cancel_of_rankOneColumns` signature (34/34); the off-pole
  hypothesis correctly excludes the `[0 1]` counterexample.
- **TO BUILD (Lean):** (a) `rankOneColumns_of_factorsThroughOne` (§3a, generic, short, rank-free);
  (b) `frontProd_factorsThroughOne` (§3b, the cast-heavy prefix-split of `prodAux` at `p*`, reusing
  the `RouteMFrontPeel` kernel — the genuine fresh infrastructure); (c) wire (a)+(b) into the landed
  `scalarGram_cancel_of_rankOneColumns` for `P₁·Λ₀ = P₂`. For (2,1): the `Fin r`/r×r-Gram analogue.
- **CITED / REUSED:** `scalarGram_cancel_of_rankOneColumns` (LANDED, `RouteMSmearedGenRate.lean`);
  `Matrix.mul_apply`, `Fin.sum_univ_one`, `div_self`, `div_mul_cancel₀` (Mathlib v4.29, all confirmed
  at the pin — the first two already used in `RouteMSmearedGenRate.lean`); the `RouteMFrontPeel`
  cast kernel (`prodAux_front_peel`, `mul_three_reassoc`, `reindex_finCongr_mul`, `Atail_apply`).

**Caveat (next to the claim):** the rank-one-columns fact is `P i j = μ j · c₀ i` with `c₀ = P.col 0`
ONLY off the pole `‖c₀‖² ≠ 0` (Codex's `[0 1]` counterexample). Both the factorization (mechanism)
and the off-pole hypothesis (normalization to column 0) are load-bearing — the unconditional
factorization alone gives columns as multiples of the HIDDEN `U`, not of `P.col 0`.
