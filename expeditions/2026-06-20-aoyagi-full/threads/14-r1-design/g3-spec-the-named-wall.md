# G3 — the one named obstruction (general-M flag-resolution): the roadmap spec

- **Seat:** `pp` (design). The "name the result for what it is" deliverable. G3 is the SINGLE wall
  between the fixed-M ladder and the all-M headline; everything else is settled (lower bound) or
  buildable (G5-abstract, the ladder rungs).

## Name it precisely (what G3 is NOT, and IS)

G3 is **NOT** "resolution of singularities in general" (Hironaka — vastly bigger, not what's needed).
G3 **IS** the EXPLICIT, COMBINATORIAL flag-resolution of the SPECIFIC variety `{∏C=0}` (the
zero-product locus of a matrix chain), recursive over the nested-rank stratification — built as explicit
polynomial charts (route-A-concrete, NO abstract blow-up machinery).

## What G3 claims (the precise statement)

For every dimension vector `M = (M¹,…,M^{L+1})`, there is a FINITE ROSE TREE of explicit polynomial
charts `{φ_node : ℝ^N → ℝ^N}` resolving `F = ‖∏C‖²` at the origin, with:
- **(G3.1)** each non-leaf node blows up a COORDINATE-SUBSPACE center = the in-chart image of a
  nested-rank stratum `S(t)`, `t` admissible (`t_L=0`), codim `Mval(t)`.
- **(G3.2)** the in-chart pullback re-identifies as `F_node = (monomial in exceptionals) × ‖∏C'‖²` for a
  STRICTLY SMALLER residual chain `∏C'` (the strict-transform / Schur-complement core) — **the
  recursion-closing step.**
- **(G3.3)** leaves are monomial×unit (Option A) or monomial×smooth-block (Option B) — recursion bottoms.
- **(G3.4)** the leaves' images cover a nbhd of `{∏C=0}` up to null (feeds G5).
- **(G3.5)** along the branch to `S(t)`, the binding divisor has `(k,h) = (1, Mval(t)−1)`.

CONSEQUENCE (with G5-abstract + S2): `rlctAt(F) = ⨅_leaves monomialThreshold = ½·min_Adm Mval =
lambdaCore`.

## The load-bearing hard part = G3.2 (everything else is designed/done)

| piece | status |
|-------|--------|
| G3.1 centers = coordinate-subspace strata | DESIGNED (R1.3 ℕ-count + pivot-chart construction) |
| G3.2 strict-transform = smaller chain product | **THE OPEN CRUX** |
| G3.3 leaves bottom out | DESIGNED (Option A/B; A-vs-B verdict) |
| G3.4 cover up to null | DESIGNED (O1/O2/O3; lower bound SETTLED) |
| G3.5 binding ratio (k=1, h=Mval−1) | DONE arith (R1.2a/b) + VALIDATED k=1 (pos-def-real init form) |

**G3.2 stated sharply:** after each pivot blow-up, PROVE the in-chart residual is AGAIN a matrix-chain
product (a smaller chain whose dims are the reduced `M`), so the recursion is well-defined for arbitrary
`M`. This is the "matrix-chain Schur complement is a smaller matrix-chain product" fact, iterated, with
the dimension bookkeeping. Aoyagi proves it on paper (pp.15–21); the GAP is the LEAN construction —
it's CONSTRUCTION/formalization, not open math (the math is settled, decorrelated-sound).

**G3.2 as a PRECISE formalizable lemma (the target for a future tide — checkable, not a paraphrase):**
> Let `C = (C^(1),…,C^(L))`, `C^(s) : M^s × M^{s+1}`. Suppose in a pivot chart the leading `t₁×t₁`
> minor of the partial product is a UNIT (invertible). Then there are UNIMODULAR (unit-determinant,
> polynomial-entry, analytic) row/column changes `Q^(s)` with
> `∏ (Q^(s) C^(s) Q^(s+1)) = [[ E_{t₁} (regular), 0 ], [ 0, ∏ C'^(s) ]]`,
> `C'^(s)` the REDUCED chain of sizes `(M^s − δ_s)×(M^{s+1} − δ_{s+1})` (Schur-reduced widths), and
> `‖∏C − B‖² = ‖regular generators‖² + ‖∏C'‖²` (the additivity split, L2/S1.5).
> ⟹ `rlctAt` reduces to `½·(reg-stratum-dim) + rlctAt(‖∏C'‖²)`; recurse on `C'`.

This IS Aoyagi Theorem 3 (the product reduction) + the chain-Schur recursion. Verified on L=1 (single
matrix: Lemma-2 ⟹ `C ~ diag(C[0,0], Schur)`, the Schur block = the length-1 reduced chain) and threads
through for L≥2. Well-founded: each step `δ > 0` strictly reduces `Σ M^s`; base case = a smooth block
(leaf). NOTE: this REUSES the existing `block_elimination` (L1, #5, DONE) + `product_reduction` (L2)
machinery — G3.2 is their GENERAL-M chained form, so the fixed-M `product_reduction` wiring is the
prototype the tide generalizes. (`/tmp/g32_schur_precise.py`.)

## Why Mathlib lacks it

- No blow-up / strict-transform machinery (no scheme-theoretic or analytic blow-up).
- No determinantal-variety / nested-rank-stratification API.
- No "matrix-chain Schur complement is a smaller matrix-chain product" lemma.
⟹ G3 must be BUILT as explicit polynomial charts + an explicit Schur-complement substitution +
structural recursion on `(L, rank vector)`. No citation route exists that respects the constraints (the
quiver-multiplier-ideal route was rejected — Q4-trap: real-vs-complex + Aoyagi-independence + black-boxes
the content).

## What a dedicated tide builds (the roadmap unit / hero-task)

1. The explicit pivot-chart map `φ` (coordinate-subspace blow-up) as a polynomial `ℝ^N→ℝ^N` + Jacobian.
2. **The Schur-complement lemma (G3.2, the crux):** in a pivot chart, `‖∏C‖² = monomial × ‖∏C'‖²`, `∏C'`
   the reduced chain. Substantial on its own.
3. The recursion: structural recursion assembling the finite tree (terminates — `L` or codim strictly
   drops, O2 a FACT).
4. The cover (G3.4) + binding ratio (G3.5) wired through.
5. Glue with **G5-abstract** (the c-o-v-tree-gluing down-payment, task #52) ⟹ `rlctAt = lambdaCore`.

ESTIMATE: a multi-rung tide; the Schur-product lemma alone is substantial, the recursion + cover wiring
more. This is the **hero-task boundary** flagged to the operator.

## The honest headline shape (name it for what it is)

- **PROVEN (this expedition):** `aoyagi_learning_coefficient` for the validated fixed-M ladder
  ((1,1,1), (2,1,2), (2,2,2)), axiom-clean mod S2; + the general MACHINERY (S1, L1/L2, D1, A1, A2,
  G5-abstract).
- **ROADMAPPED (named open):** **G3** — the general-M flag-resolution construction (G3.2 strict-transform
  the crux), which lifts the fixed-M instances to the all-M headline. The math is settled (Aoyagi + this
  expedition's paper-proofs, decorrelated-sound); the gap is the Lean construction infra.

One well-scoped obstruction, not diffuse difficulty — the cleanest honest roadmap shape.
