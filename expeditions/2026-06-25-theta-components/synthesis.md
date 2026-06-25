# Synthesis — `theta-components` expedition

Successor to the codim hero expedition. Central question: the order **θ** + the full bundle content of
**Lemma 4.6 (scope B)**, to bedrock. Opened 2026-06-25.

## Status: kickoff threads returned (2 decorrelated certificates + controller assessment)

### Headline (RESOLVED, thread 03 + controller-verified): three distinct θ-invariants; Aoyagi correct; LR's printed rlcm off by one

Thread 01 (witness seat) reached a CANDIDATE "Aoyagi erred" verdict; thread 03 (obstruction seat,
decorrelated + Codex) **REFUTED it**, and the controller verified the key claim against LR `main.tex`. (The
decorrelated dialectic worked exactly as intended — the confident headline was wrong; the skeptical seat
caught it.) Settled picture — **three distinct invariants**, agreeing iff `|δ|≤1`, diverging for `|δ|≥2`
(witness `(2,2,2,2,2)` r=0):

| invariant | formula | what it is | (2,2,2,2,2) r=0 |
|---|---|---|---|
| `cTheta` (Lean / LR `k`) | `C(m,\|δ\|)` | # top-dim irreducible components | 6 ✓ correct |
| rlcm / pole order (Aoyagi) | `a(ℓ−a)+1` | the SLT multiplicity | 5 ✓ correct |
| LR's *printed* rlcm (`:1895`) | `a(ℓ−a)` | = θ−1, the log-log coefficient | 4 ✗ off by one |

- **Aoyagi (2023) is NOT in error.** `a(ℓ−a)+1` is the genuine pole order — internally consistent (Thm 1 /
  Thm 2 / equal-width Example agree) and cross-checked against the peer-reviewed Aoyagi–Watanabe (2005)
  reduced-rank-regression multiplicity (1127 cases, 0 mismatch).
- **`cTheta = C(m,|δ|)` is correct as a component count.** LR's own Remark (`:1934`) says there is "no simple
  relationship" between rlcm and the component count `k` — so #components ≠ the order; genuinely different
  invariants (general counterexample `F=xy(x−y)`: 3 components, pole order 1).
- **LR's *printed* rlcm (`:1895`) is off by one.** LR define (`:1808`) `rlcm ∈ ℕ` = the order of the largest
  pole (≥1), but the printed `m²{S̃/m}(1−{S̃/m})` = `a(ℓ−a)` is **0 at `|δ|=0`** — impossible for a pole
  order. The correct rlcm, by their own definition, is `a(ℓ−a)+1` = Aoyagi's; the printed expression is the
  log-log coefficient θ−1. **Controller-verified against the source** (certificate-strength via the
  definition-vs-formula contradiction; pinpointing the dropped `+1` in their resolution proof is the one open
  sub-question).
- **The `rlct = codim/2` (λ) story is UNAFFECTED** — λ agrees exactly; this touches only the secondary
  multiplicity. **This resolves #54:** the Lean `cTheta` is the correct component count; the "θ" confusion
  was conflating the component count with the pole order.

### Build terrain (thread 02, scout)

- **Σ̄^r θ-count AND component↔Kostant bijection: PROVED unconditionally** (`numTop_eq_ncard_topComponents`,
  `bijOn_partitionIdeal_topComponents`, `≃o` to Mathlib `irreducibleComponents`). BEDROCK.
- **The new content = the FIBRE `mult⁻¹(B)` θ** (for B≠0 the fibre isn't `G_d`-stable; orbit machinery
  doesn't transfer directly). Two routes:
  - **(A) cheap** — transport the proved Σ̄^r bijection through the existing chart `e` via
    `orderIsoOfPrime` (minimal primes survive localization; reducedness NOT needed for *counting*).
    **Kill-condition:** every top-dim component of `mult⁻¹(E)` meets the `{detΔ≠0}` pivot chart ⟹ fibre-θ ≈
    1–3 light lemmas, the reducedness wall is OFF the θ path.
  - **(B) full reduced bundle** — needs the reducedness wall (R2-3b, `fibreGenIdeal` radical; certified
    true thread 16, Lean-unproven, ≥2-module AG sub-project) + a hand-built scheme bundle API (no Mathlib
    `FiberBundle` at scheme level) + smoothness (GLOBAL smoothness is FALSE — fibre singular at E; only
    generic/per-chart).
- **Decisive next computation (commissioned, thread 04):** primary-decompose `fibreGenIdeal` on
  `(2,2,2),r=1`, `(2,2,2,2),r=1`; per top-dim component test `detΔ` non-zero-divisor ⟹ does fibre-θ need the wall?

## Strategic read (controller)

The expedition has three separable pieces, in rough dependency/value order:
1. **Fibre θ-count + bijection (scope-2 backbone)** — likely **cheap via the (A) decoupling** (transport
   through `e`), avoiding the reducedness wall *if* the kill-condition holds. High-value, near-term.
2. **The θ-formula findings (RESOLVED)** — a precision contribution: (i) `cTheta`/component count and the
   rlcm/pole order are *distinct* invariants (formalise both, named distinctly — never conflate); (ii) LR's
   *printed* rlcm is off by one (correct rlcm = `a(ℓ−a)+1`). Does not touch the codim/λ results. #54 resolved.
3. **The full bundle + smoothness (scope-3, "rest of Lemma 4.6 B")** — the heavy lift: reducedness wall +
   hand-built bundle + smooth-locus scoping. This is where the consolidation design goal lives; it is a
   **strict scope increase, not a free consolidation** — `e` likely stays a load-bearing lemma.

Sequencing: the θ-formula question is settled (above). The (A) kill-condition (thread 04) decides whether the
fibre-θ backbone is cheap; then the bundle/smoothness heavy lift. The off-by-one warrants surfacing to the
operator (a precision finding on the paper being formalised — possible erratum/correspondence; operator call).

## Threads
- **01** θ adjudication (pen-and-paper) — DONE; certificate `threads/01-theta-adjudication/findings.md`.
  (Candidate verdict "Aoyagi erred" — REFUTED by thread 03.)
- **02** terrain map (scout) — DONE; `threads/02-terrain-map/findings.md`.
- **03** H1-vs-H2 stress-test (pen-and-paper, obstruction) — DONE; H1 REFUTED, three distinct invariants, LR
  printed rlcm off-by-one (controller-verified vs `main.tex`). Certificate `threads/03-theta-h1-h2/findings.md`.
- **04** (A)-decoupling kill-condition + `fibreGenIdeal` primary decomposition — DONE; **kill-condition HOLDS
  (`detΔ ≡ 1` on the whole fibre, a one-line definitional fact)** ⟹ Route A open, reducedness wall OFF the θ
  path. Fibre #top = `cTheta(d−r) = C(m,|δ|)` verified on 6 Singular cases. Certificate
  `threads/04-fibre-theta-route/findings.md`.

## The fibre-θ build plan (Route A — de-risked, next tide)

1. **`detΔ_unit_on_fibre`** — `detΔ − 1 ∈ fibreGenIdeal` (one-liner: `mem_fibre` + `chartΔ_normalForm`;
   general — any `d`, `r`, ring). The entry lemma.
2. **Transport** the PROVED Σ̄^r bijection `bijOn_partitionIdeal_topComponents` through the chart `e`
   (`Core.ChartLocalizedAlgEquiv`) via `IsLocalization.orderIsoOfPrime` — reducedness-free, since `detΔ` is a
   unit on `O(fibre)`. Gives: fibre top-components ↔ Σ^r top-components.
3. **Shift-width identity** `numTop(fibre d E_r) = cTheta(d−r)` — grounded in the PROVED
   `numTop_eq_ncard_topComponents` (Σ̄^r) + the block-triangular shift (rank-`r` fibre ≅ affine stratum ×
   zero-product locus of `d−r`; the affine factor adds no components). The one substantive input — check if the
   engine already has a `numTop` rank-shift (analogous to the proved `cCodim d r = cValue(d−r)`); if not, it is
   LR Lemma 4.5, a named input (commission a pen-and-paper cert if it blocks the tide).

After the fibre-θ count + bijection land (scope-2 backbone): the **heavy lift** — the full reduced bundle +
smoothness (scope-3, "rest of Lemma 4.6 B"), which DOES need the reducedness wall (R2-3b) + a hand-built scheme
bundle + smooth-locus scoping.
