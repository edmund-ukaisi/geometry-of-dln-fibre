# Thread 03 — H1-vs-H2 obstruction certificate (+ controller verification)

**Persisted by the controller.** Obstruction seat (commissioned to REFUTE thread 01's "Aoyagi erred").
Decorrelated + Codex-concurred (xhigh). Controller independently verified the load-bearing claim against
LR `main.tex` (see "Controller verification" below).

## Verdict: H1 (thread 01) REFUTED. Three distinct invariants, not two.

| invariant | closed form | what it measures | (2,2,2,2,2) r=0 |
|---|---|---|---|
| **θ_LR = `cTheta`** | `C(m,\|δ\|)` | # top-dim irreducible components of `mult⁻¹(B)` (= # QIP optima) | **6** ✓ |
| **rlcm / SLT pole order** | `a(ℓ−a)+1` (Aoyagi) | order of the largest pole of `ζ_loss` = Watanabe multiplicity | **5** ✓ |
| **LR's *printed* rlcm** | `m²{S̃/m}(1−{S̃/m})` = `a(ℓ−a)` | = θ−1, the log-log coefficient — **off by one** | **4** ✗ |

- **Aoyagi (2023) is NOT in error.** `a(ℓ−a)+1` is the genuine pole order, internally consistent (Thm 1 /
  Thm 2 / the equal-width Example all agree; `(2,2,2,2,2)` r=0 sits in the Example: `ℓ=4, a=2 ⇒ θ=5`).
- **cTheta = C(m,|δ|) is correct as a component count** (thread 01's 3 ground truths stand for *that*).
- **They are genuinely different invariants**; coincide iff `|δ|≤1`.

## Test 1 — LR keep #components and the order separate, and DISCLAIM the identity
- LR's `k` / θ is **defined** as #top-dim irreducible components (`cor:irred_comp` :806; `eqn:number_top_comp`
  :1665). A geometric count, never identified with a pole order.
- LR **separately define** `rlcm` (:1801–1808) as "the **order** of [the largest] pole" of `ζ_F(s)`, ∈ ℕ.
- **Smoking gun — LR Remark `:1934`:** "there is **no simple relationship** between `rlcm = m²{S̃/m}(1−{S̃/m})`
  and the number `k = C(m,|δ|)` of irreducible components." So thread 01's dictionary "#components = order"
  is explicitly NOT LR's claim.

## Test 2 — the pole order for (2,2,2,2,2), independent of component-counting → 5 (= a(ℓ−a)+1), never 6
- **(2a)** Aoyagi internal consistency: her Def 1 order = largest-pole order; Thm 1's resolution count
  `max_u Card{(h_j+1)/(2k_j)=λ}`, Thm 2, and the Example all give `a(ℓ−a)+1`. No internal inconsistency (which
  H1 required).
- **(2b)** Classical **Aoyagi–Watanabe (2005)** reduced-rank-regression multiplicity (peer-reviewed): for
  3-layer/RRR, `a(ℓ−a)+1` reproduces the classical parity-governed order EXACTLY — **0 mismatches over 1127
  cases** (incl. r>0, unbalanced). The order is a small parity integer (1 or 2 in the base case) —
  structurally incompatible with a large binomial `C(m,|δ|)`.
- **Order-≥1 impossibility:** LR's printed `rlcm = a(ℓ−a) = 0` at `|δ|=0`; a pole order is ≥1, so the printed
  formula is impossible there and must be the order *minus one*.
- **Counterexample to the dictionary** (Codex, decorrelated): `F=xy(x−y)` in ℝ² has 3 components through 0 but
  largest pole of order 1. #components ≠ pole order in general.

## Controller verification (against LR `main.tex`, 2026-06-25)
Read the source directly: `:1808` defines `rlcm ∈ ℕ` = the **order of the largest pole**; `:1895` prints
`rlcm(K^DLN_B) = m²{S̃/m}(1−{S̃/m})` (= `a(ℓ−a)`), which is **0 at `|δ|=0`** — contradicting the definition
(order ≥1). `:1934` is the disclaimer. **Conclusion (certificate-strength): LR's printed `rlcm` is off by one
— it is the log-log coefficient θ−1; the correct `rlcm`, by LR's own definition, is `a(ℓ−a)+1` = Aoyagi's.**
(`:1847` `rlcm(F+G)=rlcm(F)+rlcm(G)−1` is the additivity rule whose final `+1` the assembly appears to drop.)

## Consequences (for synthesis)
1. Lean `cTheta = C(m,|δ|)` is correct **as a component count**; do NOT wire `a(ℓ−a)+1` as an alternate cTheta.
2. The SLT order (rlcm) = `a(ℓ−a)+1` (Aoyagi, classically confirmed); if formalised, that is the formula —
   **not** `cTheta`, and **not** LR's printed `m²{S̃/m}(1−{S̃/m})`.
3. **LR's printed rlcm formula is off by one** (= θ−1) — a precision finding about the paper being formalised.
4. The `rlct = codim/2` (λ) story is UNAFFECTED — λ agrees exactly; this touches only the secondary multiplicity.
5. Exposition: keep three names distinct — `theta` (#components, `C(m,|δ|)`), `rlcm`/order (`a(ℓ−a)+1`),
   log-log coefficient θ−1 (`a(ℓ−a)`).

## Open part (below the rest's certainty)
Pinpoint where LR's resolution proof drops the `+1` (or author correspondence) — would upgrade Consequence 3
from "off-by-one (definition + impossibility + exact match)" to "located in the derivation." The conclusion
itself is settled by the definition-vs-printed-formula contradiction.

## Artifacts
- `threads/03-theta-h1-h2/scripts/order_vs_components.py` (crux + systematic +1 + classical-AW 1127-case
  cross-check + order-≥1 impossibility; assertions pass).
- `threads/03-theta-h1-h2/codex/order-vs-components-{prompt,answer}.md` (decorrelated xhigh).
