# Synthesis — `theta-components` expedition

Successor to the codim hero expedition. Central question: the order **θ** + the full bundle content of
**Lemma 4.6 (scope B)**, to bedrock. Opened 2026-06-25.

## Status: kickoff threads returned (2 decorrelated certificates + controller assessment)

### Headline finding (CANDIDATE — under verification): Aoyagi (2023) Thm 2's order formula may be wrong for deep nets

Thread 01 (pen-and-paper, decorrelated + Codex-concurred) adjudicated the two θ's:
- **θ_LR = C(m,|δ|)** (the Lean `cTheta` = #top-dim irreducible components) vs **θ_Aoyagi = a(ℓ−a)+1**.
- They **diverge for |δ|≥2**; agree iff |δ|≤1. Witness **(2,2,2,2,2), r=0: 6 vs 5**, with the component
  count = 6 confirmed by THREE independent ground truths (QIP brute force, Kostant stratification, LR
  closed form). λ (the RLCT) agrees exactly on all differing cases.
- Mechanism: `a(ℓ−a)+1` = first-order (single-transposition) neighborhood of the rounding vertex;
  `C(m,|δ|)` = the full closest-lattice-point set (type-A_m Voronoi). Coincide only through first order.
- Thread-01 verdict: **Aoyagi's formula undercounts — a published arithmetic error**; `C(m,|δ|)` is correct.

**Controller assessment — do NOT bank "Aoyagi erred" yet.** The verdict rests on the dictionary
**"#top-dim components = the SLT pole multiplicity (the order)."** The three ground truths confirm
*#components = 6*; they do not independently confirm the *pole multiplicity = 6* (that step uses the
dictionary). Two live hypotheses survive:
- **H1** — Aoyagi's `a(ℓ−a)+1` is an arithmetic error; the order = #components = `C(m,|δ|)`. *(thread-01)*
- **H2** — the SLT order genuinely = `a(ℓ−a)+1` (Aoyagi correct), and #top-dim components `C(m,|δ|)` is a
  *different, larger* invariant (order ≠ #components for |δ|≥2; LR's "θ" is a geometric count, not the order).

The germ-invariance argument shows the order is *well-defined*; it does not show #components = order — so
H2 is not excluded. **Decisive tests (commissioned, thread 03):** (i) does LR rigorously *prove*
#top-components = the SLT pole multiplicity, or *define* θ := #components? (ii) compute the pole multiplicity
for (2,2,2,2,2) independently of component-counting — ideally via Aoyagi's *own* Thm-1 resolution count
(`θ = max_u Card{j : (h_j+1)/(2k_j)=λ}`, the k_j/h_j). If 6 ⟹ Aoyagi internally inconsistent (H1); if 5 ⟹
H2. Either outcome is a real precision/fidelity result (correct the literature, or distinguish two θ's).

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
2. **The θ-formula finding** — a precision contribution: correct Aoyagi (H1) or distinguish the two θ's
   (H2). Verify first (thread 03); it reshapes how θ is stated, not the codim/λ results.
3. **The full bundle + smoothness (scope-3, "rest of Lemma 4.6 B")** — the heavy lift: reducedness wall +
   hand-built bundle + smooth-locus scoping. This is where the consolidation design goal lives; it is a
   **strict scope increase, not a free consolidation** — `e` likely stays a load-bearing lemma.

Sequencing: resolve H1/H2 (thread 03) + the (A) kill-condition (thread 04) **first** — they decide both the
correct θ statement and whether the backbone is cheap. Then the bundle/smoothness heavy lift.

## Threads
- **01** θ adjudication (pen-and-paper) — DONE; certificate `threads/01-theta-adjudication/findings.md`.
- **02** terrain map (scout) — DONE; `threads/02-terrain-map/findings.md`.
- **03** H1-vs-H2 stress-test (pen-and-paper, obstruction) — launched 2026-06-25.
- **04** (A)-decoupling kill-condition + `fibreGenIdeal` primary decomposition — launched 2026-06-25.
