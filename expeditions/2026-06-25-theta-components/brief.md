# Expedition — the θ / top-component side (`theta-components`)

**Branch:** `expedition/theta-components` (off `dev`).  **Opened:** 2026-06-25.  **Controller:** main session.
Successor to the codim hero expedition (`fibre-codim`): that one resolved the **dimension** of the fibre
(`codim = C+δ`, zero-cite); this one resolves the **components** — the order θ and the rest of Lemma 4.6.

## Central question

Resolve the **order θ** and the **full bundle content of Lemma 4.6 (scope B)** for the DLN multiplication
fibre, to bedrock:

1. **The two θ's diverge — which is "the order"?** Aoyagi's order `θ = a(ℓ−a)+1` (the SLT pole-multiplicity)
   and the LR / Lean component-count `θ = C(m,|δ|) = cTheta = #top-dimensional irreducible components`
   **disagree for `|δ| ≥ 2`** — smallest witness **`(2,2,2,2,2)`, r=0: 5 vs 6** — agreeing only for `|δ| ≤ 1`
   (hence `(3,3,3)` = 2 looked fine). Adjudicate: same invariant or genuinely different (geometric component
   count vs SLT order)? Which appears in the free-energy `(θ−1)·loglog n` asymptotics, and is one of the
   published θ's imprecise about which it is? **Closes #54.**

2. **The component geometry (the backbone).** Establish the top-dimensional irreducible components of
   `mult⁻¹(B)` (and `Σ^r`) and their **bijection** with the Kostant / rank-pattern data — the object the
   count rests on.

3. **Full Lemma 4.6 (B).** The **local-trivial bundle** `mult⁻¹(B) → Mat^{=r}` (base dim δ, fibre the C-part)
   + **smoothness** of the strata. **Design goal:** this bundle should *consolidate* codim + θ + smoothness as
   corollaries, and may **retire the codim expedition's hand-built radical-insensitive trivialization** —
   promoting `Core.ChartLocalizedAlgEquiv.e` from a codim-only tool to a genuine bundle chart — at the cost of
   **climbing the reducedness wall (R2-3b) the codim expedition deliberately routed around**. Whether it fully
   subsumes the hand-build or `e` stays a load-bearing lemma is for the expedition to find.

## Bar (bedrock; zero-cite for the geometry — same as codim)

- Geometric θ (component count), the bijection, the bundle, and smoothness: all **Proved**, axiom-clean
  (`[propext, Classical.choice, Quot.sound]`), **no Cited interface**.
- The **only** citation/openness allowed is the relationship between the geometric θ and Aoyagi's SLT-order θ
  (the divergence). Handle it with **precision**: prove the geometric θ; *clarify, do not conflate*, its
  relation to the SLT order. A `theta_…` result names exactly the θ it proves — never call the component count
  "the SLT order" if they differ.

## First thread (start here)

**pen-and-paper, decorrelated** — adjudicate what each θ *measures* and the `(2,2,2,2,2)` 5-vs-6. Get both
definitions dead-right from the two sources (Aoyagi Thm 1: `θ = max_u Card{j : (h_j+1)/(2k_j) = λ}`; LR: the
top-component count). Determine same-invariant-or-not; report the **structure and ideas** observed (per the
refined `pen-and-paper` role) and hand the controller a certificate. The controller synthesizes the Lean route.

## Closing criterion

The order θ is resolved (which invariant is which; the divergence understood and, if they differ, both named
honestly); the top-component geometry + local-trivial bundle + smoothness of Lemma 4.6 are **Proved zero-cite**
in Lean; #54 closed; the codim hand-build consolidated-or-explicitly-kept. Synthesis written; PR into `dev`
(operator-gated).

## Carried context

- **Predecessor:** `expeditions/2026-06-23-fibre-codim/synthesis.md`.
- **Engine to build on:** `Core.CTheta*` (`cTheta`, `qipM`/`qipS`/`qipDelta`, `numTop_eq_ncard_topComponents`
  — θ = #top components, PROVED), `Core.SigmaCodim`, `Core.FibreCodimFinal`,
  `Core.ChartLocalizedAlgEquiv` / `Core.FibreNormalForm` (the hand-built trivialization to consolidate),
  `DLN.Aoyagi.ClosedForm` (`paperEll`, `paperLambda`).
- **Universe lift** folded into this branch (ROADMAP) — low priority, do not block on it.
- **Verification scripts:** `expeditions/2026-06-23-fibre-codim/{aoyagi_check,paperell_check}.py`; the
  θ-divergence sweep (Aoyagi `a(ℓ−a)+1` vs `C(m,|δ|)`) is the kickoff certificate to reproduce + extend.
