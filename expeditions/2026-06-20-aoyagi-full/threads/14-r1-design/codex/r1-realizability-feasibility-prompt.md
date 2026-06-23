<task>
You are red-teaming a feasibility adjudication for a Lean 4 + Mathlib formalisation of a result about
the real-log-canonical-threshold (RLCT, Watanabe's learning coefficient) of deep linear neural
networks. I need a DECORRELATED independent assessment of how hard ONE specific open obligation is.

SETUP (all of this is PROVEN/green in the Lean library unless marked OPEN):

We resolve the RLCT of the singular "core" loss F(A) = ‖C_L · … · C_1‖²_Frobenius at the origin,
where C_s are matrices of shape determined by a width vector M : Fin(L+1) → ℕ (M s = layer-s width,
all reduced widths, so the product is 0 at the origin = the deepest singular point).

The architecture has three SEPARATE levels (do not conflate them):
  (1) ABSTRACT: rlctAtOn F 0 = ⨅_{i : ι} monomialThreshold (d i)(k i)(h i), over a finite chart
      family (ι, d, k, h). This bridge theorem `routeM_rlctAtOn_eq_iInf` is PROVEN, given a structure
      `IsRouteMCover F U ι d k h` (the chart family covers the loss). It needs only [Nonempty ι].
  (2) VALUE: ⨅_i monomialThreshold = (1/2)·minAdm, where minAdm = min over a finite COMBINATORIAL
      cone `Adm M ⊆ (Fin L → ℕ)` of an integer functional `Mval M T` (an explicit quadratic in the
      exponent vector T). There are TWO proven value lemmas in the library:
      (2a) `foldFamily_iInf_eq_half_minAdm` — needs (C≥): a `PivotWitness M c` for EVERY codim c on
           every leaf (PivotWitness c = ∃ T ∈ Adm M, c = (Mval M T).toNat), giving every leaf
           threshold ≥ ½·minAdm; PLUS (C=∃): ONE designated achiever leaf i₀ whose codim-list
           CONTAINS minAdm. That is all — a SINGLE achiever leaf, not full coverage.
      (2b) `resolution_value_of_atlas` — consumes the STRONGER `IsResolutionAtlas` structure with a
           field `stratum_surjective : ∀ T ∈ Adm M, ∃ i, stratum i = T` (FULL surjectivity onto Adm).
  (3) The combinatorial value identity minAdm = ½·(clean closed form) and the achiever T* that
      attains it: PROVEN green (`lambdaCore_eq_clean`, via an explicit balanced-split construction
      `qStar` / a "BG engine"). So a concrete T* ∈ Adm M with Mval M T* = minAdm is CONSTRUCTIBLE.

The recursion that BUILDS the chart family is `routeAtlas`, well-founded on the total width ΣM,
dispatched by:
  `routeStep (M₀ M) : RouteStep M₀ M := sorry`   ← THE ONE OPEN OBLIGATION.
`RouteStep M₀ M` is either `.leaf (md : MonoData)` or `.branch cells split codim witness` where
  - `split : cells → ChainDimSplit M` (a width split drop+red=M, ΣM-decreasing — CONSTRUCTIBLE via
    the proven `schurState M = (M₀−1, M₁−1, M₂, …)`, a det-1 Schur peel),
  - `codim : cells → ℕ`,
  - `witness : (c : cells) → PivotWitness M₀ (codim c)`  (root-anchored at the ORIGINAL M₀).
The per-step descent soundness (G y² = dlnLoss(S.red) 0 ∘ redEmbed, the "strict transform = smaller
core") is a SEPARATE proven lemma `schur_straighten_squeeze_exists`, but it takes the blow-up Schur
PRESENTATION (`hnode`: flatCore w = Σ regular-squares + ‖b·Erow + S·Γ‖², ‖b‖²≤T²) as an EXPLICIT
hypothesis to be supplied by the chart, NOT asserted.

Core (the engine layer) ALSO has, fully proven: the orbit↔Kostant bijection `orbitKostantEquiv`,
`baseChange_normalForm` (every matrix tuple is base-change-equivalent to an interval-direct-sum normal
form pinned by its rank pattern), the Abeasis–Del Fra orbit-CLOSURE order (`boxMoveChain_repClosure_subset`,
`canonicalCoord_mem_repClosure_orbitSet`), and rank-pattern realizability `cMPlus_iff_mem_image` +
`realizer` (every admissible Kostant array is the rank pattern of an explicit tuple). NOTE these Core
decls live over `Tuple`/`RepCoord` (matrix-tuple space), while `Adm`/`Mval`/`PivotWitness` live over the
combinatorial exponent-vector layer `Fin L → ℕ` with NO direct dependence on Core's Tuple/orbit objects.

The concrete (2,2,2) case is DONE end-to-end with a single binding `Unit`/`Fin 1` achiever leaf
(threshold 3/2 = ½·minAdm), via route (2a) — it does NOT use route (2b)/full surjectivity.

THE QUESTION I need adjudicated:
To make `routeStep` honest for GENERAL M (so that `routeAtlas` produces a chart family whose ⨅ equals
½·minAdm and whose rlctAtOn equals it), what is the MINIMAL theorem content actually required, and at
what scale? Specifically:
  Q1. Which value route does the general construction actually need to populate — (2a) achiever-only
      [C≥ for every cell + ONE achiever leaf], or (2b) full `∀ T ∈ Adm, ∃ i` surjectivity? Argue from
      what `routeM_rlctAtOn_eq_iInf`'s ⨅ + le_antisymm logically requires, NOT from which structure
      happens to be in the file. Is full surjectivity strictly STRONGER than what the value needs?
  Q2. For the (C≥) leg — "every blow-up cell's codim c is (Mval M₀ T).toNat for some admissible
      T ∈ Adm M₀" — is this a finite recursion/induction over the Adm cone + the ChainDimSplit
      width-drop bookkeeping (i.e. DLN-combinatorics, formaliser-scale), or does it genuinely require
      invoking Core's orbit-Kostant / orbit-closure theory (i.e. that each geometric blow-up center IS
      an admissible rank stratum, proven via the quiver translation)? Distinguish "the codim BOOKKEEPING
      (c = Mval of SOME admissible T)" from "the GEOMETRIC identification (the center is the rank locus
      cut by exactly Mval equations)".
  Q3. For the achiever leg (C=∃) — given that a concrete T* ∈ Adm with Mval T* = minAdm is already
      constructible (qStar, green), what is the residual to make ONE chart PATH in `routeAtlas` actually
      reach a leaf whose codim-list contains minAdm? Is "reach the minimiser by a legal blow-up path"
      a genuine global surjectivity/coverage theorem, or can the achiever path be CONSTRUCTED directly
      (descend along the specific reduction sequence dictated by T*), making it a path-existence /
      construction rather than a coverage theorem?
  Q4. Net: is general-M `routeStep` realizability IN-REACH from the listed proven machinery (then name
      the missing glue lemmas and estimate their scale: "finite-recursion over Adm, formaliser-weeks"
      vs "needs new Core orbit theory, research-months"), or is there a genuine residual research gap?
      If a gap, state the SINGLE smallest missing theorem precisely and classify it as
      Core-orbit-Kostant-scale vs DLN-chart-combinatorics-scale.
</task>

<output_contract>
Answer Q1, Q2, Q3, Q4 in order, each ≤ 200 words. For Q4 end with one line:
VERDICT: IN-REACH (achiever-only) | IN-REACH (needs full surjectivity) | ROADMAP: <one-sentence minimal missing theorem + scale class>.
Mark every claim as [FACT] (forced by the stated logic) or [INFERENCE] (your judgement). Do not
rubber-stamp; if the achiever-only route has a hidden dependence on full coverage, say so and why.
</output_contract>

<grounding_rules>
You may reason about RLCT/blow-up/quiver-resolution mathematics and Lean formalisation scale. You may
NOT assume any Lean decl exists beyond those I listed as proven. If a step needs a decl I did not list
as proven, flag it as a NEW obligation. The distinction between the combinatorial Adm/Mval layer and
the geometric Core/orbit layer is load-bearing — keep them separate in your answer. Flag inference vs
forced-fact explicitly.
</grounding_rules>
