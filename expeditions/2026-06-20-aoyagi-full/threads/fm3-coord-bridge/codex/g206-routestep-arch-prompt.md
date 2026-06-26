<task>
I am a Lean4+Mathlib formaliser on a research project formalising the RLCT (real
log-canonical threshold) of deep linear networks. I need an architecture/scoping
red-team on a multi-step grind, BEFORE I sink compute. You are a decorrelated
second opinion; I have a detailed design cert from a pen-and-paper colleague but
no Lean-ready construction for the general case.

## The setting (precise)

A "width vector" is `M : Fin (L+1) → ℕ` with `∀ s, 0 < M s` (call it hMid).
`dlnLoss M 0 : Params M → ℝ` is a sum-of-squares polynomial loss; `Params M` is a
product of matrix spaces, flat dimension `flatDim M = Σ_s M(s)·M(s+1)`.
The deepest point is the all-zero tuple. Target headline:
`rlctAtOn (flat dlnLoss M 0) 0 = ⨅_i monomialThreshold (d i)(k i)(h i) = ½·minAdm(M)`
where `minAdm(M) = ((Adm M).inf' Mval).toNat`, `Adm M ⊂ (Fin L → ℕ)` a finite
admissible cone, `Mval M T : ℤ` an explicit quadratic form.

## What is BANKED (sorry-free, committed)

VALUE SIDE (fully done, RouteMState.lean):
- `MonoData = {d, k : Fin d→ℕ, h : Fin d→ℕ}`; `appendDivisor md c` snocs axis (1, c−1);
  `foldDivisors cs` folds appendDivisor over a codim-list `cs : List ℕ`.
- `monomialThreshold (foldDivisors cs) = ratioMinFold cs = min over cs of (c/2)`.
- `foldFamily_threshold_ge_of_pivotWitness` (C≥) + `foldFamily_achiever` (C=∃):
  given every leaf's codim-list is built from `PivotWitness M c = {T, hAdm:T∈Adm M,
  hCodim: c=(Mval M T).toNat}`, and one minimiser leaf has m₀=minAdm in its list,
  the family realises ⨅ = ½·minAdm. So the VALUE side reduces to: a finite leaf
  family `ι` (Fintype, Nonempty) + per-leaf codim-lists from PivotWitnesses.

RECURSION SKELETON (route-checked green, 1 sorry = routeStep):
- `ChainDimSplit M = {drop, red : Fin(L+1)→ℕ, hsum: drop+red=M, hdrops: 0<Σdrop}`.
  Raw width-split carrier. `redM_widthSum_lt : Σ red < Σ M` (termination measure).
- `RouteStep M = leaf (md:MonoData) | branch (cells:Type)(Fintype)(Nonempty)
  (split:cells→ChainDimSplit M)(codim:cells→ℕ)(witness:(c)→PivotWitness M (codim c))`.
- `routeStep M : RouteStep M := sorry`  ← THE GATE.
- `routeAtlas = WellFounded.fix` on Σred<ΣM: leaf↦PUnit chart; branch↦Σ over cells of
  (recurse on (split c).red), each child MonoData getting appendDivisor (codim c).
  Produces `routeMIota M` (Fintype, Nonempty), `routeD/K/H M`.
  CRITICAL: routeAtlas only READS `split c` (to recurse on `.red`) + `codim c` + leaf md;
  the witness is carried but unused by the atlas itself (feeds the value/cover facts).
  So `split.red` and the witness `T` are LOGICALLY DECOUPLED in the type — nothing
  forces `split.red` to be the "Schur-reduction of resolving stratum T".

(2,2,2) ANCHOR (the only concrete worked case, Case222*.lean, ~2000 lines):
- A bespoke proof gives `rlctAtOn myF222 0 = 3/2` where `myF222 : (Fin 8→ℝ)→ℝ` is a
  hand-written flat polynomial and `dlnLoss H222 0 = myF222 ∘ e222`. The proof is a
  3-deep hand-built pivotBlowupOn recursion landing 24 leaves, each threshold 3/2.
  IMPORTANT: it goes STRAIGHT to the rlctAtOn value; it does NOT produce the
  `IsRouteMCover` packaging (the Σ-over-leaves ∫ monomialIntegrand inequalities below).

## What I must DELIVER (consumed by a bridge `routeM_rlctAtOn_eq_iInf`, landed sorry-free)

The bridge takes `IsRouteMCover F U ι d k h` (a Prop) and gives
`rlctAtOn F 0 = ⨅_i monomialThreshold (d i)(k i)(h i)`. `IsRouteMCover` fields:
- `Fmeas : Measurable F`, `Uopen : IsOpen U`, `Umem : 0 ∈ U`,
- `cover_le : ∀ c':NNReal, ∃ C:ℝ≥0∞, C<⊤ ∧ ∫⁻_U ofReal(|F x|^(-c')) ≤
   C * Σ_i ∫⁻_{unitBox(d i)} ofReal(monomialIntegrand (d i)(k i)(h i) c')`,
- `cover_ge_div : ∀ c', (∃ i, monomialThreshold(d i)(k i)(h i) ≤ c') →
   ∀ Ω open ∋0, ¬IntegrableOn (|F|^(-c')·1) Ω`.
Here F = flat dlnLoss M 0, U = bounded open box ∋ 0, ι/d/k/h = routeMIota/D/K/H M.

Banked CoV atoms for cover_le: `node_loss_pivot_factor` (core∘pivotBlowup = x_p²·residual),
`node_jacobian_det` ((x_p)^{card−1}), `integrableOn_monomial_mul_unit_iff` (fold a^{−c'}),
`integrableOn_Icc_symm_of_even` (fold 2^d), argmaxCellOn cover/aedisjoint (atlas).

## The two GATES and my open question

GATE 1 (routeStep, general M): produce leaf|branch with CERTIFIED PivotWitnesses for
ARBITRARY M (hMid). The cert says: LEAF iff residual core is a UNIT; else branch on a
pivotBlowupOn with split.red = "schurState" = (M_0−1, M_1−1, M_{≥2}), witness T from
rank-descent. But "schurState"/"residualCore" have NO Lean def; and split.red is
decoupled from the witness T in the type. A prior Codex pass already flagged the
"vacuity trap": a routeStep returning ARBITRARY splits type-checks and produces SOME
(d,k,h) but disconnected from dlnLoss — strictly worse than sorry IF used as a resolution.
BUT: the cover_le/cover_ge_div facts (GATE 2) are what actually tie (d,k,h) to dlnLoss;
the value facts only need the PivotWitnesses (pure Adm/Mval combinatorics, already banked).

GATE 2 (cover_le, general M): the Σ-over-leaves integral inequality. NO banked precedent
even for (2,2,2) (Case222 bypassed IsRouteMCover, went straight to rlctAtOn). This is the
analytic heart: compose per-node light pullbacks down the resolution tree at the lintegral
level + det-1 MP change-of-variables → land each leaf's monomialIntegrand, fold a^{−c'}·2^d
into C. For GENERAL M this requires a recursion matching routeAtlas's WellFounded.fix.

THE MILESTONE my controller set: the (2,2,2) `IsRouteMCover` instance green (unblocks the
end-to-end packaging). NOT the general case necessarily.
</task>

<output_contract>
Answer in 4 sections, terse, decision-oriented:

1. SCOPING VERDICT. Should I (A) build the fully general routeStep + general cover_le,
   or (B) build a concrete (2,2,2) routeStep + (2,2,2) cover_le first as the anchor, or
   (C) something else? Rank by expected-value-per-unit-risk. State the single biggest
   risk of each.

2. THE routeStep DECOUPLING. Given split.red is decoupled from witness T in the type,
   and routeAtlas only recurses on split.red while the value facts only read codim+witness:
   is it SOUND to define a general routeStep where (i) split.red is a simple
   ΣM-decreasing decrement (e.g. decrement the largest interior width by 1) chosen ONLY
   for termination, and (ii) the witness T + codim carry the genuine Adm/Mval content?
   Or does this manufacture a misleading object (the vacuity trap) EVEN THOUGH the
   value facts are honest and cover_le is the thing that ties (d,k,h) to dlnLoss?
   Decisive yes/no + the one-line reason. If no, what is the minimal HONEST general
   routeStep (do I need to define schurState as a Lean def and prove split.red=schurState
   factors the loss)?

3. cover_le REACHABILITY for (2,2,2). Given Case222 already proves rlctAtOn myF222 0 = 3/2
   via a bespoke 24-leaf recursion that does NOT produce the Σ∫ monomialIntegrand form:
   is the (2,2,2) IsRouteMCover.cover_le reachable by (a) re-deriving the Σ∫ bound from
   the existing leaf machinery, (b) a fresh direct proof, or (c) is there a slicker route
   — e.g. can cover_le be DERIVED from rlctAtOn=3/2 + finiteness, sidestepping the explicit
   Σ∫? (rlctAtOn F 0 = sup of c' with ∫_U|F|^{-c'}<⊤ for some U; cover_le is a finiteness
   bound.) Flag if cover_le as stated genuinely requires the explicit leaf-sum or if a
   weaker single-∫ finiteness suffices for the bridge.

4. ORDER. The 3 cheapest-first concrete Lean sub-tasks to attempt, in order, with the
   single discriminating check for each (what tells me it's working vs walling).
</output_contract>

<grounding_rules>
- Distinguish what you can VERIFY from the description vs what is INFERENCE — tag inferences.
- The bridge signature + IsRouteMCover fields are GROUND TRUTH (I pasted them verbatim).
- Do NOT propose reopening the value-side (banked sorry-free). Do NOT propose changing the
  bridge (landed sorry-free, owned by another agent).
- If you cannot determine cover_le reachability without seeing the rlctAtOn definition,
  say so and state what you'd need.
</grounding_rules>
