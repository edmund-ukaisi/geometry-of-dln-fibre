<task>
Lean 4 + Mathlib formalisation. I must prove "conjunct-2" of a theorem (the WALL of the expedition).
I need a STRATEGY: is it provable as stated, and what is the exact algebraic decomposition? Diagnosis,
not Lean code (I build in Lean myself).

## The objects (real Lean defs, paraphrased faithfully; D := flatDim d, a fixed dimension)

Coordinates `u : Fin D → ℝ` decode into LAYERS: each coord i belongs to exactly one layer ℓ(i) ∈ {0..N-1}.
`layerCoords d ℓ` = the coords in layer ℓ. `blockCoords d ℓ` = layer-ℓ coords capped on one axis (⊆ layerCoords d ℓ).

IgnoresCoords c S V  :=  ∀ w∈V, ∀ m∈S, ∀ t, c (update w m t) = c w        -- c does not read S-coords
AffineOn f X V       :=  ∃ a b, IgnoresCoords a X V ∧ (∀x∈X, IgnoresCoords (b x) X V)
                                ∧ ∀u∈V, f u = a u + ∑_{x∈X} b x u · u x    -- total degree ≤1 in X
PerLayerDeg1From d f fromLayer V := ∀ ℓ ≥ fromLayer, AffineOn f (layerCoords d ℓ) V   -- per-layer deg≤1 from a threshold
Deg1SupportedSlot d resid j S fromLayer V :=
    (∃ c, (∀i, ContinuousOn (c i) V) ∧ ∀u∈V, resid j u = ∑_{i∈S} c i u · u i)   -- (A) support-decomp on S (⟹ vanishes at 0)
  ∧ PerLayerDeg1From d (resid j) fromLayer V                                    -- (B) per-layer deg≤1 from fromLayer

The support window (V ≡ univ everywhere, so ignore V):
  supportAt d S J := if J=0 then blockCoords d S else if S+1<N then blockCoords d (S+1) else ∅
  supportLayerOf state := if state.cleared=0 then state.layer else state.layer+1

The step map on a coordinate vector, at an edge `ed` (center : Finset, pivot ∈ center, shearφ, case):
  blockShear φ u          := u + φ u                       -- unipotent, φ 0 = 0, keeps pivot coord: (blockShear φ u) pivot = u pivot
  edgeShear ed            := id (case11/rollover) | blockShear ed.shearφ (case12/case2)
  blockBlowupMap S p w j  := if j=p then w p else if j∈S then w p · w j else w j
  stepMap ed              := blockBlowupMap ed.center ed.pivot ∘ edgeShear ed
  blockBlowupCoordQuot p j w := if j=p then 1 else w j
  qm ed u                 := fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear ed u)   -- pivot↦1, else sheared

The fold residual family `foldResid p : Fin (foldNR p) → (Fin D→ℝ) → ℝ`, recursively:
  root ↦ coreGen (DLN generators: each entry is a CROSS-LAYER PRODUCT, one coord factor per layer, so it
                  vanishes at any point with only one coord nonzero);
  a non-terminal step p→child (child = p.extend ed), with δ := [p.conState.cleared = 0]:
    δ=1 (STRICT TRANSFORM): foldResid child j u = foldResid p (cast j) (qm ed u)
    δ=0 (PULLBACK):         foldResid child j u = foldResid p (cast j) (stepMap ed u)

## The theorem (interior case-1) — I must prove conjunct-2

Hypotheses (ed is a FREE edge — its fields center/pivot/case/nextState/shearφ are arbitrary subject to):
  hcase1  : ed.case ∈ {case11, case12}
  hlayer  : ed.nextState.layer + 1 < N
  hcenter : ed.center ⊆ blockCoords d p.conState.layer                    -- ⊆ (NOT =); pivot ∈ center ⊆ this
  hinv-2  : ∀ j, Deg1SupportedSlot d (foldResid p) j
                    (supportAt d p.conState.layer p.conState.cleared)     -- S_parent
                    (supportLayerOf p.conState)
  hgrade  : ShearGrades ed  — on S' := supportAt d ed.nextState.layer ed.nextState.cleared (the CHILD support):
       ∃ c, (∀i k, ContinuousOn (c i k)) ∧
         (∀ i∈S', ∀u, (blockShear ed.shearφ) u i = ∑_{k∈S'} c i k u · u k)        -- (a) S'-images graded on S'
         ∧ (∀ i k, PerLayerDeg1From d (c i k) (supportLayerOf ed.nextState))       -- coeffs per-layer deg≤1
         ∧ (∀ i∉S', IgnoresCoords (fun u ↦ (blockShear ed.shearφ) u i) S')          -- (b) S'ᶜ-images ignore S'

GOAL (conjunct-2): ∀ j, Deg1SupportedSlot d (foldResid child) j S' (supportLayerOf ed.nextState)
    where child = p.extend ed, S' = supportAt d ed.nextState.layer ed.nextState.cleared.

## Ground truth I have (sympy batteries, all confirmed)
- Interior δ=1: child = foldResid_p(qm u). Concrete model: parent slot = de·s1·e (de∈layer S, s1∈layer S+1, e∈layer S+2),
  shear folds de↦de−be·ga (be,ga∈layer S), giving child = s1·e·(de−be·ga). This VANISHES at 0 (carries s1 factor),
  is deg-1 on S'={s1} (=layer S+1), and PerLayerDeg1 holds from ≥ S+1 but FAILS at layer S (the be·ga is deg-2 there).
  So the threshold ADVANCES S→S+1 with the descend; the cleared layer S drops below-threshold.
- The bare-unit failure (a child entry with a nonzero constant at S'=0) occurs ONLY at S=L (last layer), which
  hlayer excludes (there nextState.layer = N-1 so nextState.layer+1 = N, not < N).

## The load-bearing question
ed.nextState is FREE, so S' = supportAt(ed.nextState) and supportLayerOf(ed.nextState) are computed from a free
state — there is NO hypothesis linking ed.nextState.layer/cleared to p.conState. Yet ShearGrades (hgrade) is
stated on this specific S'. In the CONSTRUCTION, a case-1 clear gives ed.nextState.layer = p.conState.layer,
ed.nextState.cleared = p.conState.cleared+1, so S' is the DESCENDED block (layer+1) when δ=1, or same block when δ=0.
</task>

<output_contract>
Answer in this order, terse:
1. VERDICT: Is conjunct-2 provable from (hcase1,hlayer,hcenter,hinv-2,hgrade) ALONE for a FREE ed.nextState?
   Or does the proof require a hypothesis linking ed.nextState to p.conState (a "descend" relation
   S' = supportAt(successor of p.conState))? If a link is required, state the WEAKEST link that suffices,
   as a precise predicate, and say whether hgrade (being stated on the specific S') already smuggles enough.
2. If provable: give the algebraic decomposition as a chain of named sub-lemmas, δ=1 and δ=0 separately.
   For each, the exact identity: how foldResid_p(qm u) [or (stepMap u)], with foldResid_p being
   Deg1SupportedSlot on S_parent, re-expresses as ∑_{i∈S'} c'_i u · u_i (conjunct A) and PerLayerDeg1From
   S' (conjunct B). Name which hypothesis clause each step consumes (hinv-2's A, hinv-2's B, hgrade (a), hgrade (b)).
3. The single most likely FAILURE POINT (where a free ed.nextState or the ⊆-not-= hcenter breaks a step), and
   the cheapest discriminating check (a sympy substitution) to settle it before I invest in Lean.
</output_contract>

<grounding_rules>
Distinguish (i) what FOLLOWS from the stated hypotheses vs (ii) what you INFER about the intended construction.
Flag any step where you assume a state relationship not in the hypotheses. Do not claim a Mathlib lemma exists
unless you are confident at v4.29; I verify all lemma names myself. If you think the theorem is FALSE as stated
for a free ed.nextState, say so and give the counterexample shape.
</grounding_rules>
