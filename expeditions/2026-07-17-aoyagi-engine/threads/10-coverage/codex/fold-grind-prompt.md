<task>
Lean 4 + Mathlib (toolchain v4.29.0, Mathlib v4.29). I am proving two lemmas in a coverage module.
I want the CLEANEST proof strategy (tactic-level, with correct v4.29 lemma names) for each, and
flagging of any friction. This is a design consult — I will run all code locally; the DIAGNOSIS is
what I want, not code I paste blindly.

## Background defs (all already in the codebase, verbatim)

Mutually-recursive tree carrier (`M : Fin (L+1) → ℕ`, `Params M` is a normed ℝ-vector space):

  inductive ResolutionTree (M) | leaf (l : LeafData M) | branch (n : StepData M) (edges : List (Edge M))
  inductive Edge (M) | mk (case : StepCase) (subst : ChartSubst M) (child : ResolutionTree M)
  -- Edge.subst (.mk _ s _) = s ; Edge.child (.mk _ _ c) = c ; ChartSubst.localSub : Params M → Params M
  -- LeafData.srcBox : Set (Params M) ; LeafData.chartMap : Params M → Params M

  mutual  -- leaf/composite pairs, acc = the root→leaf fold so far
  def leafPaths (acc : Params M → Params M) : ResolutionTree M → List (LeafData M × (Params M → Params M))
    | leaf l => [(l, acc)]
    | branch _ edges => edgesLeafPaths acc edges
  def edgesLeafPaths (acc) : List (Edge M) → List (LeafData M × (Params M → Params M))
    | [] => []
    | .mk _ s c :: es => leafPaths (acc ∘ s.localSub) c ++ edgesLeafPaths acc es
  end

  mutual  -- (also in codebase) the leaves themselves
  def leaves : ResolutionTree M → List (LeafData M)
    | leaf l => [l] | branch _ edges => edgesLeaves edges
  def edgesLeaves : List (Edge M) → List (LeafData M)
    | [] => [] | .mk _ _ c :: es => leaves c ++ edgesLeaves es
  end

My own new def (structural recursion, mirrors edgesLeaves; ALREADY PROVEN to compile + a fold lemma
`leafPathImages_branch : leafPathImages (branch n edges) = ⋃ e ∈ edges, e.subst.localSub '' leafPathImages e.child`):

  mutual
  def leafPathImages : ResolutionTree M → Set (Params M)
    | .leaf l => l.srcBox | .branch _ edges => edgesImages edges
  def edgesImages : List (Edge M) → Set (Params M)
    | [] => ∅ | .mk _ s c :: es => s.localSub '' leafPathImages c ∪ edgesImages es
  end

## Lemma A (the headline's missing bridge)
I need, for the ChartBridge headline:
  leafPathImages t = ⋃ p ∈ leafPaths (id : Params M → Params M) t, p.2 '' p.1.srcBox
Then coherence `(∀ p ∈ leafPaths id t, p.1.chartMap = p.2)` rewrites p.2 → p.1.chartMap, and
`leaves t ↔ (leafPaths id t).map Prod.fst` turns it into `⋃ l ∈ leaves t, l.chartMap '' l.srcBox`.

My plan: prove a general-accumulator lemma by MUTUAL induction on the tree/edge-list:
  imgAcc (acc) (t) : (⋃ p ∈ leafPaths acc t, p.2 '' p.1.srcBox) = acc '' leafPathImages t
  imgEdgesAcc (acc) (edges) : (⋃ p ∈ edgesLeafPaths acc edges, p.2 '' p.1.srcBox) = acc '' edgesImages edges
The cons case needs: biUnion over `++`, `Set.image_comp` for `(acc ∘ s.localSub) '' X = acc '' (s.localSub '' X)`,
`Set.image_union`. Then Lemma A = imgAcc id + `id '' S = S`. And `(leafPaths acc t).map Prod.fst = leaves t`
by another mutual induction.

## Lemma B (node_pivotCover_of_atom — the per-node cover, flat embedding)
Rung-1 atom (PROVEN): for `d ≥ 1`, `⋃ i : Fin d, pivotChart i '' pivotChartDom i R = cubeBox d R`
over `Fin d → ℝ`, where `pivotChart i u k = if k = i then u i else u i * u k`,
`pivotChartDom i R = {u | |u i| ≤ R ∧ ∀ k ≠ i, |u k| ≤ 1}`, `cubeBox d R = univ.pi (fun _ => Icc (-R) R)`.
I must embed this into `Params M ≃L[ℝ] (Fin (flatDim M) → ℝ)` (`paramsEquivFlatCLE`, a continuous linear
equiv / homeomorphism): a blow-up node has `d_center` "center" flat coordinates (an injection
`S : Fin d_center ↪ Fin (flatDim M)`); the pivot chart acts as `pivotChart` on the S-coordinates and
IDENTITY on the other ("spectator") flat coordinates; as a self-map of `Params M` it is
`paramsEquivFlat.symm ∘ (flat embedded chart) ∘ paramsEquivFlat`. I need to discharge
  `∃ U, IsOpen U ∧ V ⊆ U ∧ U ⊆ ⋃ (the d_center embedded pivot charts) '' (embedded domains)`
where V is a neighbourhood of the center `{flat coords in S all 0}`.

## What I've established as the shape
- The union of embedded charts over S = "S-slab cube" = {y : y|_S ∈ cubeBox, y|_{Sᶜ} free}; V = open S-slab
  ⊆ U = open S-slab ⊆ closed S-slab = the union. So U = the open version works.
</task>

<output_contract>
Two sections, A and B.

For A: (1) Is a `mutual theorem` block with equation-style pattern matching (`| .leaf l => by ...`)
the right v4.29 idiom for induction following this leafPaths/edgesLeafPaths structure, or is there a
cleaner approach (e.g. a manual `.rec`, `List.rec` + tree induction, or a single non-mutual framing)?
(2) The correct v4.29 Mathlib names for: biUnion over `List` append (`⋃ p ∈ A ++ B, f p = (⋃∈A) ∪ (⋃∈B)`),
biUnion over cons/singleton, `Set.image_comp` (exact signature + which direction), `Set.image_union`,
`id '' s`. (3) The known friction point (controller flagged `image_comp` HO-unification fighting `rw`):
the recommended sidestep (fully-applied `exact`? `simp only [Set.image_comp]`? `Set.image_image`?).
Give the cons-case tactic block concretely.

For B: (1) The cleanest way to define the flat-embedded pivot chart as a `Params M → Params M`
self-map and its domain, minimizing paramsEquivFlat transport friction — is conjugation
`e.symm ∘ flat ∘ e` best, or should I work entirely in `Fin (flatDim M) → ℝ` and transport the final
cover statement once? (2) Which Mathlib facts transport the cover: `Set.image_comp`,
`Equiv.image_eq_preimage`, `Homeomorph.isOpen_image`/`isOpen_preimage`, `ContinuousLinearEquiv`
image/preimage lemmas — the cleanest chain to move `V ⊆ U ⊆ ⋃ images` across the equiv. (3) The
"S-slab" union: how to express `⋃ i, embChart i '' embDom i` = the atom's cube on S-coords × free on
spectators, reusing the rung-1 atom (`Set.pi`/`Function.update`/coordinate-split lemmas). (4) The single
biggest risk that would make this balloon, and the cheapest way to de-risk it.

Keep it tight and concrete; assume I know Mathlib basics. Flag any lemma name you're UNSURE exists at
v4.29 as "verify".
</output_contract>

<grounding_rules>
Flag any Mathlib lemma name you are not confident exists at v4.29 with "(verify)". Distinguish "this
is the standard idiom" (fact) from "I'd try this" (suggestion). Do not invent lemma names.
</grounding_rules>
