<task>
Lean 4 + Mathlib v4.29. I am building the SCAFFOLD (statement + WellFounded
termination plumbing + a deferred recStep contract) for a finiteness recursion.
I am NOT proving the recStep here — I want the cleanest, lowest-friction SHAPE so
that two already-PROVED concrete instances are literal instantiations, and the
WellFounded wrapper compiles cleanly with the recStep stubbed by a sorry.

## The mathematics (corank-stratified radial-Schur recursion)
Fix column count p (here p = 4). For corank r ≥ 1, the object is

  core(r, c') :=  ∫_{Δ ∈ matBox r r T} ∫_{S ∈ matBox r p T}
                    ENNReal.ofReal ( (frobSq (rmatMul Δ S)) ^ (-c') )    -- < ⊤ ?

where matBox a b T = {X : Fin a → Fin b → ℝ | ∀ i j, X i j ∈ Icc (-T) T},
frobSq X = ∑ᵢⱼ Xᵢⱼ², rmatMul X Y i j = ∑ₖ Xᵢₖ Yₖⱼ.

The recursion threshold is  λ(r,p) = min( r²/2 , min_{1≤j≤r} ( j·p/2 + λ(r−j, p) ) ),
with λ(0,p) = 0 (a corank-0 leaf is finite for any c' > 0 via pure Morse).
Concretely λ(2,4)=2, λ(3,4)=4. core(r,c') < ⊤ for 0 < c' < λ(r,p).

The recStep (the per-corank inductive step, DEFERRED): cover the Δ-box by r²
radial pivot charts; per chart, radial change-of-variables + N2b minor-pivot
Schur split peels a top j·p-dim Morse block (threshold j·p/2) leaving a JOINT
free-box corank-(r−j) core (the Schur complement Sc plays the role of the free
Δ) integrated at the SHIFTED exponent c' − j·p/2, finite by the IH for
c' − j·p/2 < λ(r−j, p). The IH carrier is the JOINT (W, V, Sc) free-box core —
structurally IDENTICAL to core(r−j, ·), via an already-proved translation-
domination lemma `schurResid2_translate_lt_top` (M22 ↦ Sc is a pure translation,
Jac = 1, into a fixed enlarged box).

## Two ALREADY-PROVED instances that must be literal instantiations
- core_schur2_lt_top : (c' : ℝ) (0 < c') (c' < 2) (T) (0 < T) :
    (∫⁻ Δ in matBox 2 2 T, ∫⁻ S in matBox 2 4 T,
       ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))) < ⊤
- core_schur3_lt_top (in flight, same shape with 2→3 / matBox 3 4 / c' < 4).

## What I'm deciding (the SHAPE questions)
Q1. The threshold λ(r,p). Options:
  (a) a Lean `def schurLambda : ℕ → ℕ → ℝ` by strong recursion on r (well-founded
      via r−j < r), then prove `schurLambda 2 4 = 2`, `schurLambda 3 4 = 4`.
  (b) keep the GENERAL statement parameterised by an ABSTRACT threshold function
      `λ : ℕ → ℝ` supplied as a hypothesis with the two properties the wrapper
      needs (λ 0 ... base, and the min/additive step), so I never have to define
      the recursion's value — the wrapper is threshold-agnostic and the concrete
      λ(2,4)=2 / λ(3,4)=4 are discharged at instantiation.
  (c) state core_schurGen with the threshold INLINED as the min-expression at each
      r (no separate def), unfolding once per r.
  Which minimises friction for a SCAFFOLD whose recStep is stubbed? I lean (b)
  (threshold-agnostic wrapper) or (a). Rank them; name the specific Mathlib
  friction each invites (e.g. defining a ℝ-valued strong recursion, decidability,
  `Nat.strong_induction` vs `WellFounded.fix` ergonomics).

Q2. WellFounded plumbing. The measure is corank r, strictly decreasing (r−j < r,
  j ≥ 1). For a SCAFFOLD that takes an abstract recStep and produces ∀r, is
  `Nat.strong_induction_on` (or `Nat.strongRecOn`) the right tool, and what is the
  exact shape of the recStep hypothesis so the induction discharges cleanly? Give
  the precise Lean signature of the recStep `example`/hypothesis (carrier =
  the JOINT core finiteness one corank lower, NOT the Sc-core alone).

Q3. Pitfalls in v4.29 specifically for: a ℝ-valued well-founded `def` (option a);
  `Nat.strong_induction_on` motive inference; stating an `example` contract that
  references a `sorry`-stubbed step without the stub leaking into the wrapper's
  axioms inappropriately. (I will force `#print axioms`; the scaffold WILL carry
  the deferred recStep sorry intentionally — that's expected and marked.)
</task>

<output_contract>
1. Q1: rank (a)/(b)/(c), one paragraph each naming the concrete Lean friction;
   give a recommendation. If (b), sketch the abstract-λ hypothesis bundle.
2. Q2: the exact Lean signature of (i) `core_schurGen_lt_top`, (ii) the recStep
   hypothesis/contract, (iii) the strong-induction wrapper that consumes (ii) and
   yields (i) for all r. Use real Mathlib v4.29 lemma names (Nat.strong*, etc.).
3. Q3: a short bullet list of v4.29 gotchas for this scaffold.
Be concise and concrete. Lean signatures must typecheck-plausibly (I will build).
</output_contract>

<grounding_rules>
Distinguish (mark explicitly) any Mathlib lemma NAME or signature you are
INFERRING vs one you are confident exists in v4.29. I will verify every name with
`scripts/lean-search` / rg over .lake/packages/mathlib before trusting it. Do not
invent lemma names silently; if unsure of the exact name, say "exists, name ≈ X".
</grounding_rules>
