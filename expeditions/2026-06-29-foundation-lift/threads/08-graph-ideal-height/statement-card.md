# Statement card — P2-R3 graph-ideal height re-home

**Thread:** 08-graph-ideal-height (foundation-lift Phase 2, the last P2 rung)
**Branch:** `expedition/foundation-lift-p2` (commit `12fb9faa`)
**Build:** `./scripts/lb DLNFibre` green at **3820 jobs** (matches the warm baseline). `scripts/sorries`
clean (0 sorry / 0 #exit / 0 native_decide / 0 axiom). `#print axioms
MvPolynomial.height_graphIdeal_eq` = `[propext, Classical.choice, Quot.sound]`.

## What was done

Re-homed the graph-ideal **height** content from `DLNFibre/Core/GraphIdealHeight.lean` (namespace
`DLNFibre.Core`) into a new sibling module **`DLNFibre/Core/MvPolynomial/GraphIdealHeight.lean`**
(namespace **`MvPolynomial`**), beside the `graphIdeal` it measures. The source module was already
maximally general (`[Field k] [Finite σ] [Finite τ]`); the lift was a re-home + namespace change to
`MvPolynomial` + a Mathlib-grade docstring/minimal-hypothesis pass + a dependency tidy. **No
signature, hypothesis, or proof changed.** The old file was deleted (git records a rename, 86%).

The result it delivers: the graph ideal eliminating the `σ`-block of `MvPolynomial (σ ⊕ τ) k` has
height `Nat.card σ` — the number of eliminated variables — by the field catenary `height + dim
(quotient) = #vars`. This is the lower-bound engine for the `Iad = J` height-squeeze of `G2-2`
(`height J = #B22block = (p−r)(q−r) = C`; the inclusion `J ⊆ Iad` alone only gives `≤ C`).

## Placement choice (sibling, not extend `GraphIdeal.lean`)

Chose a **sibling** `Core/MvPolynomial/GraphIdealHeight.lean` over extending P2-R1's
`Core/MvPolynomial/GraphIdeal.lean`. The base `GraphIdeal.lean` is deliberately pure `MvPolynomial`
— imports only basic Mathlib (`Algebra.MvPolynomial.Basic`, `RingTheory.Ideal.*`), carries no
finiteness, and is upstream-ready (a file-move to `Mathlib.RingTheory.MvPolynomial.…` with no
namespace surgery). The height content genuinely needs the field-catenary / Krull-dimension stack
(`DLNFibre.Core.Dimension.Codimension` and its transitive `Catenary`), a heavyweight dependency that
would pollute that clean base file and break its upstream-move property. The sibling keeps the height
result **cohesive** (same `MvPolynomial/` directory, namespace `MvPolynomial`, beside the ideal it
measures) while quarantining the dimension dependency. As a dependency tidy, the new module imports
`DLNFibre.Core.Dimension.Codimension` **directly** (the catenary's true home, per #14) rather than
the previous `DLNFibre.Core.NullstellensatzCodim` re-export, which also dragged in `OrbitCodim` and
the full Nullstellensatz — a lighter, more honest import.

## Module + signatures (ns `MvPolynomial`, `variable {k} [Field k] {σ τ} [Finite σ] [Finite τ]`)

`DLNFibre/Core/MvPolynomial/GraphIdealHeight.lean` (175 LoC; `open DLNFibre.Core.Dimension`):

```
theorem ringKrullDim_quotient_graphIdeal_eq (c : σ → MvPolynomial τ k) :   -- omit [Finite σ]
    ringKrullDim (MvPolynomial σ (MvPolynomial τ k) ⧸ graphIdeal c) = (Nat.card τ : WithBot ℕ∞)

theorem height_graphIdeal_eq (c : σ → MvPolynomial τ k) :                  -- THE HEADLINE
    (graphIdeal c).height = (Nat.card σ : ℕ∞)

theorem height_coordIdeal_eq :
    (Ideal.span (Set.range fun i ↦ (X i : MvPolynomial σ (MvPolynomial τ k)))).height
      = (Nat.card σ : ℕ∞)

noncomputable def translateAux {R : Type*} [CommRing R] (c : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R                                -- X b ↦ X b + C (c b)

theorem height_coordIdeal_localization_eq (f : MvPolynomial τ k) (hf : f ≠ 0)
    (Sd : Type u) [CommRing Sd] [Algebra (MvPolynomial τ k) Sd] [IsLocalization.Away f Sd] :
    (Ideal.span (Set.range fun b ↦ (X b : MvPolynomial σ Sd))).height = (Nat.card σ : ℕ∞)

theorem height_graphIdeal_localization_eq (f : MvPolynomial τ k) (hf : f ≠ 0)   -- the G2-2 consumer
    (Sd : Type u) [CommRing Sd] [Algebra (MvPolynomial τ k) Sd] [IsLocalization.Away f Sd]
    (c : σ → Sd) : (graphIdeal c).height = (Nat.card σ : ℕ∞)
```

**Headline exact signature** (full namespace `MvPolynomial.height_graphIdeal_eq`):

```
theorem height_graphIdeal_eq {k : Type u} [Field k] {σ : Type v} {τ : Type w}
    [Finite σ] [Finite τ] (c : σ → MvPolynomial τ k) :
    (graphIdeal c).height = (Nat.card σ : ℕ∞)
```

## Minimal hypotheses (confirmed by build)

- `ringKrullDim_quotient_graphIdeal_eq` — needs only `[Finite τ]`; carries `omit [Finite σ]` (it
  reads the quotient `MvPolynomial τ k`, whose dimension `Nat.card τ` is independent of `σ`).
- `height_graphIdeal_eq` and the downstream height results — need **both** `[Finite σ]` and
  `[Finite τ]`. The catenary `height_add_ringKrullDim_quotient_eq_card` fires on
  `MvPolynomial (σ ⊕ τ) k`, whose finite Krull dimension requires `[Finite (σ ⊕ τ)]` (i.e. both
  summands finite), and the `#vars = #σ + #τ` step uses `Nat.card_sum` (both summands finite). So
  `[Finite τ]` is **not** droppable from the height results — the weakest set that compiles is exactly
  `[Field k] [Finite σ] [Finite τ]`. The consumers (`B22block = Fin _ × Fin _`,
  `SchurVar = Fin-sum/product`) are both `Fintype`, so both instances are met.

## Sibling-clash gate (CLEAR)

`rg` over `.lake/packages/mathlib/` finds **no** `height_graphIdeal_eq`,
`ringKrullDim_quotient_graphIdeal_eq`, `height_coordIdeal_eq`, `height_coordIdeal_localization_eq`,
`height_graphIdeal_localization_eq`, or `translateAux` anywhere. The only Mathlib `translate` is
`Mathlib.Algebra.Group.Translate.translate` (`G → α`, a different namespace and shape, not imported);
no `MvPolynomial.translate*`. All six identifiers are new in namespace `MvPolynomial`. `@[stacks …]`
**declined** — no exact Stacks-tag match for "graph-ideal height = #eliminated vars over a field".

## What re-pointed (L2 sweep + full build)

- `DLNFibre/Core/DeterminantalBaseElimination.lean` — the only direct code consumer (uses
  `height_graphIdeal_localization_eq` via `height_graphIdeal_forcedB22_eq`): import re-pointed
  `Core.GraphIdealHeight` → `Core.MvPolynomial.GraphIdealHeight`; one docstring reference updated. It
  already `open MvPolynomial`, so the bare call re-resolves with no body edit. Green.
- `DLNFibre/Core/DeterminantalBasePresentation.lean` — transitive consumer (one docstring mention of
  `height_coordIdeal_localization_eq`); no import/body edit needed. Green.
- `DLNFibre.lean` aggregator — the single import line re-pointed **in place** (no reorder).
- Full `DLNFibre/` `rg` sweep of all six identifiers + the old module path: no lingering
  `Core.GraphIdealHeight` / `Core/GraphIdealHeight` reference anywhere; every name sits in a file that
  `open MvPolynomial`.

## Build / sorry / axiom status

- `./scripts/lb DLNFibre`: **green, 3820 jobs** (= warm baseline).
- `scripts/sorries`: **0 sorry / 0 #exit / 0 native_decide / 0 axiom**.
- `#print axioms MvPolynomial.height_graphIdeal_eq`: `[propext, Classical.choice, Quot.sound]`.
- LoC delta: `+175` (new module) / `−161` (deleted source); the `+14` is the Apache header +
  expanded docstring (placement rationale + minimal-hypothesis note). Zero proof content changed.

## Holes / surprises

None. Verbatim re-home of already-general, already-green code; behavioural changes are the namespace
(`DLNFibre.Core` → `MvPolynomial`), the lighter import (`NullstellensatzCodim` →
`Dimension.Codimension`), and prose. Pre-existing longLine / `show`-linter warnings live in DLN/Core
files this rung did not touch. **Name = content:** `height_graphIdeal_eq` proves exactly the height
equals `Nat.card σ` (eliminated-variable count), no more.
