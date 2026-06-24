# Narrow decorrelation probe: is there an HONEST non-vacuous general `routeStep` body today?

## Context (Lean 4 + Mathlib, DLN-fibre RLCT formalisation)
We have a well-founded recursion `routeAtlas` over width vectors `M : Fin (L+1) → ℕ`, terminating on
`ΣM`. It dispatches each node via:

```
inductive RouteStep (M₀ M : Fin (L+1) → ℕ) : Type 1
  | leaf (md : MonoData)
  | branch (cells : Type) (cellsFin : Fintype cells) (cellsNe : Nonempty cells)
      (split : cells → ChainDimSplit M) (codim : cells → ℕ)
      (witness : (c : cells) → PivotWitness M₀ (codim c))

noncomputable def routeStep (M₀ M : Fin (L+1) → ℕ) : RouteStep M₀ M := sorry  -- THE GATE
```

Available, BANKED, sorry-free:
- `schurState M hlo : ChainDimSplit M` where `hlo : ∀ s, s.val ≤ 1 → 1 ≤ M s`. It sets
  `red = (M₀−1, M₁−1, M₂, …)`, `drop = (1,1,0,…)`, ΣM−2. This is the C1 reduced-width split.
- `PivotWitness M₀ c := { T : Fin L → ℕ // hAdm : T ∈ Adm M₀ // hCodim : c = (Mval M₀ T).toNat }` —
  a Type-structure. `Adm M₀` is a concrete Finset, `Mval M₀ T : ℤ` a concrete formula.
- `leafMonoData d : MonoData` (k≡0,h≡0, threshold ⊤).
- The value-side fold lemmas all consume `codim`/`PivotWitness`/`MonoData` abstractly (driver-agnostic).

The pp2 dispatcher cert (§2/§4/§7) is explicit that the LOAD-BEARING risk is:
  - codim must equal `Mval M₀ T` for an ADMISSIBLE T (the geometric codim), NOT coordinate
    cardinality (the (4,3,2) trap: card ≠ Mval there);
  - the cells must correspond to GENUINE rank strata REACHED by a legal chart path — and §4 states
    "only the minimiser need be reached, but THAT COVERAGE IS A THEOREM" (rides Core normal-form
    realizability), NOT a freebie from termination;
  - LEAF must be `IsUnit residualCore`, NOT "no C1 applies".

There is NO Lean `residualCore`, no rank-defect classifier over `M`, and no realizability lemma
connecting the chart path to `Mval M₀ T` yet.

## The narrow question (one direction, truth-value)
Given ONLY what is banked today (schurState exists; PivotWitness/Adm/Mval are concrete; NO residualCore,
NO realizability lemma): is there ANY general `routeStep (M₀ M)` body that is BOTH
(a) total + green, AND
(b) NON-VACUOUS and CERTIFIED — i.e. the produced atlas's leaves genuinely fold to
    `⨅ = ½·minAdm(Mval M)` for the cases it claims, with every branch `codim = Mval M₀ T` for a
    GENUINELY-REACHED admissible T?

Or is (b) blocked on the realizability theorem (§4) + a residualCore classifier — i.e. any total green
body buildable today is necessarily either vacuous (leaf-everywhere / wrong-codim) or it secretly
ASSUMES the unbuilt realizability?

I believe the answer is: blocked. Any total green body today either returns leaf-everywhere (vacuous —
the atlas is trivial, ⨅ = ⊤ ≠ ½·minAdm) or fabricates a PivotWitness whose `T`/`hCodim` cannot be
discharged without the realizability lemma (so it can't actually typecheck the witness field, OR it
picks codim = card and that's the (4,3,2)-wrong value). So the honest move is: keep the named sorry,
fence the 3 obligations precisely, do NOT stub. Confirm or refute, sharply, and name any honest partial
body I'm missing (e.g. a leaf-only total arm that's genuinely correct for degenerate M).
