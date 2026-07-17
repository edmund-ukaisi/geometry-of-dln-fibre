import Meta.Cordon
import DLNFibre.DLN.RLCT.Foundations.Loss
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic

/-!
# `DLNFibre.DLN.RLCT.Engine.ResolutionTree` — the pp.14–22 resolution-tree carrier

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules apply
(`docs/policies/expedition-map.md` § The blueprint).** This module is the founding carrier of the
transform-only Aoyagi engine: a Lean datatype for the paper's double induction (`S = 0..L+1` layer
index, `J = 0..min(M(S),M(S+1))` cleared pivots) that resolves the multiplication-ideal singularity
by iterated blow-ups (Aoyagi 2023 preprint pp.14–22; `theory/aoyagi-2023-reproduction/
aoyagi-2023-worked.tex` § blow-up).

The **non-negotiable per-node data** (map node: `resolution-tree`) is fixed by the coupled-binding
battery witnesses — flattening the sharing structure provably changes the RLCT
(`g-coupled-binding-334.py`, `g-delta-flatten.py`: `lct(δ²(x²+y²)) = ½` vs `lct(δ₁²x² + δ₂²y²) = 1`,
identical per-generator multiplicities, different value). Every node therefore records, and cannot
flatten:

* the **monomial vector** `bExp` with its **divisibility chain** `bChain`
  (`b₀ = 1`, `bᵢ = (∏_{t̃=i−1} u) bᵢ₋₁`, so `bᵢ₋₁ ∣ bᵢ`);
* the **residual block** `D_J` of size `(M(S)−J) × (M(S+1)−J)` (its dimensions `resRows × resCols`);
* the **per-divisor exponent ledger** `divExp` (`M_{s,k}`, Jacobian power `M_{s,k}−1`) and clearing
  level `divTilde` (`t̃_{s,k}`);
* the **divisor-support (sharing) map** `support : Gen → Finset DivVar` — which exceptional blow-up
  variables divide which residual generator. THIS is the datum flattening loses.

Encoding note (design freedom, per the architect charter): exceptional divisors and generators are
counted (`Fin numDiv`, `Fin numGen`) per node; the branching is the finite chart cover of each
blow-up (`List (ResolutionTree M)`). The tree carrier is real (no holes); the *obligations* about it
live in `Engine.EngineObligations`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- Which branch of the `(S,J)` step produced this node. Case 1 (partial equal `b`-run) splits into
`case11` (the `d`-block `= u·d'`; exponent-merge inner recursion, `t̃ = J`) and `case12` (first row
normalised, `u = u_{S,J+1}·u'`; introduces a new pivot divisor and advances `J`); `case2` is the
full-remaining-block blow-up (`M'_{S,J+1} = (M(S)−J)(M(S+1)−J)`, the residual codimension). -/
inductive StepCase
  | case11
  | case12
  | case2
  deriving DecidableEq, Repr

/-- **Per-node data of the double induction** (map node: `resolution-tree`). Records the `(S,J)`
index, the case, the residual-block dimensions, the monomial vector + divisibility chain, the
per-divisor exponent ledger and clearing levels, and — load-bearing — the divisor-support (sharing)
map. `numDiv` counts the exceptional divisor variables in scope; `numGen` the residual
generators. -/
structure StepData (M : Fin (L + 1) → ℕ) where
  /-- The layer index `S` (`0 ≤ S ≤ L`). -/
  layer : ℕ
  /-- The count `J` of unit pivots already cleared in layer `S`. -/
  cleared : ℕ
  /-- Which branch of the step this node is. -/
  case : StepCase
  /-- Residual block `D_J` row count `M(S) − J`. -/
  resRows : ℕ
  /-- Residual block `D_J` column count `M(S+1) − J`. -/
  resCols : ℕ
  /-- Number of exceptional divisor variables `u_{s,k}` in scope. -/
  numDiv : ℕ
  /-- Length of the monomial vector `b₁ … b_{M(S)}`. -/
  numB : ℕ
  /-- The monomial vector: `bExp i` is the exponent vector of `bᵢ` over the divisor variables. -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The divisibility chain** `b₀ ∣ b₁ ∣ … ∣ b_{M(S)}` — `bExp` is pointwise monotone. -/
  bChain : Monotone bExp
  /-- The per-divisor exponent ledger `M_{s,k}` (Jacobian power of `u_{s,k}` is `divExp k − 1`). -/
  divExp : Fin numDiv → ℕ
  /-- The per-divisor clearing level `t̃_{s,k}` (`0` for a terminal divisor). -/
  divTilde : Fin numDiv → ℕ
  /-- Number of residual generators tracked for sharing. -/
  numGen : ℕ
  /-- **The divisor-support (sharing) map**: which divisor variables divide each generator. This is a
  `Finset`-valued (not `ℕ`-valued) field ON PURPOSE — "simplifying" it to per-generator
  multiplicities `Fin numGen → ℕ` is a TYPE ERROR here, not merely a battery failure: a multiplicity
  cannot record WHICH divisors are shared, and sharing changes the RLCT (`g-delta-flatten.py`). -/
  support : Fin numGen → Finset (Fin numDiv)

/-- **Terminal (leaf) data**: the fully monomialised state at `S = L+1` — the diagonal
`⟨∏ C⟩ = ⟨diag(b₁ … b_{M(L+1)})⟩`, loss `∑ bᵢ²` normal-crossing. Records the terminal divisor
exponents `divExp` (`= Mval` of the divisor's rank profile), each terminal divisor's rank profile
`divProfile ∈ (Fin L → ℕ)`, the diagonal monomial vector, and the chart's domain in parameter
space (used by the coverage obligation). -/
structure LeafData (M : Fin (L + 1) → ℕ) where
  /-- Number of terminal exceptional divisors (all with `t̃ = 0`). -/
  numDiv : ℕ
  /-- The accumulated exponent `M_{s,k}` of each terminal divisor. -/
  divExp : Fin numDiv → ℕ
  /-- The rank profile `t_{s,k} = (t⁽¹⁾, …, t⁽ᴸ⁾)` of each terminal divisor's branch. -/
  divProfile : Fin numDiv → (Fin L → ℕ)
  /-- Length of the diagonal monomial vector `b₁ … b_{M(L+1)}`. -/
  numB : ℕ
  /-- The diagonal monomial vector at the leaf. -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- The coordinate chart's domain in parameter space (its image covers part of the zero locus). -/
  chartDom : Set (Params M)

/-- **The resolution tree** (map node: `resolution-tree`): a finite tree whose internal nodes are
blow-up steps (`StepData`) with their finite chart cover as children, and whose leaves are the
fully-monomialised terminal states (`LeafData`). The `(S,J)` double induction is the root-to-leaf
path; the branching is each blow-up's chart cover. Finite by construction (`List` children); the
`monomialization-termination` obligation asserts a resolution *exists* for every `M`. -/
inductive ResolutionTree (M : Fin (L + 1) → ℕ) where
  | leaf (l : LeafData M) : ResolutionTree M
  | branch (n : StepData M) (charts : List (ResolutionTree M)) : ResolutionTree M

namespace ResolutionTree

/-- The list of terminal leaves of the tree (its chart atlas). -/
def leaves {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (LeafData M)
  | leaf l => [l]
  | branch _ charts => charts.attach.flatMap (fun t => t.1.leaves)
  decreasing_by
    have h := List.sizeOf_lt_of_mem t.2
    simp_wf
    omega

/-- The list of internal (blow-up step) nodes of the tree. -/
def nodes {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (StepData M)
  | leaf _ => []
  | branch n charts => n :: charts.attach.flatMap (fun t => t.1.nodes)
  decreasing_by
    have h := List.sizeOf_lt_of_mem t.2
    simp_wf
    omega

/-- The terminal divisor exponents `{M_{s,k} : t̃_{s,k} = 0}` gathered across all leaves — the
candidate set the threshold `½·min` (Aoyagi p.22) reads off. -/
def terminalExponents {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : List ℕ :=
  (leaves t).flatMap (fun l => (List.finRange l.numDiv).map l.divExp)

end ResolutionTree

end DLNFibre.DLN.RLCT.Engine
