import Meta.Cordon
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic

/-!
# `DLNFibre.DLN.RLCT.Engine.ResolutionTree` — the pp.14–22 resolution-tree carrier (edge-labelled)

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules apply.**
The founding carrier of the transform-only Aoyagi engine: a Lean datatype for the paper's double
induction (`S = 0..L+1`, `J`) that resolves the multiplication-ideal singularity by iterated blow-ups
(Aoyagi 2023 pp.14–22; worked.tex § blow-up).

**Edge-labelled shape (council of two, 2026-07-17).** One Case-1 blow-up emits BOTH a 1(1) and a 1(2)
chart of ONE step (necessity witness); the per-chart **case** and **substitution** are per-EDGE data.
So children hang off `Edge {case, subst, child}`, `StepData` carries no `case`, and the chart CoV is
the FOLD of the edge substitutions down the tree.

**Charts as self-maps of `Params M` (Q5 route (b), fork 8).** Each substitution is a coordinate change
`Params M → Params M` (the space is normed / finite-dimensional / Haar via `Foundations/
ParamsFlatLinear`), so a leaf chart's Jacobian `Dφ w : Params M →L Params M` is an endomorphism with a
`det` — exactly the shape `rlctAtOn_boundedUnit_localHomeomorph` consumes. The monomial-Jacobian ledger
(`ChartSubst.jacPow`, folded along the path) carries the divisor exponents; NO opaque derivative field
is stored as data. Divisor / Morse coordinates are read off `w` via `paramsEquivFlat` (indices in
`Fin (flatDim M)`).

Non-negotiable per-node data (map node: `resolution-tree`) — flattening the sharing provably changes
the RLCT (`g-coupled-binding-334.py`, `g-delta-flatten.py`): the monomial vector `bExp` + chain
`bChain` (typed on BOTH `StepData` and `LeafData`), the residual dims, the exponent ledger
`divExp`/`divTilde`, and the sharing map `support : Gen → Finset DivVar`.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- Which branch of the `(S,J)` step an EDGE realises (case11 exponent-merge / case12 new pivot /
case2 full-block); one blow-up may emit multiple cases, so the tag lives on the edge. -/
inductive StepCase
  | case11
  | case12
  | case2
  deriving DecidableEq, Repr

/-- **The per-edge substitution ledger** (fork 8): `localSub` is the chart's coordinate change as a
self-map of `Params M` (blow-up ∘ shear); `jacPow` is its monomial-Jacobian ledger (the exceptional
exponents contributed at this step). The leaf chart CoV is the fold of the `localSub`s along the path;
the leaf Jacobian exponent is the fold of the `jacPow`s. No opaque derivative field. -/
structure ChartSubst (M : Fin (L + 1) → ℕ) where
  /-- The chart coordinate change (self-map of parameter space). -/
  localSub : Params M → Params M
  /-- Number of exceptional divisors this step introduces. -/
  jacDivCount : ℕ
  /-- Monomial-Jacobian exponents contributed at this step. -/
  jacPow : Fin jacDivCount → ℕ

/-- **Per-node data of the double induction** (map node: `resolution-tree`). The step's CASE is on the
edge, not here. -/
structure StepData (M : Fin (L + 1) → ℕ) where
  /-- The layer index `S`. -/
  layer : ℕ
  /-- The count `J` of unit pivots cleared in layer `S`. -/
  cleared : ℕ
  /-- Residual block row count `M(S) − J`. -/
  resRows : ℕ
  /-- Residual block column count `M(S+1) − J`. -/
  resCols : ℕ
  /-- Number of exceptional divisor variables in scope. -/
  numDiv : ℕ
  /-- Length of the monomial vector. -/
  numB : ℕ
  /-- The monomial vector (exponent vectors over divisor variables). -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The divisibility chain** — `bExp` pointwise monotone. -/
  bChain : Monotone bExp
  /-- The per-divisor exponent ledger `M_{s,k}`. -/
  divExp : Fin numDiv → ℕ
  /-- The per-divisor clearing level `t̃_{s,k}`. -/
  divTilde : Fin numDiv → ℕ
  /-- Number of residual generators tracked for sharing. -/
  numGen : ℕ
  /-- **The divisor-support (sharing) map** — `Finset`-valued (a multiplicity flatten is a TYPE
  ERROR; `g-delta-flatten.py`). -/
  support : Fin numGen → Finset (Fin numDiv)

/-- **Terminal (leaf) data**: the fully monomialised state. The chart CoV `chartMap : Params M →
Params M` is DERIVED (= fold of the root→leaf edge substitutions; coherence in the bundle), over the
UPSTAIRS source domain `srcBox`. Divisor coords `divCoord` and Morse coords `resCoord` are indices in
`Fin (flatDim M)`, read off a point via `paramsEquivFlat`. -/
structure LeafData (M : Fin (L + 1) → ℕ) where
  /-- Number of terminal divisors (all `t̃ = 0`). -/
  numDiv : ℕ
  /-- The accumulated exponent `M_{s,k}` of each terminal divisor. -/
  divExp : Fin numDiv → ℕ
  /-- The rank profile of each terminal divisor's branch. -/
  divProfile : Fin numDiv → (Fin L → ℕ)
  /-- Length of the diagonal monomial vector. -/
  numB : ℕ
  /-- The diagonal monomial vector. -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The leaf divisibility chain** — `bExp` pointwise monotone (C1, type-strength). -/
  bChain : Monotone bExp
  /-- The leaf chart CoV (the root→leaf edge-substitution fold; coherence in the bundle). -/
  chartMap : Params M → Params M
  /-- The chart's UPSTAIRS source domain. -/
  srcBox : Set (Params M)
  /-- Rank of the residual Morse core (`0` = bounded unit). -/
  resRank : ℕ
  /-- Which flat coordinates are the terminal divisors `u_k` (for the pullback monomial `∏ u²`). -/
  divCoord : Fin numDiv → Fin (flatDim M)
  /-- The Morse residual coordinates `z` (disjoint from the divisors), for the `‖z‖²` normal form. -/
  resCoord : Fin resRank → Fin (flatDim M)

mutual
  /-- **The resolution tree** (map node: `resolution-tree`): internal nodes are blow-up steps,
  children hang off labelled `Edge`s, leaves are terminal states. -/
  inductive ResolutionTree (M : Fin (L + 1) → ℕ) where
    | leaf (l : LeafData M) : ResolutionTree M
    | branch (n : StepData M) (edges : List (Edge M)) : ResolutionTree M
  /-- A labelled edge: the chart's `case`, its `subst`itution, and the `child` subtree. -/
  inductive Edge (M : Fin (L + 1) → ℕ) where
    | mk (case : StepCase) (subst : ChartSubst M) (child : ResolutionTree M) : Edge M
end

namespace Edge
variable {M : Fin (L + 1) → ℕ}
/-- The case tag of an edge. -/
def case : Edge M → StepCase | .mk c _ _ => c
/-- The substitution ledger of an edge. -/
def subst : Edge M → ChartSubst M | .mk _ s _ => s
/-- The child subtree of an edge. -/
def child : Edge M → ResolutionTree M | .mk _ _ c => c
end Edge

namespace ResolutionTree

mutual
/-- The list of terminal leaves of the tree (its chart atlas). -/
def leaves {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (LeafData M)
  | leaf l => [l]
  | branch _ edges => edgesLeaves edges
/-- The leaves reachable through a list of edges. -/
def edgesLeaves {M : Fin (L + 1) → ℕ} : List (Edge M) → List (LeafData M)
  | [] => []
  | .mk _ _ c :: es => leaves c ++ edgesLeaves es
end

mutual
/-- The list of internal (blow-up step) nodes of the tree. -/
def nodes {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (StepData M)
  | leaf _ => []
  | branch n edges => n :: edgesNodes edges
/-- The step nodes reachable through a list of edges. -/
def edgesNodes {M : Fin (L + 1) → ℕ} : List (Edge M) → List (StepData M)
  | [] => []
  | .mk _ _ c :: es => nodes c ++ edgesNodes es
end

mutual
/-- Each leaf paired with the composite of its root→leaf edge substitutions (`acc` = the fold so
far). The bundle's coherence clause equates this composite to the leaf's `chartMap`. -/
def leafPaths {M : Fin (L + 1) → ℕ} (acc : Params M → Params M) :
    ResolutionTree M → List (LeafData M × (Params M → Params M))
  | leaf l => [(l, acc)]
  | branch _ edges => edgesLeafPaths acc edges
/-- The leaf/composite pairs reachable through a list of edges. -/
def edgesLeafPaths {M : Fin (L + 1) → ℕ} (acc : Params M → Params M) :
    List (Edge M) → List (LeafData M × (Params M → Params M))
  | [] => []
  | .mk _ s c :: es => leafPaths (acc ∘ s.localSub) c ++ edgesLeafPaths acc es
end

mutual
/-- Parent-step / edge pairs of the tree — the domain of the edge-relational `StepRel`. -/
def stepEdges {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (StepData M × Edge M)
  | leaf _ => []
  | branch n edges => edges.map (fun e => (n, e)) ++ edgesStepEdges edges
/-- Parent–edge pairs reachable through a list of edges. -/
def edgesStepEdges {M : Fin (L + 1) → ℕ} : List (Edge M) → List (StepData M × Edge M)
  | [] => []
  | .mk c s ch :: es => stepEdges ch ++ edgesStepEdges es
end

/-- The terminal divisor exponents gathered across all leaves — the candidate set the threshold
`½·min` (Aoyagi p.22) reads off. -/
def terminalExponents {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : List ℕ :=
  (leaves t).flatMap (fun l => (List.finRange l.numDiv).map l.divExp)

end ResolutionTree

end DLNFibre.DLN.RLCT.Engine
