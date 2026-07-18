import Meta.Cordon
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic

/-!
# `DLNFibre.DLN.RLCT.Engine.ResolutionTree` — the pp.14–22 resolution-tree carrier (edge-labelled)

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules
apply.**
The founding carrier of the transform-only Aoyagi engine: a Lean datatype for the paper's double
induction (`S = 0..L+1`, `J`) that resolves the multiplication-ideal singularity by iterated
blow-ups
(Aoyagi 2023 pp.14–22; worked.tex § blow-up).

**Edge-labelled shape (council of two, 2026-07-17).** One Case-1 blow-up emits BOTH a 1(1) and a
1(2)
chart of ONE step (necessity witness); the per-chart **case** and **substitution** are per-EDGE
data.
So children hang off `Edge {case, subst, child}`, `StepData` carries no `case`, and the chart CoV is
the FOLD of the edge substitutions down the tree.

**Charts as self-maps of `Params M` (Q5 route (b), fork 8).** Each substitution is a coordinate
change
`Params M → Params M` (the space is normed / finite-dimensional / Haar via `Foundations/
ParamsFlatLinear`), so a leaf chart's Jacobian `Dφ w : Params M →L Params M` is an endomorphism with
a
`det` — exactly the shape `rlctAtOn_boundedUnit_localHomeomorph` consumes. The monomial-Jacobian
ledger
(`ChartSubst.jacPow`, folded along the path) carries the divisor exponents; NO opaque derivative
field
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
exponents contributed at this step). The leaf chart CoV is the fold of the `localSub`s along the
path;
the leaf Jacobian exponent is the fold of the `jacPow`s. No opaque derivative field. -/
structure ChartSubst (M : Fin (L + 1) → ℕ) where
  /-- The chart coordinate change (self-map of parameter space). -/
  localSub : Params M → Params M
  /-- The Case-1 equal-run length `J₁` of this step (the exponent-merge increment
  `M' = M + J₁·(M^{(S+1)}−J)`; page-image preprint p.16 Case 1(1)). CERTIFICATE CONSTRAINT — read by
  `StepRel`'s case-1(1) clause. -/
  runLen : ℕ
  /-- Number of exceptional divisors this step introduces. CONSTRUCTION-SIDE BOOKKEEPING. -/
  jacDivCount : ℕ
  /-- Monomial-Jacobian exponents contributed at this step. CONSTRUCTION-SIDE BOOKKEEPING (minor 8):
  the leaf Jacobian is pinned by `LeafJacobian`'s existential `Dβ`, NOT by this ledger; no
  obligation reads `jacPow`, so it may be corrupted without changing the certificate. -/
  jacPow : Fin jacDivCount → ℕ

/-- **Per-node data of the double induction** (map node: `resolution-tree`). The step's CASE is on
the
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
  /-- The monomial vector (exponent vectors over divisor variables). TYPE-LEVEL CERTIFICATE
  CONSTRAINT via `bChain` (no runtime Prop reads `bExp`; its content is the typed monotonicity). -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The divisibility chain** — `bExp` pointwise monotone. CERTIFICATE CONSTRAINT at TYPE
  strength (a multiplicity flatten is a type error; `g-delta-flatten.py`), not a runtime
  obligation. -/
  bChain : Monotone bExp
  /-- The per-divisor exponent ledger `M_{s,k}`. CERTIFICATE CONSTRAINT — read by `StepRel`'s
  case-1(1) clause and `IsFullMonomialization`. -/
  divExp : Fin numDiv → ℕ
  /-- The per-divisor clearing level `t̃_{s,k}`. CERTIFICATE CONSTRAINT — read by `StepRel`'s
  case-1(1) clause (`divTilde kp = cleared`). -/
  divTilde : Fin numDiv → ℕ
  /-- Number of residual generators tracked for sharing. -/
  numGen : ℕ
  /-- **The divisor-support (sharing) map** — `Finset`-valued (a multiplicity flatten is a TYPE
  ERROR; `g-delta-flatten.py`). CERTIFICATE CONSTRAINT — read by `StepRel`'s case-2 clause
  (`∀ g, kp ∈ support g`). -/
  support : Fin numGen → Finset (Fin numDiv)

/-- **Terminal (leaf) data**: the fully monomialised state. The chart CoV `chartMap : Params M →
Params M` is DERIVED (= fold of the root→leaf edge substitutions; coherence in the bundle), over the
UPSTAIRS source domain `srcBox`. Divisor coords `divCoord` and Morse coords `resCoord` are indices
in
`Fin (flatDim M)`, read off a point via `paramsEquivFlat`. -/
structure LeafData (M : Fin (L + 1) → ℕ) where
  /-- Number of terminal divisors (all `t̃ = 0`). -/
  numDiv : ℕ
  /-- The accumulated exponent `M_{s,k}` of each terminal divisor. CERTIFICATE CONSTRAINT — read by
  `IsFullMonomialization`, `terminalExponents`, and the exponent hooks. -/
  divExp : Fin numDiv → ℕ
  /-- The rank profile of each terminal divisor's branch. CERTIFICATE CONSTRAINT — `Adm`-membership
  and the `Mval` tie are read by `IsFullMonomialization` (finding 4). -/
  divProfile : Fin numDiv → (Fin L → ℕ)
  /-- Length of the diagonal monomial vector. -/
  numB : ℕ
  /-- The diagonal monomial vector. TYPE-LEVEL CERTIFICATE CONSTRAINT via `bChain` (no runtime Prop
  reads `bExp`; its content is the typed monotonicity). -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The leaf divisibility chain** — `bExp` pointwise monotone (C1, type-strength). CERTIFICATE
  CONSTRAINT at TYPE strength (a flatten is a type error), not a runtime obligation. -/
  bChain : Monotone bExp
  /-- The leaf chart CoV (the root→leaf edge-substitution fold; coherence in the bundle). -/
  chartMap : Params M → Params M
  /-- The chart's UPSTAIRS source domain. -/
  srcBox : Set (Params M)
  /-- Rank of the residual Morse core (`0` = bounded unit). -/
  resRank : ℕ
  /-- Which flat coordinates are the terminal divisors `u_k` (for the pullback monomial `∏ u²`). -/
  divCoord : Fin numDiv → Fin (flatDim M)
  /-- The Morse residual coordinates `z` (disjoint from the divisors), for the `‖z‖²` normal form.
  -/
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

/-- Root-node accessors reading the ledger at the ROOT of a subtree (a `StepData` for a `branch`,
the `LeafData` for a `leaf`) — used by `StepRel` to read an edge's `child` (finding 1). -/
def rootNumDiv {M : Fin (L + 1) → ℕ} : ResolutionTree M → ℕ
  | leaf l => l.numDiv
  | branch n _ => n.numDiv

/-- The child root's divisor exponent at (ℕ-)index `k` (`0` out of range). -/
def rootDivExp {M : Fin (L + 1) → ℕ} : ResolutionTree M → ℕ → ℕ
  | leaf l, k => if h : k < l.numDiv then l.divExp ⟨k, h⟩ else 0
  | branch n _, k => if h : k < n.numDiv then n.divExp ⟨k, h⟩ else 0

/-- The child root's cleared-pivot count `J` (`0` at a leaf, `S = L+1` terminal). -/
def rootCleared {M : Fin (L + 1) → ℕ} : ResolutionTree M → ℕ
  | leaf _ => 0
  | branch n _ => n.cleared

/-- The terminal EXPONENTS the threshold `½·min` reads off: each leaf's divisor exponents PLUS its
positive Morse-residual rank `resRank` (the resRank fold — so the `region_glue` ratio `hrat` covers
the `resRank/2` residual threshold and `exponent_ledger_bridge` extends to `minAdm ≤ resRank`;
ruling 2a / the elder-ratified rev-1 amendment). Aoyagi p.22 + cert-bridge-design A2. -/
def terminalExponents {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : List ℕ :=
  (leaves t).flatMap (fun l =>
    ((List.finRange l.numDiv).map l.divExp) ++ (if 0 < l.resRank then [l.resRank] else []))

end ResolutionTree

end DLNFibre.DLN.RLCT.Engine
