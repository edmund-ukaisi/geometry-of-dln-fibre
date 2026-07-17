import Meta.Cordon
import DLNFibre.DLN.RLCT.Foundations.Loss
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic

/-!
# `DLNFibre.DLN.RLCT.Engine.ResolutionTree` — the pp.14–22 resolution-tree carrier (edge-labelled)

**Blueprint spine: statements are forecasts; churn is normal; the blueprint consumption rules apply
(`docs/policies/expedition-map.md` § The blueprint).** The founding carrier of the transform-only
Aoyagi engine: a Lean datatype for the paper's double induction (`S = 0..L+1`, `J`) that resolves the
multiplication-ideal singularity by iterated blow-ups (Aoyagi 2023 pp.14–22; worked.tex § blow-up).

**Edge-labelled shape (council of two, 2026-07-17).** One Case-1 blow-up emits BOTH a 1(1) and a 1(2)
chart of ONE step (necessity witness, `threads/01-skeleton/necessity-and-encodings.md`); the per-chart
**case** and **substitution** are therefore per-EDGE data. So children hang off `Edge {case, subst,
child}`, `StepData` no longer carries a `case` (it moves to the edge), and the chart CoV composes down
the tree by folding the edge substitutions. This is the shape the node carrier provably could not
express (a terminal chart's case / any edge's substitution had no home).

Non-negotiable per-node data (map node: `resolution-tree`), unchanged in content — flattening the
sharing provably changes the RLCT (`g-coupled-binding-334.py`, `g-delta-flatten.py`):
* the **monomial vector** `bExp` + its **divisibility chain** `bChain` (kept a TYPED field on BOTH
  `StepData` and `LeafData` — C1 stays type-strength);
* the **residual block** dims `resRows × resCols`;
* the **per-divisor exponent ledger** `divExp` + clearing level `divTilde`;
* the **divisor-support (sharing) map** `support : Gen → Finset DivVar`.

`LeafData` additionally carries the CoV data (council + cert-bridge-design): `chartMap`/`srcBox`
(UPSTAIRS source domain — downstairs blow-up images are NOT open) and the Morse-residual rank
`resRank`. The `chartMap` is DERIVED (= fold of the root→leaf edge substitutions; the coherence clause
lives in the bundle) — not an independent set, closing the `chartDom = univ` vacuity at type strength.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- Which branch of the `(S,J)` step an EDGE realises. Case 1 (partial equal `b`-run) splits into
`case11` (the `d`-block `= u·d'`, an existing exceptional factor; exponent-merge inner recursion) and
`case12` (first row normalised, a NEW pivot `u_{S,J+1}`; advances `J`); `case2` is the full-block
blow-up (`M'_{S,J+1} = (M(S)−J)(M(S+1)−J)`). One blow-up may emit charts of MULTIPLE cases — hence the
tag lives on the edge, not the node. -/
inductive StepCase
  | case11
  | case12
  | case2
  deriving DecidableEq, Repr

/-- **The per-chart substitution ledger** carried on each edge (Q5 route-neutral form, council
interim). `map` is the plain coordinate substitution (blow-up ∘ shear composite) from the edge's
source coordinates into `Params M`; `jacPow` is the monomial-Jacobian ledger (`|det Dφ| = ∏ u^{jacPow}
· unit`). The exact analytic form of the Jacobian identity (fderiv over flat coords vs the
RLCT-transport route) is `LeafJacobian`'s deliberately-loose piece, pending the Q5 supplemental
ruling. -/
structure ChartSubst (M : Fin (L + 1) → ℕ) where
  /-- Number of source coordinates of this chart. -/
  numSrc : ℕ
  /-- The coordinate substitution into parameter space (blow-up ∘ shear composite). -/
  map : (Fin numSrc → ℝ) → Params M
  /-- Number of exceptional divisors this substitution introduces. -/
  jacDivCount : ℕ
  /-- The monomial-Jacobian ledger: `|det Dφ| = ∏_k u_k^{jacPow k} · unit`. -/
  jacPow : Fin jacDivCount → ℕ

/-- **Per-node data of the double induction** (map node: `resolution-tree`). Records the `(S,J)` index,
the residual-block dimensions, the monomial vector + divisibility chain, the per-divisor exponent
ledger and clearing levels, and — load-bearing — the divisor-support (sharing) map. The step's CASE is
NOT here (it is per-edge). -/
structure StepData (M : Fin (L + 1) → ℕ) where
  /-- The layer index `S`. -/
  layer : ℕ
  /-- The count `J` of unit pivots already cleared in layer `S`. -/
  cleared : ℕ
  /-- Residual block `D_J` row count `M(S) − J`. -/
  resRows : ℕ
  /-- Residual block `D_J` column count `M(S+1) − J`. -/
  resCols : ℕ
  /-- Number of exceptional divisor variables in scope. -/
  numDiv : ℕ
  /-- Length of the monomial vector `b₁ … b_{M(S)}`. -/
  numB : ℕ
  /-- The monomial vector: `bExp i` is the exponent vector of `bᵢ` over the divisor variables. -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The divisibility chain** `b₀ ∣ b₁ ∣ …` — `bExp` is pointwise monotone. -/
  bChain : Monotone bExp
  /-- The per-divisor exponent ledger `M_{s,k}` (Jacobian power `M_{s,k} − 1`). -/
  divExp : Fin numDiv → ℕ
  /-- The per-divisor clearing level `t̃_{s,k}` (`0` for a terminal divisor). -/
  divTilde : Fin numDiv → ℕ
  /-- Number of residual generators tracked for sharing. -/
  numGen : ℕ
  /-- **The divisor-support (sharing) map**: which divisor variables divide each generator. A
  `Finset`-valued (not `ℕ`-valued) field ON PURPOSE — a per-generator-multiplicity flatten is a TYPE
  ERROR here (`g-delta-flatten.py`). -/
  support : Fin numGen → Finset (Fin numDiv)

/-- **Terminal (leaf) data**: the fully monomialised state at `S = L+1`. Records the terminal divisor
exponents `divExp` (`= Mval` of the branch profile), each terminal divisor's rank profile
`divProfile`, the diagonal monomial vector + its chain, the CoV data (`chartMap` over the UPSTAIRS
`srcBox`), and the Morse-residual rank `resRank`. `chartMap` is DERIVED (= fold of edge substitutions;
coherence in the bundle), not an independent set — closing the old `chartDom = univ` vacuity. -/
structure LeafData (M : Fin (L + 1) → ℕ) where
  /-- Number of terminal exceptional divisors (all `t̃ = 0`). -/
  numDiv : ℕ
  /-- The accumulated exponent `M_{s,k}` of each terminal divisor. -/
  divExp : Fin numDiv → ℕ
  /-- The rank profile `t_{s,k}` of each terminal divisor's branch. -/
  divProfile : Fin numDiv → (Fin L → ℕ)
  /-- Length of the diagonal monomial vector. -/
  numB : ℕ
  /-- The diagonal monomial vector at the leaf. -/
  bExp : Fin numB → (Fin numDiv → ℕ)
  /-- **The leaf divisibility chain** — `bExp` pointwise monotone (C1, type-strength). -/
  bChain : Monotone bExp
  /-- Number of source (upstairs) coordinates of the leaf chart. -/
  numChartVar : ℕ
  /-- The leaf chart CoV (the root→leaf edge-substitution composite; coherence in the bundle). -/
  chartMap : (Fin numChartVar → ℝ) → Params M
  /-- The chart's UPSTAIRS source domain (openness lives here — downstairs images are not open). -/
  srcBox : Set (Fin numChartVar → ℝ)
  /-- Rank of the residual Morse core (`0` = bounded unit). -/
  resRank : ℕ
  /-- Which source coordinates are the terminal divisors `u_k` (for the pullback monomial `∏ u²`). -/
  divCoord : Fin numDiv → Fin numChartVar
  /-- The Morse residual coordinates `z` (disjoint from the divisors), for the `‖z‖²` normal form
  (Codex §8 #4: the Morse core needs disjoint coords + a `‖z‖²` squeeze, not just a rank). -/
  resCoord : Fin resRank → Fin numChartVar

mutual
  /-- **The resolution tree** (map node: `resolution-tree`): a finite tree whose internal nodes are
  blow-up steps (`StepData`) with an EDGE-LABELLED chart cover as children (each `Edge` carries its
  case + substitution + child), leaves the fully-monomialised terminal states. -/
  inductive ResolutionTree (M : Fin (L + 1) → ℕ) where
    | leaf (l : LeafData M) : ResolutionTree M
    | branch (n : StepData M) (edges : List (Edge M)) : ResolutionTree M
  /-- A labelled edge of the tree: the chart's `case`, its `subst`itution, and the `child` subtree. -/
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
/-- All edges of the tree — the atlas's charts (each with its case + substitution). -/
def treeEdges {M : Fin (L + 1) → ℕ} : ResolutionTree M → List (Edge M)
  | leaf _ => []
  | branch _ edges => edgesEdges edges
/-- All edges reachable through a list of edges (that list + descendants'). -/
def edgesEdges {M : Fin (L + 1) → ℕ} : List (Edge M) → List (Edge M)
  | [] => []
  | e@(.mk _ _ c) :: es => e :: (treeEdges c ++ edgesEdges es)
end

/-- The terminal divisor exponents gathered across all leaves — the candidate set the threshold
`½·min` (Aoyagi p.22) reads off. -/
def terminalExponents {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : List ℕ :=
  (leaves t).flatMap (fun l => (List.finRange l.numDiv).map l.divExp)

end ResolutionTree

end DLNFibre.DLN.RLCT.Engine
