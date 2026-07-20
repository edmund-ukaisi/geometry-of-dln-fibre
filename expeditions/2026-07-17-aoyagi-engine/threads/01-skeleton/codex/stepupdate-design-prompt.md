<task>
Lean 4 + Mathlib v4.29 formalisation. I am building the "construction tide" of a resolution-tree
engine (Aoyagi's DLN blow-up resolution). RUNG 1 is a typed `stepUpdate` + a FAITHFUL re-point of the
per-edge relation `StepRel`. I need a design adjudication on the OUTPUT TYPE and whether the faithful
equality can be discharged rfl-class, BEFORE I build it.

## The current carrier (verbatim, elaborates green today)

```lean
inductive StepCase | case11 | case12 | case2   -- deriving DecidableEq, Repr

structure ChartSubst (M : Fin (L + 1) → ℕ) where
  localSub    : Params M → Params M   -- coordinate change (self-map of param space)
  runLen      : ℕ                     -- Case-1 equal-run length J₁
  jacDivCount : ℕ
  jacPow      : Fin jacDivCount → ℕ

structure StepData (M : Fin (L + 1) → ℕ) where
  layer   : ℕ                          -- S
  cleared : ℕ                          -- J
  resRows : ℕ                          -- M(S)-J
  resCols : ℕ                          -- M(S+1)-J
  numDiv  : ℕ
  numB    : ℕ
  bExp    : Fin numB → (Fin numDiv → ℕ)
  bChain  : Monotone bExp
  divExp  : Fin numDiv → ℕ             -- M_{s,k}
  divTilde: Fin numDiv → ℕ             -- t̃_{s,k} (clearing level)
  numGen  : ℕ
  support : Fin numGen → Finset (Fin numDiv)   -- sharing map (typed; flatten = type error)

structure LeafData (M : Fin (L + 1) → ℕ) where
  numDiv     : ℕ
  divExp     : Fin numDiv → ℕ
  divProfile : Fin numDiv → (Fin L → ℕ)
  numB : ℕ ; bExp : Fin numB → (Fin numDiv → ℕ) ; bChain : Monotone bExp
  chartMap : Params M → Params M ; srcBox : Set (Params M) ; resRank : ℕ
  divCoord : Fin numDiv → Fin (flatDim M) ; resCoord : Fin resRank → Fin (flatDim M)

mutual
  inductive ResolutionTree (M) | leaf (l : LeafData M) | branch (n : StepData M) (edges : List (Edge M))
  inductive Edge (M) | mk (case : StepCase) (subst : ChartSubst M) (child : ResolutionTree M)
end
-- Edge.case/.subst/.child projections exist.

-- root-ledger accessors on the child subtree:
def rootNumDiv  : ResolutionTree M → ℕ            | leaf l => l.numDiv | branch n _ => n.numDiv
def rootDivExp  : ResolutionTree M → ℕ → ℕ         -- l.divExp ⟨k,_⟩ if k<numDiv else 0 (both cases)
def rootCleared : ResolutionTree M → ℕ            | leaf _ => 0 | branch n _ => n.cleared
```

## Current (downscoped) StepRel — an existence-CONSISTENCY check (to be replaced)

```lean
def StepRel (n : StepData M) (e : Edge M) : Prop :=
  (e.case = .case2  → (∃ kp : Fin n.numDiv, ∀ g, kp ∈ n.support g) ∧
                      (∃ kc : ℕ, kc < rootNumDiv e.child ∧ rootDivExp e.child kc = n.resRows*n.resCols)) ∧
  (e.case = .case11 → ∃ kp : Fin n.numDiv, n.divTilde kp = n.cleared ∧
                      (∃ kc : ℕ, kc < rootNumDiv e.child ∧
                        rootDivExp e.child kc = n.divExp kp + e.subst.runLen * n.resCols)) ∧
  (e.case = .case12 → rootCleared e.child = n.cleared + 1 ∧ 0 < rootNumDiv e.child)
```
The existential form is UNFAITHFUL (a dummy divisor may appear/vanish across an edge unchecked).

## The paper transitions (Aoyagi preprint p.16, verified against the page image)

- **case 1(1) merge**: one existing divisor u_{s,k} with t̃=J+J₁ gets exponent
  `M'_{s,k} = M_{s,k} + J₁·(M^{(S+1)}−J)` = parent divExp + runLen·resCols; its t̃ becomes J; and "the
  count of u's with t̃=J+J₁ is decremented by one" (inner recursion; S,J unchanged).
- **case 1(2) pivot**: introduces a NEW divisor u_{S,J+1}; advances (J or S).
- **case 2 full block**: introduces a NEW shared divisor of exponent `resRows·resCols`; clears the full block.

## The target (fork 9 + elder ratification)

Define `stepUpdate : StepData M → StepCase → ChartSubst M → <child root ledger>` computing the child's
root ledger from the parent + case + subst, and re-point `StepRel n e := (child's root ledger) =
stepUpdate n e.case e.subst`. Since the construction will BUILD each child via stepUpdate, the equality
should be rfl-class. GUARD: if this is not the natural definitional shape or the equality balloons (the
sharing bookkeeping — `support`/`numGen`/the per-divisor injection — is the named risk), I STOP-AND-SURFACE
and take a permanent downscope. Grinding is the wrong move.

Key tension: `stepUpdate` takes only `(StepData, StepCase, ChartSubst)`. But case-1(1) must know WHICH
divisor merges (the one with t̃=J+J₁), and case-2 which is the shared divisor. Determinism requires either
(a) a canonical choice derivable from the StepData (e.g. "all divisors with divTilde = cleared+runLen"),
or (b) an added transition-index field on ChartSubst/Edge.
</task>

<output_contract>
Answer these, briefly and concretely, in this order:

1. OUTPUT TYPE. What should `<child root ledger>` be? Rank: (i) a lightweight record
   `{numDiv, divExp, divTilde, cleared}` (exponent+clearing core, NO support) with a projection
   `rootLedger : ResolutionTree M → that`, vs (ii) the same PLUS `{numGen, support}`, vs (iii) a full
   new `StepData`. For each, say whether `rootLedger child = stepUpdate parent e` can be **rfl-class**
   in a construction that builds children via stepUpdate, and where dependent-`Fin`/`Finset` re-indexing
   would make it balloon.

2. DETERMINISM. Should the case-1(1) merge target (and case-2 shared divisor) come from a canonical
   StepData-derived choice, or from an added field on ChartSubst/Edge? Which keeps stepUpdate a total
   function AND keeps the equality rfl-class? Give the concrete field(s) if you recommend adding.

3. SUPPORT PROPAGATION — the balloon test. Is including `support : Fin numGen → Finset (Fin numDiv)`
   in the equality (i.e. comparing propagated Finsets across the per-divisor injection) a genuine
   balloon that should trigger STOP-AND-SURFACE, or is there a natural definitional shape (e.g. deriving
   support from a `genDivExp : Fin numGen → Fin numDiv → ℕ` multiplicity ledger) that keeps it rfl-class?
   Give a clear GO / STOP-AND-SURFACE recommendation with the reason.

3b. If STOP-AND-SURFACE on support: what is the honest minimal rung-1 (ledger core only) that still
    (a) discharges rfl-class on a hand-built (2,2,4) witness, and (b) rejects the dummy-divisor tree
    (a divisor appearing/vanishing across an edge) via a ¬-theorem?

4. RFL-CLASS DISCHARGE. For the witness (a HAND-built tree, not via the construction), what makes
   `rootLedger child = stepUpdate parent e` provable — literal `rfl`, `decide`, or `simp`+`decide`? Any
   `Fin numDiv` OfNat / motive pitfalls at v4.29 to pre-empt?

5. DUMMY-DIVISOR ¬-THEOREM. Sketch the cleanest in-file rejection witness: a tree with an edge whose
   child ledger differs from stepUpdate(parent) by an extra/missing divisor, and `¬ StepRel n e`.
</output_contract>

<grounding_rules>
This is a design/diagnosis consult. Flag any recommendation that assumes a Mathlib lemma you are not
certain exists at v4.29 as "verify". Distinguish "this is the natural shape" (design judgment) from
"this will elaborate" (needs a build). The recipe is illustrative; I will elaborate everything locally.
Prioritise the GO / STOP-AND-SURFACE call on support (item 3) — that is the decision I am buying.
</grounding_rules>

<execution_constraint>
DO NOT run any shell commands, do not explore the repository, do not invoke lake/lean/rg. This is a
PURE DESIGN question — reason only from the Lean types pasted above. Emit your answer directly.
</execution_constraint>
