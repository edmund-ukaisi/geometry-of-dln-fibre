<task>
You are auditing a Lean 4 transcription of a resolution-of-singularities construction
(Aoyagi 2023, deep linear networks). I give you (A) the paper's page-pinned rules and
(B) the Lean code. Judge fidelity INDEPENDENTLY; do not assume the code is correct.

Setup / indexing conventions (from the paper):
- A width vector M = (M^(1), ..., M^(L+1)), L+1 widths, L matrices. In Lean M : Fin (L+1) → ℕ
  is 0-indexed: M(0)=M^(1), M(1)=M^(2), ..., M(L)=M^(L+1).
- Each exceptional divisor carries a rank-pattern vector T = (t^(1), ..., t^(L)) of length L
  (weakly decreasing, t^(L) can be 0). In Lean this is `divProfile : Fin numDiv → (Fin L → ℕ)`,
  so a single divisor's profile is `Fin L → ℕ`, 0-indexed: Lean index p (0..L-1) ↔ t^(p+1).
- The double induction runs over layers S = 1,2,...,L and a cleared-count J within each layer.
  In Lean the node stores `layer : ℕ` and `cleared : ℕ` (= J). The paper's S is 1-indexed;
  the Lean `layer` is 0-indexed, so (claimed) Lean layer = S - 1.
- The clearing level of a divisor is t̃ = min over the components of T.

(A) THE PAPER'S RULES (transcribed from the page images; treat as ground truth):

  Init: a fresh divisor's profile is set from the widths; t̃ = M(1) (the paper's notation).
  Def 4 (order): T ≤ T' iff t^(j) ≤ t'^(j) for all j (componentwise).

  The T-update at a blow-up step at layer S with cleared count J:
   - The TAIL positions t^(S), t^(S+1), ..., t^(L) are all set to J.
   - The HEAD positions t^(1), ..., t^(S-1) are:
       * case 1(1) (merge into an existing divisor): UNCHANGED (keep the parent's head).
       * case 1(2) (split off a new pivot from a parent divisor): INHERITED from that parent
         divisor's head, i.e. t^(i) := t^(i)_parent for i < S.
       * case 2 (new full-block pivot): RESET to the widths, t^(i) := M^(i+1) for i < S.
  The exponent update M_{s,k} at a step:
   - case 1(1): M' = M_parent + J₁·(M^(S+1) − J)   [J₁ = the run length to the next occupied level]
   - case 1(2): M' = M_parent + J₁·(M^(S+1) − J)
   - case 2:    M' = (M(S) − J)·(M^(S+1) − J)     [M(S) is the running min of widths up to S]

  Worked (3,3,4) values I want you to reproduce independently:
   - A case-1(1) merge at S=2, J=0, J₁=1 on a divisor with profile (1,1) and exponent 4:
     what is the resulting profile and exponent?
   - A case-2 step at S=2, J=0 (new full-block pivot): what is the resulting profile and exponent,
     given M(2)=min(3,3)=3?

(B) THE LEAN CODE (the transition `stepUpdate`; `n` is the parent node, `σ` the edge data with
`runLen`=J₁ and `mergeIdx`; `n.resRows` is meant to be M(S)−J, `n.resCols` is meant to be
M^(S+1)−J; `n.cleared` is J; `n.layer` is the 0-indexed layer):

  let setTail : (Fin L → ℕ) → (Fin L → ℕ) :=
    fun T p => if n.layer ≤ (p : ℕ) then n.cleared else T p
  match c with
  | case11 =>
      { numDiv := n.numDiv
        divExp := fun k => if (k:ℕ) = σ.mergeIdx then n.divExp k + σ.runLen * n.resCols
                            else n.divExp k
        divProfile := fun k => if (k:ℕ) = σ.mergeIdx then setTail (n.divProfile k)
                                else n.divProfile k
        cleared := n.cleared }
  | case12 =>
      { numDiv := n.numDiv + 1
        divExp := Fin.snoc n.divExp
          ((if h : σ.mergeIdx < n.numDiv then n.divExp ⟨σ.mergeIdx,h⟩ else 0) + σ.runLen * n.resCols)
        divProfile := Fin.snoc n.divProfile
          (setTail (if h : σ.mergeIdx < n.numDiv then n.divProfile ⟨σ.mergeIdx,h⟩ else fun _ => 0))
        cleared := n.cleared + 1 }
  | case2 =>
      { numDiv := n.numDiv + 1
        divExp := Fin.snoc n.divExp (n.resRows * n.resCols)
        divProfile := Fin.snoc n.divProfile (setTail (fun p => M p.succ))
        cleared := n.cleared + 1 }

QUESTIONS:
1. Does `setTail` correctly implement "tail positions t^(S..L) := J, head positions t^(1..S-1)
   unchanged", under the stated indexing (Lean layer = S-1, Lean profile index p ↔ t^(p+1))?
   In particular check the boundary: is the condition `n.layer ≤ p.val` (vs `<`, vs `n.layer-1`,
   vs `n.layer+1 ≤ p.val`) the right one? Work out which Lean indices are head vs tail at S=2
   (layer=1) for L=2 and confirm against the paper.
2. For case 2, is `fun p => M p.succ` the correct head-RESET value t^(i):=M^(i+1)? Check the
   index arithmetic: Lean head index p ↔ paper t^(p+1), which resets to M^(p+2); is M(p.succ)
   equal to M^(p+2) under the 0-indexed M?
3. Reproduce the two (3,3,4) worked values from (A) and check the Lean code yields them.
4. THE PRECONDITION QUESTION. A separate lemma about a case-1(1) merge on the construction state
   requires the hypothesis `layer < L` (strictly). It is used to prove that after the tail-write
   the clearing level t̃ = min(setTail ...) ≤ J (because the last coordinate, index L-1, is a tail
   coordinate and gets value J). Question: is `layer < L` the right precondition — i.e., does a
   case-1(1) merge only ever fire at a layer where `layer < L` holds? Given layers S run 1..L and
   Lean layer = S-1, what is the range of Lean `layer` for a real (non-terminal) blow-up step, and
   does `layer < L` hold throughout it? Could a case-1(1) merge ever fire at Lean layer = L, and if
   so what would go wrong (does setTail still create a tail coordinate)? A state invariant only
   provides `layer ≤ L`; is that enough, or must the recursion supply `layer < L` separately?
</task>

<output_contract>
Five short sections: Q1 (boundary verdict + the head/tail index split at S=2, L=2), Q2 (case-2
reset index verdict), Q3 (the two reproduced (3,3,4) values + match/mismatch to the code), Q4
(precondition verdict: is layer<L right, is it suppliable, is layer≤L enough), and a final
VERDICT line (FAITHFUL / MISMATCH-AT-Qn). Be concrete with numbers.
</output_contract>

<grounding_rules>
Distinguish what you COMPUTED from what you INFERRED. If the indexing convention forces an
assumption, state it. Flag any place the code is ambiguous rather than guessing.
</grounding_rules>
