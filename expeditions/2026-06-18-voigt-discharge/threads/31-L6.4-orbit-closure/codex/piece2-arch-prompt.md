<task>
Lean 4 / Mathlib v4.29 formalisation. I am proving the orbit-closure equality (Abeasis–Del Fra) for
equioriented type-A quiver representations, at the ideal level. The headline I want:

  vanishingIdeal (canonicalCoord '' orbitRankLocus M) = vanishingIdeal (orbitSet M)

and then primeness of the LHS (from the RHS being prime). The EASY inclusion (≤) is landed. I need the
HARD inclusion: orbitRankLocus M ⊆ repClosure (orbitSet M), where
  repClosure S := zeroLocus (vanishingIdeal (canonicalCoord '' S))   -- the Zariski closure operator
over the SAME base field k (read/write same field, K = k in Mathlib's zeroLocus/vanishingIdeal).

I have ALL the bricks. The key objects and lemmas (exact signatures):

-- Tuples and flattening
  Tuple (k:=k) d                       -- composable matrix tuple over dim vector d : Fin (N+1) → ℕ
  canonicalCoord d : Tuple d ≃ (RepCoord d → k)   -- linear flattening
  orbitSet M : Set (RepCoord d → k) := canonicalCoord d '' { A | ∃ P : BaseChangeGroup d, P • M = A }
  rankPattern d A i j hij : ℕ         -- = (submult d A i j).rank, for i ≤ j : Fin (N+1)
  orbitRankLocus M : Set (Tuple d) := { A | ∀ i j h, rankPattern d A i j h ≤ rankPattern d M i j h }

-- Complete invariant (Cor 2.9):
  rankPattern_eq_iff_orbit (A B : Tuple d) :
    (∀ i j hij, rankPattern d A i j hij = rankPattern d B i j hij) ↔ ∃ P : BaseChangeGroup d, P • A = B

-- Gabriel normal form: every tuple is G_d-equivalent to a reindexed interval direct sum of its bars:
  baseChange_normalForm (A : Tuple d) :
    ∃ (L : List (Fin(N+1)×Fin(N+1))) (h : foldDim L = d) (P : BaseChangeGroup d),
      P • A = h ▸ intervalDirectSum L ∧ (∀ p∈L, p.1≤p.2) ∧
      ∀ i j hij, (rankPattern d A i j hij : ℤ) = cumul N (multiplicityArray L) i j
  -- where intervalDirectSum L : Tuple (foldDim L) is dirSum-folded interval modules,
  -- multiplicityArray L : ℤ→ℤ→ℤ counts intervals, cumul/diff are the IE-inversion (mutually inverse on
  -- Supported arrays), and diff(cumul m)=m.

-- Combinatorial box-move chain (landed):
  BoxMoveStep (r r' : ℤ→ℤ→ℤ) : Prop :=
    ∃ a c b e : ℤ, a<c ∧ c≤b+1 ∧ b+1≤e ∧ (1≤diff r a e) ∧ (c≤b → 1≤diff r c b) ∧ r' = boxDrop r a c b e
  -- boxDrop r a c b e = r - boxIndicator a c b e (a 4-corner second-difference move:
  --   diff drops m_{[a,e]} by 1, m_{[c,b]} by 1 (linked case c≤b), raises m_{[a,b]} and m_{[c,e]} by 1)
  BoxMoveChain r s := Relation.ReflTransGen BoxMoveStep r s
  box_move_chain_of_le (N:ℤ) (r s : ℤ→ℤ→ℤ)
    (hsupp : Supported N (fun i j ↦ r i j - s i j)) (hpos : ∀ i j, 0 ≤ r i j - s i j)
    (hbelow : ∀ i j, j ≤ i → r i j - s i j = 0) (hms : ∀ i j, 0 ≤ diff s i j) :
    BoxMoveChain r s

-- Per-move geometric degeneration (landed) — TWO versions, both land downstairs ∈ closure(orbit upstairs):
  -- SPLIT (c = b+1), arbitrary rest, Lup = (a,e)::rest, Ldn = (a,b.castSucc)::(b.succ,e)::rest:
  splitMove_intervalDirectSum_mem_closure [Infinite k] (a e : Fin(N+1)) (b : Fin N) rest
    (hae : a ≤ b.castSucc) (hbe : b.succ ≤ e) :
    canonicalCoord _ ((foldDim_splitCons_eq ..) ▸ intervalDirectSum ((a,b.castSucc)::(b.succ,e)::rest))
      ∈ zeroLocus (vanishingIdeal (orbitSet (dirSum (intervalModule a e) (intervalDirectSum rest))))
  -- NONSPLIT (a<c≤b<e), arbitrary rest, upstairs base LEFT-ASSOCIATED:
  nonsplitMove_intervalDirectSum_mem_closure [Infinite k] (a c e : Fin(N+1)) (b : Fin N) rest
    (hac : a<c) (hcb : c ≤ b.castSucc) (hbe : b.succ ≤ e) :
    canonicalCoord _ ((foldDim_nonsplitCons_eq ..) ▸ intervalDirectSum ((a,b.castSucc)::(c,e)::rest))
      ∈ zeroLocus (vanishingIdeal (orbitSet
          (dirSum (dirSum (intervalModule a e) (intervalModule c b.castSucc)) (intervalDirectSum rest))))

The intended 5-piece plan:
 1. closure-operator algebra (extensive/monotone/idempotent + "canonicalCoord '' S ⊆ repClosure T → repClosure S ⊆ repClosure T") — easy, Galois connection.
 2. PER-STEP in closure form: BoxMoveStep r r'' → repClosure (orbitSet (nf r'')) ⊆ repClosure (orbitSet (nf r')),
    where nf p = intervalDirectSum (the Gabriel partition with multiplicities diff p). THIS IS THE CRUX.
 3. chain composition by ReflTransGen induction.
 4. assembly: A ∈ orbitRankLocus M ⟹ s=rankPattern A ≤ r=rankPattern M, box_move_chain_of_le + piece 3,
    A ∈ orbitSet(nf s) ⊆ repClosure(orbitSet(nf s)) ⊆ repClosure(orbitSet(nf r)) = repClosure(orbitSet M).
 5. primeness: rewrite + isPrime_vanishingIdeal_orbitSet.

THE PROBLEM with piece 2 as literally stated: a BoxMoveStep on the ℤ-array r' = boxDrop r a c b e gives
the upstairs/downstairs multiplicity arrays, but turning "nf r' " and "nf r'' " into the EXACT list shapes
(a,e)::(c,b)::rest and (a,b)::(c,e)::rest that the geometric lemmas demand requires: (i) extracting the
ℤ-coords a,c,b,e back to Fin(N+1)/Fin N; (ii) decomposing the partition list of r' as a permutation of
(a,e)::(c,b)::rest; (iii) the geometric lemma's upstairs orbit base is LEFT-ASSOCIATED dirSum, not defeq to
intervalDirectSum of any single list; (iv) intervalDirectSum is only well-defined up to list permutation
(via rankPattern_eq_iff_orbit, since permuting the list preserves the rank pattern ⟹ same orbit ⟹ same
closure). This multiset/assoc bookkeeping is the feared thrash.

KEY QUESTION: What is the CLEANEST architecture for piece 2 + the glue that minimises the multiset/assoc
pain? Specifically:

(A) Should I phrase the per-step lemma directly on BoxMoveStep at the ℤ-array level, or instead introduce a
helper "orbit-closure of a rank pattern" set R(p) := orbitSet (any tuple with rank pattern = cumul(...))
and prove a permutation/orbit-invariance lemma "same rank pattern ⟹ same repClosure(orbitSet)" ONCE, so
that the geometric lemma's left-associated base and my chosen list shape are reconciled by the complete
invariant rather than by defeq?

(B) Concretely: define repClosureRP (p : ℤ→ℤ→ℤ) [for an achievable, supported p] := repClosure (orbitSet T_p)
for ANY tuple T_p whose rankPattern = cumul of (diff p) — well-defined because rankPattern_eq_iff_orbit makes
the orbitSet (hence repClosure) depend only on the rank pattern. Then piece 2 becomes: BoxMoveStep r r'' ⟹
repClosureRP r'' ⊆ repClosureRP r'. And the geometric per-move lemma is invoked with its OWN list shape; I
reconcile both sides to repClosureRP by the "same rank pattern ⟹ same repClosure" lemma, never matching
list shapes by defeq. Is this the right factoring? What is the cleanest way to state "orbitSet depends only
on rank pattern" and "repClosure(orbitSet) depends only on rank pattern" so that both the LEFT-ASSOCIATED
geometric base AND my list-shaped nf land on the same repClosureRP?

(C) For extracting (a,c,b,e : the box coords) from a BoxMoveStep and matching them to Fin-indexed interval
endpoints: the BoxMoveStep coords are ℤ with 0 ≤ a < c ≤ b+1 ≤ e ≤ N (are these bounds derivable? the
chain is built from exists_boxMoveStep_descent which gives 0≤a, a<c, c≤b+1, b+1≤e, e≤N). Is converting
ℤ-coords-in-[0,N] to Fin(N+1) the right move, or should I instead prove the per-step degeneration entirely
at the ℤ-array / rank-pattern level (showing the two rank patterns differ by the 4-corner move and that the
downstairs is in the closure of the upstairs orbit) WITHOUT ever naming the Fin endpoints — i.e. is there a
formulation of the geometric per-move lemma purely in terms of "rank pattern r vs r-1_D" that I should prove
as the bridge, reusing splitMove/nonsplitMove only at the very end for a single canonical witness?

(D) Risk ranking: of the four pain sources (i)-(iv) above, which is the genuine blocker and which dissolve
under the repClosureRP factoring? If the whole thing is likely to exceed ~8 failed attempts, what is the
minimal CONDITIONAL skeleton (piece 1+3+4+5 + a precisely-stated per-step lemma as hypothesis) that still
banks maximal value, and exactly how should the per-step lemma be stated so the conditional is honest and
the residual is a single clean obligation?
</task>

<output_contract>
Four sections, terse and concrete (this is Lean architecture advice, not prose):
1. VERDICT on the repClosureRP factoring (A/B): adopt as-is / modify / reject, with the one-line reason.
2. The CLEANEST per-step lemma statement(s) — give the Lean-ish signature(s) you'd actually write, including
   the "same rank pattern ⟹ same repClosure(orbitSet)" bridge lemma and how the left-associated geometric
   base is absorbed.
3. The (a,c,b,e) extraction (C): ℤ→Fin conversion vs pure-rank-pattern bridge — pick one, say why, and name
   the 2-3 sub-lemmas it needs.
4. Risk ranking of (i)-(iv) + the minimal honest CONDITIONAL skeleton if piece 2 thrashes (exact per-step
   hypothesis to assume).
</output_contract>

<grounding_rules>
You may assume the listed signatures are accurate (I pasted them from the source). Flag any place where
your advice DEPENDS on a lemma I have NOT listed (e.g. "this needs a permutation-invariance of
intervalDirectSum's rank pattern, which you must prove"). Distinguish "this dissolves the pain" (architectural
claim) from "you'll still need to grind this" (irreducible work). Do not write full proofs; signatures +
the key proof idea per lemma only.
</grounding_rules>
