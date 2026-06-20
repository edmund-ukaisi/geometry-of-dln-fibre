<task>
Lean 4 / Mathlib v4.29. Closing the per-step degeneration lemma (piece 2) of an orbit-closure proof.
Pieces 1 (closure operator repClosure) and the rank-pattern bridge are LANDED and green:

  repClosure {d} (S : Set (RepCoord d → k)) : Set (RepCoord d → k)
    := zeroLocus (vanishingIdeal S)         -- Zariski closure, monotone/extensive/idempotent
  repClosure_subset_of_subset_repClosure : S ⊆ repClosure T → repClosure S ⊆ repClosure T
  -- THE BRIDGE (needs A B over the SAME dimension vector d):
  repClosure_orbitSet_eq_of_rankPattern_eq {d} {A B : Tuple d}
    (h : ∀ i j hij, rankPattern d A i j hij = rankPattern d B i j hij) :
    repClosure (orbitSet A) = repClosure (orbitSet B)

The GEOMETRIC per-move lemmas (LANDED) land downstairs ∈ closure(orbit upstairs), but over a
GEOMETRIC dimension vector, NOT the chain's fixed d. E.g. non-split:

  nonsplitMove_intervalDirectSum_mem_closure [Infinite k] (a c e : Fin(N+1)) (b : Fin N) rest
    (hac:a<c)(hcb:c≤b.castSucc)(hbe:b.succ≤e) :
    canonicalCoord dg ((foldDim_nonsplitCons_eq ..) ▸ intervalDirectSum ((a,b.castSucc)::(c,e)::rest))
      ∈ zeroLocus (vanishingIdeal (orbitSet
          (dirSum (dirSum (intervalModule a e) (intervalModule c b.castSucc)) (intervalDirectSum rest))))
   -- where dg := fun l ↦ (intervalDim a e l + intervalDim c b.castSucc l) + foldDim rest l

I have the box-move chain over ℤ-arrays. Each BoxMoveStep r r'' carries box coords (a,c,b,e : ℤ),
r achievable (diff r ≥ 0), supported, with diff r a e ≥ 1 and (linked) diff r c b ≥ 1, and
r'' = boxDrop r a c b e so diff r'' = diff r − δ(a,e) − δ(c,b) + δ(a,b) + δ(c,e).

THE CONCRETE OBSTACLE. I want the per-step conclusion in a form the CHAIN can compose, i.e. over a
FIXED d (the dimension vector of M). But:
 - The geometric lemma's tuples live over dg = (intervalDim a e + intervalDim c b.castSucc) + foldDim rest.
 - The chain's realizers live over d (= cumul(diff r) on the diagonal).
 - I need rest : List with multiplicityArray rest = diff r − δ(a,e) − δ(c,b), via listOfArray of that
   residual SuppArray, and then dg = d requires foldDim((a,b)::(c,e)::rest) = d, i.e. a foldDim_listOfArray
   computation (which holds: diagonal of cumul gives d).

Available realizer machinery (LANDED):
  CMPlus d (m : SuppArray N ℤ) : Prop := IsKostantArray m ∧ ∀ k, (d k:ℤ) = cumul N m.1 k k
  realizer {d} (m : SuppArray N ℤ) (hm : CMPlus d m) : Tuple d := foldDim_listOfArray ▸ intervalDirectSum (listOfArray m)
  rankPattern_realizer (m hm) (i j hij) : (rankPattern d (realizer m hm) i j hij : ℤ) = cumul N m.1 i j
  multiplicityArray_listOfArray (m) (hm : CMPlus d m) : multiplicityArray (listOfArray m) = m.1
  foldDim_listOfArray (m) (hm : CMPlus d m) : foldDim (listOfArray m) = d
  rankPattern_intervalDirectSum_eq_cumul (L) (i j hij) : (rankPattern (foldDim L) (intervalDirectSum L) i j hij : ℤ) = cumul N (multiplicityArray L) i j
  rankPattern_dirSum (A B) (i j hij) : rankPattern _ (dirSum A B) i j hij = rankPattern _ A i j hij + rankPattern _ B i j hij
  rankPattern_intervalModule, rankPattern_transport (h : d₀=d) (X) : rankPattern d (h ▸ X) i j hij = rankPattern d₀ X i j hij
  cumul_add, cumul_singleDelta (a b i' j') : cumul N (singleDelta a b) i' j' = [a≤i' ∧ j'≤b]
  diff_cumul (N m) (hi hj) : diff (cumul N m) = m ;  cumul_diff (N r)(hi hj): cumul N (diff r) = r  (on Supported)

QUESTION. Whats the LEAST-cast way to assemble the per-step lemma so the chain composes? Two candidate
shapes:

(S1) State per-step entirely at the GEOMETRIC dimension vector dg and never convert to d. I.e. the chain
itself runs over the realizers, and at the END (piece 4) I transport once. But the chain links r → r'' →
r''' have DIFFERENT geometric dg at each step (each box move has its own a,c,b,e,rest). So composing
repClosure inclusions across steps needs them all over the SAME ambient d anyway (repClosure is typed by
d). => S1 seems to FORCE a per-step transport to d. Correct?

(S2) State per-step over the FIXED d, conclusion:
   repClosure (orbitSet (realizer (diff r'' truncated)) ) ⊆ repClosure (orbitSet (realizer (diff r)))
 proved by: build rest := listOfArray (residual), show dg = d (foldDim computation), transport the
 geometric tuples (dg ▸ ·) to d, apply the bridge twice (geometric-upstairs ↔ realizer r; geometric-
 downstairs ↔ realizer r'') and repClosure_subset_of_subset_repClosure. The bridge needs the geometric
 tuple cast to d via (h : dg = d) ▸; rankPattern_transport handles the cast inside the rank computation.

Specifically for S2:
(a) Is `(h : dg = d) ▸ (geometric tuple)` the right way to move a Tuple dg to Tuple d, and does
    rankPattern_transport then let me compute its rank pattern as the dg-rank pattern? Any defeq landmine
    with the DOUBLE cast (the geometric lemma ALREADY has a `foldDim_nonsplitCons_eq ▸` inside)?
(b) The geometric membership is `canonicalCoord dg (castedThing) ∈ zeroLocus(vanishingIdeal(orbitSet U_dg))`.
    To feed repClosure_subset_of_subset_repClosure I need this as `orbitSet (D_d) ⊆ repClosure (orbitSet U_d)`
    where D_d, U_d are over d. The membership is a SINGLE point (canonicalCoord of the downstairs), not the
    whole orbitSet D. How do I get the whole `orbitSet D_d ⊆ repClosure(orbitSet U_d)` from one point +
    rank-pattern bridge? (orbitSet is G_d-invariant and repClosure(orbitSet U) is closed and G_d-stable?
    Is repClosure(orbitSet U) G_d-stable — do I need that, or does the bridge orbitSet D = orbitSet(single
    witness) suffice because the witness IS canonicalCoord of a representative whose orbit is all of orbitSet D?)
(c) The residual SuppArray m_rest = diff r − δ(a,e) − δ(c,b): proving CMPlus d_rest m_rest where d_rest is
    its own diagonal — but I need foldDim rest to combine with intervalDim a e + intervalDim c b to give d.
    Is it cleaner to (i) prove CMPlus (someDimVec) m_rest and let foldDim_listOfArray give foldDim rest =
    that dimvec, then show intervalDim a e + intervalDim c b + that = d by a cumul-diagonal computation; or
    (ii) avoid CMPlus entirely and just use multiplicityArray_listOfArray (which needs CMPlus too)? Is there
    a lighter realizer that needs only "nonneg + supported + below-diag-vanish" without the dimension eqn?

Give me the SHARPEST path. If S2 is right, give the exact statement of the per-step lemma over d and the
3-5 sub-lemmas (with the cumul-diagonal dim computation spelled out). If there's a lighter route I'm
missing (e.g. proving orbitSet D ⊆ repClosure(orbitSet U) directly from the single-point membership +
G_d-stability of repClosure(orbitSet ·)), say so and give that lemma.
</task>

<output_contract>
1. S1 vs S2 verdict (one line + reason).
2. The exact per-step lemma statement over fixed d you'd write.
3. The single-point-membership → whole-orbitSet-inclusion step: state the lemma and its proof idea
   (is repClosure(orbitSet U) G_d-stable needed? if so, how to prove it cheaply?).
4. The residual CMPlus / dimension-vector computation: which sub-route (i vs ii vs lighter realizer), and
   the cumul-diagonal identity that proves dg = d, as an explicit chain of rewrites.
5. Landmines with the double `▸` cast and how to avoid (subst? rankPattern_transport ordering?).
</output_contract>

<grounding_rules>
Assume listed signatures are accurate. Flag any step needing a lemma I did NOT list (e.g. "orbitSet is
G_d-stable as a set", "repClosure of a G_d-stable set is G_d-stable", "single point's orbit = orbitSet").
Distinguish architectural dissolves from irreducible grind. Signatures + proof ideas only, no full proofs.
</grounding_rules>
