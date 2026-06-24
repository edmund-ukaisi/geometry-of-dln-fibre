<task>
Lean 4 / Mathlib v4.29. I must fill ONE remaining `sorry`: the per-step degeneration crux of an
orbit-closure proof. EVERYTHING ELSE IS LANDED & GREEN (closure operator, rank-pattern bridge,
G_d-stability single-point⟹orbit, chain composition, assembly, primeness). I need the tightest proof
skeleton for the crux body, given the exact landed lemmas, to avoid thrash. Two cases (split c=b+1 /
nonsplit c≤b); the dimension-vector cast dg=d is the feared part.

THE GOAL (the sorry):
```
theorem boxMoveStep_repClosure_subset [Infinite k] {d : Fin (N + 1) → ℕ}
    {r r'' : ℤ → ℤ → ℤ} {Tp Tq : Tuple (k := k) d}
    (hrsupp : Supported (N:ℤ) r) (hr''supp : Supported (N:ℤ) r'')
    (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j) (hr''nn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r'' i j)
    (hrdiag : ∀ k : Fin (N+1), (d k:ℤ) = r k k) (hr''diag : ∀ k : Fin (N+1), (d k:ℤ) = r'' k k)
    (hp : ∀ i j hij, (rankPattern d Tp i j hij : ℤ) = r i j)
    (hq : ∀ i j hij, (rankPattern d Tq i j hij : ℤ) = r'' i j)
    (hstep : BoxMoveStep r r'') :
    repClosure (orbitSet Tq) ⊆ repClosure (orbitSet Tp)
```
where BoxMoveStep r r'' := ∃ a c b e : ℤ, a<c ∧ c≤b+1 ∧ b+1≤e ∧ 1≤diff r a e ∧ (c≤b → 1≤diff r c b)
  ∧ r'' = boxDrop r a c b e ;  boxDrop r a c b e = r - boxIndicator a c b e ;
  diff(boxDrop) = diff r − δ(a,e) − δ(c,b) + δ(a,b) + δ(c,e)  (via boxIndicator_diff; in split c=b+1
  the δ(c,b) corner is below-diagonal and the conclusion is only used on the triangle).

LANDED LEMMAS I CAN USE (exact names/signatures):
-- closure + bridge + stability (LANDED):
  repClosure_subset_of_subset_repClosure : S ⊆ repClosure T → repClosure S ⊆ repClosure T
  repClosure_mono, subset_repClosure, repClosure_idem
  repClosure_orbitSet_eq_of_rankPattern_eq {A B : Tuple d}
    (h : ∀ i j hij, rankPattern d A i j hij = rankPattern d B i j hij) :
    repClosure (orbitSet A) = repClosure (orbitSet B)
  orbitSet_subset_repClosure_orbitSet_of_canonical_mem {D U : Tuple d}
    (hD : canonicalCoord d D ∈ repClosure (orbitSet U)) : orbitSet D ⊆ repClosure (orbitSet U)
-- box bounds + realizer (LANDED):
  zero_le_of_diff_pos (hr:Supported N r)(hae:1≤diff r a e) : 0 ≤ a
  le_N_of_diff_pos  (hr:Supported N r)(hae:1≤diff r a e) : e ≤ N
  diffTri r hr : SuppArray N ℤ := ⟨fun i j ↦ if i≤j then diff r i j else 0, _⟩
  cumul_diffTri_eq (hr)(hij:i≤j) : cumul N (diffTri r hr).1 i j = r i j
  cMPlus_diffTri (hr)(hrnn)(hrdiag) : CMPlus d (diffTri r hr)
  patternRealizer (hr)(hrnn)(hrdiag) : Tuple d   -- = realizer (diffTri r hr) (cMPlus_diffTri ..)
  rankPattern_patternRealizer (hr)(hrnn)(hrdiag)(i j hij) :
    (rankPattern d (patternRealizer ..) i j hij : ℤ) = r i j
-- realizer machinery (LANDED, from OrbitKostant/IntervalModule/Orbit):
  realizer {d} (m : SuppArray N ℤ)(hm : CMPlus d m) : Tuple d := foldDim_listOfArray ▸ intervalDirectSum (listOfArray m)
  listOfArray (m : SuppArray N ℤ) : List (Fin(N+1)×Fin(N+1))
  multiplicityArray_listOfArray (m)(hm:CMPlus d m) : multiplicityArray (listOfArray m) = m.1
  foldDim_listOfArray (m)(hm:CMPlus d m) : foldDim (listOfArray m) = d
  rankPattern_realizer (m)(hm)(i j hij) : (rankPattern d (realizer m hm) i j hij : ℤ) = cumul N m.1 i j
  rankPattern_intervalDirectSum_eq_cumul (L)(i j hij) : (rankPattern (foldDim L)(intervalDirectSum L) i j hij:ℤ) = cumul N (multiplicityArray L) i j
  rankPattern_dirSum (A B)(i j hij) : rankPattern _ (dirSum A B) i j hij = rankPattern _ A i j hij + rankPattern _ B i j hij
  rankPattern_intervalModule (i j)(hij) : rankPattern (intervalDim i j)(intervalModule i j) i' j' hij = if i≤i' ∧ j'≤j then 1 else 0
  rankPattern_intervalModule_eq_cumul (i j)(hij:i'≤j') : (rankPattern .. : ℤ) = cumul N (singleDelta i j) i' j'
  rankPattern_transport (h:d₀=d)(X)(i j hij) : rankPattern d (h▸X) i j hij = rankPattern d₀ X i j hij
  cumul_singleDelta (a b i' j') : cumul N (singleDelta a b) i' j' = if a≤i' ∧ j'≤b then 1 else 0
  cumul_add (M m1 m2 i j) : cumul M (fun a b ↦ m1 a b + m2 a b) i j = cumul M m1 i j + cumul M m2 i j
  diff_cumul / cumul_diff (mutually inverse on Supported)
  cumul_kostantArrayOfRank_of_le, kostantArrayOfRank_of_le, kostantArrayOfRank_isKostant
-- THE GEOMETRIC PER-MOVE LEMMAS (LANDED), over dg, NOT d:
  splitMove_intervalDirectSum_mem_closure [Infinite k] (a e : Fin(N+1)) (b : Fin N) rest
    (hae : a ≤ b.castSucc)(hbe : b.succ ≤ e) :
    canonicalCoord dgS ((foldDim_splitCons_eq a e b rest hae hbe) ▸
        intervalDirectSum ((a,b.castSucc)::(b.succ,e)::rest))
      ∈ zeroLocus (vanishingIdeal (orbitSet (dirSum (intervalModule a e) (intervalDirectSum rest))))
    -- dgS := fun l ↦ intervalDim a e l + foldDim rest l
  nonsplitMove_intervalDirectSum_mem_closure [Infinite k] (a c e : Fin(N+1)) (b : Fin N) rest
    (hac:a<c)(hcb:c≤b.castSucc)(hbe:b.succ≤e) :
    canonicalCoord dgN ((foldDim_nonsplitCons_eq a c e b rest hac hcb hbe) ▸
        intervalDirectSum ((a,b.castSucc)::(c,e)::rest))
      ∈ zeroLocus (vanishingIdeal (orbitSet (dirSum (dirSum (intervalModule a e)(intervalModule c b.castSucc))(intervalDirectSum rest))))
    -- dgN := fun l ↦ (intervalDim a e l + intervalDim c b.castSucc l) + foldDim rest l
  NOTE zeroLocus(vanishingIdeal X) IS repClosure X (definitionally, σ=RepCoord, K=k=k).

THE PLAN for the crux body (my draft):
A. destruct hstep → a c b e : ℤ, ineqs, hae:1≤diff r a e, hcbm, hr''=boxDrop r a c b e.
B. bounds: ha0:0≤a (zero_le_of_diff_pos), heN:e≤N (le_N_of_diff_pos), and from a<c≤b+1≤e≤N derive
   c≤N, b+1≤N so b<N (i.e. b∈[0,N)), e≤N, also need c≥0 (a≥0,a<c), b≥0? (c≤b+1, but b could be -1 in
   split? a<c≤b+1 with a≥0 ⟹ b+1>a≥0 ⟹ b≥0). Convert: aF:=finOfInt a, cF:=finOfInt c, eF:=finOfInt e
   ∈ Fin(N+1); bF : Fin N from b∈[0,N).
C. By bridge: repClosure(orbitSet Tp) = repClosure(orbitSet (patternRealizer r ..)) and likewise Tq↔r''.
   (Tp,Tq realize r,r''; patternRealizer realizes r,r''; same rank pattern ⟹ same closure.) So reduce to
   repClosure(orbitSet (realizer r'')) ⊆ repClosure(orbitSet (realizer r)).
D. THE CAST: build rest := listOfArray (mRest) where mRest := the residual Kostant array
   = (diffTri r) minus δ(aF,eF) and (linked) δ(cF, bF.castSucc), truncated. Then:
   - geometric upstairs U := dirSum(dirSum M[aF,eF] M[cF,bF.cast]) (intervalDirectSum rest), over dgN.
   - prove dgN = d (diagonal cumul identity), giving cast h:dgN=d.
   - prove rankPattern (h ▸ U) = r on triangle (rankPattern_dirSum + intervalModule + intervalDirectSum
     = cumul(δ+δ+mRest)=cumul(diffTri r)=r).  ⟹ by bridge repClosure(orbitSet (h▸U)) = repClosure(orbitSet (realizer r)).
   - similarly downstairs D' := the (a,b)::(c,e)::rest interval sum cast to d, rankPattern = r''.
   - geometric lemma: canonicalCoord dgN (.. downstairs ..) ∈ repClosure(orbitSet U).
     transport the cast: canonicalCoord d (h▸downstairs) ∈ repClosure(orbitSet (h▸U)).
   - so canonicalCoord d (h▸downstairs) ∈ repClosure(orbitSet (realizer r)); and h▸downstairs has rank
     pattern r'' = rankPattern (realizer r''), so by bridge orbitSet(h▸downstairs)=orbitSet(realizer r''),
     and by orbitSet_subset_repClosure_orbitSet_of_canonical_mem + single point ⟹ whole orbit, done.

QUESTIONS — give the SHARPEST guidance:
1. Is step C correct (reduce Tp/Tq to patternRealizer via the bridge first)? Or should I keep Tp,Tq and
   only bridge the geometric witnesses to them directly (skip patternRealizer)? Which has fewer casts?
2. The dimension cast dgN=d: I want to AVOID transporting U and downstairs with `h▸` if possible.
   Codex earlier said "prove rank lemmas over dg, transport once". Concretely: do I (i) define mRest and
   rest, prove dgN=d via the cumul-diagonal chain, then `subst`/`h▸` the geometric membership to d; or
   (ii) is there a way to keep everything at dgN and use the bridge at dgN (i.e. realize r,r'' by tuples
   over dgN instead of d)? The chain forces Tp,Tq over d. So I think (i). Confirm + give the exact
   cumul-diagonal identity dgN t = d t as a rewrite chain (intervalDim aF eF t = cumul(singleDelta aF eF) t t
   via rankPattern_intervalModule_eq_cumul+rankPattern_self?, foldDim rest t = cumul(mRest) t t).
3. Building mRest: the residual diff r − δ(aF,eF) − δ(cF,bF.cast). Is it IsKostantArray (nonneg on
   triangle? δ subtractions: diff r aF eF ≥ 1 so subtracting δ(aF,eF) keeps ≥0 AT (aF,eF); but at OTHER
   cells δ=0 so unchanged ≥0; the (cF,bF) corner similarly needs diff r cF bF ≥ 1 = hcbm, only in linked
   case)? AND supported, AND below-diag-0 (truncate)? Give the cleanest mRest definition (a SuppArray)
   and the proof obligations. Should mRest be `diffTri r` minus deltas truncated, i.e.
   ⟨fun i j ↦ if i≤j then (diff r i j − δ(aF,eF) − δ(cF,bF)) else 0, _⟩? Is it cleaner to define mRest
   and then prove cumul(δ(aF,eF)+δ(cF,bF)+mRest) = cumul(diffTri r) = r on the triangle?
4. SPLIT vs NONSPLIT: in split c=b+1, there's NO M[cF,bF] summand and the upstairs is
   dirSum M[aF,eF] (intervalDirectSum rest), downstairs (aF,bF.cast)::(bF.succ,eF)::rest. The residual
   mRest = diff r − δ(aF,eF) only. Should I do TWO separate branches (by_cases c≤b) each ~full, or is
   there a unifying formulation? The geometric lemmas have DIFFERENT shapes (split: 1 module + rest;
   nonsplit: 2 modules + rest). I think two branches. Confirm and say which is simpler to do first.
5. Biggest landmine you foresee in this body + how to preempt it. Estimate line count per branch.
</task>

<output_contract>
Five numbered answers, terse + concrete (Lean tactic-level where it matters). For Q2 give the explicit
cumul-diagonal rewrite chain. For Q3 give the exact mRest SuppArray definition + the cumul identity to
prove. For Q4 say split-first or nonsplit-first and why. For Q5 name the landmine + line estimate.
</output_contract>

<grounding_rules>
Assume listed signatures accurate. Flag any needed lemma NOT listed (e.g. "foldDim of listOfArray's
diagonal = cumul mRest diagonal — you need foldDim_eq_cumul_multiplicityArray_diag which you must
prove", or "intervalDim aF eF t = cumul(singleDelta) diagonal needs a helper"). Distinguish
"architecturally fine" from "irreducible grind". No full proofs; skeleton + key rewrites only.
</grounding_rules>
