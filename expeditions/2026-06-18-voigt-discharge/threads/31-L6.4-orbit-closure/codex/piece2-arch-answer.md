**1. VERDICT**

Adopt, but slightly modify: define `repClosureRP` by an explicit witness tuple plus a proof of its rank pattern, and prove witness-independence once. Reason: it makes permutation, reassociation, and normal-form choices irrelevant because `rankPattern_eq_iff_orbit` upgrades “same rank pattern” to “same orbit/closure”.

**2. CLEANEST Per-Step Lemmas**

Core bridge:

```lean
lemma orbitSet_eq_of_rankPattern_eq
    {A B : Tuple (k:=k) d}
    (h : ∀ i j hij, rankPattern d A i j hij = rankPattern d B i j hij) :
    orbitSet A = orbitSet B := by
  -- use rankPattern_eq_iff_orbit A B to get ∃ P, P • A = B
  -- then prove equality of orbits under group action
```

Then closure bridge:

```lean
lemma repClosure_orbitSet_eq_of_rankPattern_eq
    {A B : Tuple (k:=k) d}
    (h : ∀ i j hij, rankPattern d A i j hij = rankPattern d B i j hij) :
    repClosure (orbitSet A) = repClosure (orbitSet B) := by
  rw [orbitSet_eq_of_rankPattern_eq h]
```

For the RP wrapper, avoid quotienting if possible. Use a structure:

```lean
structure RankPatternWitness (d : Fin (N+1) → ℕ) where
  T : Tuple (k:=k) d
  pattern : ℤ → ℤ → ℤ
  hpattern :
    ∀ i j hij, (rankPattern d T i j hij : ℤ) = pattern i j
```

Then:

```lean
def repClosureRP (W : RankPatternWitness (k:=k) d) :
    Set (RepCoord d → k) :=
  repClosure (orbitSet W.T)

lemma repClosureRP_eq_of_same_pattern
    {W W' : RankPatternWitness (k:=k) d}
    (h : ∀ i j, W.pattern i j = W'.pattern i j) :
    repClosureRP W = repClosureRP W' := by
  apply repClosure_orbitSet_eq_of_rankPattern_eq
  intro i j hij
  exact_mod_cast W.hpattern i j hij.trans (h i j) -- schematic
```

The per-step lemma I would actually target:

```lean
lemma boxMoveStep_repClosureRP_subset
    [Infinite k]
    {d : Fin (N+1) → ℕ}
    {Wup Wdn : RankPatternWitness (k:=k) d}
    (hstep : BoxMoveStep Wup.pattern Wdn.pattern) :
    repClosureRP Wdn ⊆ repClosureRP Wup := by
  -- destruct hstep
  -- build the split/nonsplit geometric witnesses with their own list/assoc shape
  -- prove their rank patterns are Wup.pattern and Wdn.pattern
  -- transport both sides using repClosureRP_eq_of_same_pattern
```

Better still, split the geometric bridge from `BoxMoveStep`:

```lean
lemma split_boxMove_rankPattern_closure
    [Infinite k]
    (a e : Fin (N+1)) (b : Fin N) (rest : List (Fin(N+1) × Fin(N+1)))
    (hae : a ≤ b.castSucc) (hbe : b.succ ≤ e) :
    repClosure (orbitSet
      ((foldDim_splitCons_eq ..) ▸
        intervalDirectSum ((a,b.castSucc)::(b.succ,e)::rest)))
      ⊆
    repClosure (orbitSet
      (dirSum (intervalModule a e) (intervalDirectSum rest))) := ...
```

and similarly for nonsplit. The left-associated upstairs base is absorbed by:

```lean
lemma repClosure_leftAssoc_eq_intervalDirectSum_of_rankPattern_eq
    {T U : Tuple (k:=k) d}
    (h : ∀ i j hij, rankPattern d T i j hij = rankPattern d U i j hij) :
    repClosure (orbitSet T) = repClosure (orbitSet U) :=
  repClosure_orbitSet_eq_of_rankPattern_eq h
```

This needs one unlisted lemma: rank pattern of `dirSum` / `intervalDirectSum` is additive and permutation-invariant, or at least enough specialized rank-pattern computations for the two geometric bases.

**3. (a,c,b,e) Extraction**

Use `ℤ → Fin` conversion. Do not try to make the whole per-step bridge pure rank-pattern only. The geometric lemmas are indexed by `Fin`, so a pure-rank-pattern bridge just postpones the same conversion to a less local place.

Needed sub-lemmas:

```lean
def intToFinN1 (x : ℤ) (hx0 : 0 ≤ x) (hxN : x ≤ N) : Fin (N+1) := ...

def intToFinN (b : ℤ) (hb0 : 0 ≤ b) (hbN : b < N) : Fin N := ...
```

Compatibility lemmas:

```lean
lemma intToFinN_castSucc_val
    ... :
    ((intToFinN b hb0 hbN).castSucc : Fin (N+1)).val = b.toNat := ...

lemma intToFinN_succ_val
    ... :
    ((intToFinN b hb0 hbN).succ : Fin (N+1)).val = (b+1).toNat := ...
```

Order transport:

```lean
lemma intToFinN1_le_iff_of_bounds ... :
    intToFinN1 x hx0 hxN ≤ intToFinN1 y hy0 hyN ↔ x ≤ y := ...
```

This is still grind, but it is localized. You also need the bounds `0 ≤ a`, `e ≤ N`, and `b < N`. If those are not in `BoxMoveStep`, make a strengthened descent-step lemma or carry a separate invariant from the chain construction. Without bounds, `BoxMoveStep` alone is too weak for invoking the geometric lemmas.

**4. Risk Ranking + Conditional Skeleton**

Risk ranking:

1. **(iii) left-associated `dirSum` vs `intervalDirectSum`** is the genuine blocker unless absorbed by rank-pattern invariance. With `repClosureRP`, it dissolves architecturally.
2. **(ii) decomposing canonical partition lists** is also dangerous. Avoid it entirely: invoke geometric lemmas with their own ad hoc list shape, then transport by rank pattern.
3. **(iv) list permutation invariance** dissolves if you never compare lists directly. You only need rank-pattern equality for the chosen witnesses.
4. **(i) `ℤ → Fin` extraction** remains real grind, but it is bounded arithmetic, not architectural risk.

Minimal honest conditional skeleton:

```lean
axiom boxMoveStep_repClosureRP_subset
    [Infinite k]
    {d : Fin (N+1) → ℕ}
    {Wup Wdn : RankPatternWitness (k:=k) d}
    (hstep : BoxMoveStep Wup.pattern Wdn.pattern) :
    repClosureRP Wdn ⊆ repClosureRP Wup
```

Then bank pieces 1, 3, 4, 5 around this.

Chain composition:

```lean
lemma boxMoveChain_repClosureRP_subset
    [Infinite k]
    {W₀ W₁ : RankPatternWitness (k:=k) d}
    (hchain : BoxMoveChain W₀.pattern W₁.pattern) :
    repClosureRP W₁ ⊆ repClosureRP W₀ := by
  induction hchain
  · exact subset_rfl
  · exact Set.Subset.trans
      (boxMoveStep_repClosureRP_subset ‹_›)
      ‹_›
```

Final conditional hard inclusion should depend only on:

```lean
hypothesis per_step :
  ∀ {d} {Wup Wdn : RankPatternWitness (k:=k) d},
    BoxMoveStep Wup.pattern Wdn.pattern →
    repClosureRP Wdn ⊆ repClosureRP Wup
```

That is the clean residual: one geometric degeneration obligation per box move, with all normal-form, permutation, and association choices hidden behind rank-pattern invariance.