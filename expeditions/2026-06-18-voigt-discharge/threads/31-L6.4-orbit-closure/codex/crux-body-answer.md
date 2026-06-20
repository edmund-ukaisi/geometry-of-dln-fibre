1. **Step C is correct.** Reduce `Tp,Tq` to `patternRealizer` first. It does not create extra dimension casts; it only rewrites closures inside the fixed ambient `d`.

```lean
have hTpR :
  repClosure (orbitSet Tp)
    = repClosure (orbitSet (patternRealizer hrsupp hrnn hrdiag)) := by
  apply repClosure_orbitSet_eq_of_rankPattern_eq
  intro i j hij
  apply Nat.cast_injective
  calc
    ((rankPattern d Tp i j hij : ℕ) : ℤ) = r i j := hp i j hij
    _ = ((rankPattern d (patternRealizer hrsupp hrnn hrdiag) i j hij : ℕ) : ℤ) :=
      (rankPattern_patternRealizer hrsupp hrnn hrdiag i j hij).symm
```

Do the same for `Tq` and `r''`, then `rw [hTqR, hTpR]`. Bridging the geometric witnesses directly to `Tp,Tq` saves no casts and mixes `hp/hq` into the hard geometric body.

2. Use **(i)**. Prove rank computations over `dgS`/`dgN`, prove `hgd : dgN = d`, then transport once. You cannot stay at `dgN` because the final closure lives in `RepCoord d → k`.

Nonsplit diagonal chain:

```lean
have hgdZ : ∀ t : Fin (N+1), (dgN t : ℤ) = (d t : ℤ) := by
  intro t
  calc
    (dgN t : ℤ)
        = (intervalDim aF eF t : ℤ)
          + (intervalDim cF bF.castSucc t : ℤ)
          + (foldDim rest t : ℤ) := by
            simp [dgN, Nat.cast_add, add_assoc]
    _ = cumul N (singleDelta aF eF) (t:ℤ) (t:ℤ)
        + cumul N (singleDelta cF bF.castSucc) (t:ℤ) (t:ℤ)
        + cumul N mRest.1 (t:ℤ) (t:ℤ) := by
          rw [intervalDim_eq_cumul_singleDelta_diag,
              intervalDim_eq_cumul_singleDelta_diag,
              foldDim_eq_cumul_multiplicityArray_diag,
              hmultRest]
    _ = cumul N
          (fun x y =>
            singleDelta aF eF x y
            + singleDelta cF bF.castSucc x y
            + mRest.1 x y)
          (t:ℤ) (t:ℤ) := by
          rw [← cumul_add, ← cumul_add]
          simp [add_assoc]
    _ = cumul N (diffTri r hrsupp).1 (t:ℤ) (t:ℤ) := by
          rw [hUpArr]
    _ = r (t:ℤ) (t:ℤ) := cumul_diffTri_eq hrsupp le_rfl
    _ = (d t : ℤ) := (hrdiag t).symm

have hgd : dgN = d := by
  funext t
  exact_mod_cast hgdZ t
```

Needed but not listed: `intervalDim_eq_cumul_singleDelta_diag`, `foldDim_eq_cumul_multiplicityArray_diag`, and preferably `multiplicityArray_listOfArray_of_isKostant`.

3. Define residuals as truncated arrays. Nonsplit:

```lean
let m := diffTri r hrsupp

def mRest : SuppArray (N:ℤ) ℤ :=
  ⟨fun x y =>
      if x ≤ y then
        m.1 x y
          - singleDelta aF eF x y
          - singleDelta cF bF.castSucc x y
      else 0,
    by
      -- support: use m.2 plus Fin bounds to kill deltas outside [0,N]
      ...⟩
```

Split:

```lean
def mRest : SuppArray (N:ℤ) ℤ :=
  ⟨fun x y =>
      if x ≤ y then m.1 x y - singleDelta aF eF x y else 0,
    ...⟩
```

Proof obligations:

```lean
have hRestK : IsKostantArray mRest := ...
have hmultRest : multiplicityArray (listOfArray mRest) = mRest.1 := ...
```

For `hRestK`, split on the delta cells. Use `hae : 1 ≤ diff r a e` at `(a,e)`, and in nonsplit use `hcbm hcb : 1 ≤ diff r c b` at `(c,b)`. Else use `hrnn x y hxy`.

Main cumul identities:

```lean
have hUpArr :
  (fun x y =>
    singleDelta aF eF x y
    + singleDelta cF bF.castSucc x y
    + mRest.1 x y)
  = (diffTri r hrsupp).1 := by
  funext x y
  by_cases hxy : x ≤ y
  · simp [mRest, hxy]; ring
  · -- deltas vanish because their endpoints are upper-triangular
    simp [mRest, hxy, singleDelta_eq_zero_of_lt]
```

Downstairs nonsplit:

```lean
have hDnArr :
  (fun x y =>
    singleDelta aF bF.castSucc x y
    + singleDelta cF eF x y
    + mRest.1 x y)
  = (diffTri r'' hr''supp).1 := by
  -- upper triangle: use hr'' = boxDrop ... and boxIndicator_diff
  -- below triangle: both sides are 0
  ...
```

In split, replace the two nonsplit terms by
`singleDelta aF bF.castSucc + singleDelta bF.succ eF`.

4. Do **two branches**. The geometric lemmas have different tuple shapes and different dimension vectors, so a unifying abstraction will cost more than it saves.

Do **split first**: one residual subtraction, one upstream interval, and the `dgS = d` proof validates the transport pattern with less algebra. The only split-specific nuisance is deriving `c = b + 1` from `¬ c ≤ b` and `c ≤ b + 1`.

5. Biggest landmine: transporting geometric membership, not the rank-pattern transport. Add this tiny helper before the crux:

```lean
lemma mem_repClosure_orbitSet_transport
    {d₀ d : Fin (N+1) → ℕ} (h : d₀ = d)
    {D U : Tuple (k := k) d₀}
    (hm : canonicalCoord d₀ D ∈ repClosure (orbitSet U)) :
    canonicalCoord d (h ▸ D) ∈ repClosure (orbitSet (h ▸ U)) := by
  subst h
  simpa using hm
```

With helpers factored, expect roughly **120-170 lines for split** and **180-260 for nonsplit**. Without the helper lemmas above, each branch can easily double.