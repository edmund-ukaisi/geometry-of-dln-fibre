**Ranking**

1. **Best: symbolic reader slots + custom additive `Bparams` + per-layer chart equality.**  
   Do not compute any `Fin 8` slot. Define the leaf slots and reader slots through the same `chartIdxEquiv.symm` tags, prove reader/leaf disjointness by `chartIdxEquiv.symm.injective`, and define
   ```lean
   B y := paramsEquivFlat M222 (Bparams y)
   ```
   where `Bparams` reads the pivot as `y (structPivot M222 hN)` and leaves `a,b,n,w₀,w₁` as ordinary reader values.

2. **Same proof, but package `B` as a new additive decoder.**  
   This is cleaner semantically if you want `chartParamsGen 1 ...`, but it must be a new decoder whose pivot `E(0,0)` reads `y_p`, not `genBlkFlatLiveR1`. More code than direct `Bparams`.

3. **Transport through the banked free-pivot `phi222` template by building an opaque-reader coordinate permutation.**  
   Useful for `hasDB`/`hdet`, but expensive for `hmap`: you still need to align opaque reader tags with the semantic coordinates.

4. **Try to compute or replace `chartIdxEquiv`.**  
   Not recommended. `Fintype.equivFin` is choice-based, and proving it equals your preferred enumeration is the wrong fight.

5. **Use `B = phiGen 1 (genBlkFlatLiveR1 ...)` or prove the GenBlk `hslot`.**  
   Dead. The repo already machine-checks the obstruction: the fixed pivot block forces `u = 1` in the false GenBlk equality. See [RouteMSlotId.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a6fc410663da5b26b/lean/DLNFibre/DLN/RLCT/Validate/RouteMSlotId.lean:124).

**Answer To 1**

Yes, you can avoid concrete reader-slot numbers for the reader/leaf disjointness. The idiom is:

```lean
abbrev χ := chartIdxEquiv M222 (tDesc M222 tach222) ha.h0 ha.hc ha.hL
def slot (c : ChartIdx M222 (tDesc M222 tach222)) : Fin (routeMAmbient M222) := χ.symm c
```

Then prove slot inequalities by:
```lean
intro h
have htag := χ.symm.injective h
-- now close by Sigma/Sum tag contradiction, usually `simpa` or cases
```

But one caveat matters: injectivity alone does **not** tell you that a semantic leaf slot is different from `structPivot = 0`, because `structPivot` is not itself given as a `ChartIdx` tag. So either:

- prove separate lemmas `leafSlot0 ≠ structPivot` and `leafSlot1 ≠ structPivot`, or
- choose `leafSlot0/1` from a finite complement with proofs that they avoid `structPivot` and the fixed reader slots.

That pivot-disjointness is the biggest risk.

**Top Proof Skeleton**

Define:
```lean
p := structPivot M222 hN
active := {p, lf0, lf1}
rfin x := !![x lf0, x lf1]
```

Core `pivotBlowupOn` lemmas:
```lean
pbo_pivot : pivotBlowupOn active p x p = x p
pbo_leaf0 : pivotBlowupOn active p x lf0 = x p * x lf0
pbo_leaf1 : pivotBlowupOn active p x lf1 = x p * x lf1
pbo_fixed :
  q ≠ lf0 → q ≠ lf1 → pivotBlowupOn active p x q = x q
```
The last lemma does not require `q ≠ p`; the pivot branch is fixed anyway. Use `by_cases q = p; simp [pivotBlowupOn, active, *]`.

Then define:
```lean
Bparams y :=
  Fin.cons
    (!![a y, a y * n y;
        a y * b y, a y * b y * n y + y p])
    (Fin.cons
      (!![y lf0 - n y * w0 y, y lf1 - n y * w1 y;
          w0 y, w1 y])
      (fun i => i.elim0))

B y := paramsEquivFlat M222 (Bparams y)
```

Prove opaque explicit layer lemmas for the LHS decoder:
```lean
Agen0_liveR1_opaque :
  Agen (x p) M222 tach222 (genBlkFlatLiveR1 ... (rfin x) x) hle 0
    = !![a x, a x * n x; a x * b x, a x * b x * n x + x p]

Agen1_liveR1_opaque :
  Agen (x p) M222 tach222 (genBlkFlatLiveR1 ... (rfin x) x) hle 1
    = !![x p * x lf0 - n x * w0 x,
         x p * x lf1 - n x * w1 x;
         w0 x, w1 x]
```

Use the same pattern as `Agen0_222_eq` / `Agen1_222_eq`: `rw [chainA_apply_castAdd]`, `rw [chainA_apply_natAdd]`, `rw [chainQ_apply_castAdd]`, `rw [chainQ_apply_natAdd]`, `genBlkFlatLiveR1_Rmat_pivot`, `rmatPad_natAdd_natAdd`, `pivotEIndicator_apply_zero`, then `fin_cases` and `ring`.

Finally:
```lean
theorem hmap :
  phiFlatLiveR1 M222 tach222 ha hN 1 hp1 hp2 rfin
    = B ∘ pivotBlowupOn active p := by
  funext x
  unfold phiFlatLiveR1 phiGen B
  congr 1
  funext s
  fin_cases s
  · rw [Agen0_liveR1_opaque]
    ext i j <;> fin_cases i <;> fin_cases j
    simp [Bparams, pbo_fixed, pbo_pivot]
    ring
  · rw [Agen1_liveR1_opaque]
    ext i j <;> fin_cases i <;> fin_cases j
    simp [Bparams, pbo_fixed, pbo_leaf0, pbo_leaf1]
    ring
```

**Answer To 2**

Yes, the clean proof is per-layer and treats `a,b,n,w₀,w₁` as opaque scalars. But do **not** use `chartParamsGen 1 (genBlkFlatLiveR1 ...)` as `B`; that is the superseded wrong `B`, because it reads the fixed pivot entry as `1`. Use either direct `Bparams`, or a new additive decoder whose pivot entry reads `y_p`.

**Answer To 3**

Confirmed. The additive `+ u` is consistent because `pivotBlowupOn active p x p = x p`. So the faithful `B` reads the pivot coordinate directly:
```lean
Bparams y A0(1,1) = a y * b y * n y + y p
```
and at `y = pivotBlowupOn active p x`, this becomes `a*b*n + x p`. The leaf coordinates are multiplicative because `y lfᵢ = x p * x lfᵢ`. This is the cleanest `B` for `hmap`.