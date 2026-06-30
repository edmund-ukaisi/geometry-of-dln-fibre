# Decorrelated adjudication: does an opaque-width InjOn proof generalize from a fin_cases anchor?

I am formalising in Lean 4 + Mathlib. I must deliver, OR flag as a wall with a precise obstruction:

```
theorem interiorLDU_injOn (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hN : 0 < routeMAmbient M) :
    Set.InjOn (interiorLDUphi M ha hN)
      {u : Fin (routeMAmbient M) → ℝ | u (structPivot M hN) ≠ 0
        ∧ ∀ j ∈ (Finset.univ.filter (fun a => 0 < interiorLDU_leafH M ha hN a)).erase (structPivot M hN), u j ≠ 0}
```

## The map (opaque per-layer widths)
`interiorLDUphi M ha hN x = paramsEquivFlat M (chartParamsGen (x p) M (tach M) (genBlkFlatStruct M (tach M) ha (kLDU M (tach M) ha x)) hle)`
where:
- `paramsEquivFlat M` is a measurable EQUIV (bijection) Params M ≃ (Fin N → ℝ). So InjOn of interiorLDUphi ⟺ InjOn of `x ↦ chartParamsGen (x p) ... (genBlkFlatStruct ... (kLDU x))`.
- `chartParamsGen u ... B` builds layer matrices `A_k` (k : Fin (L+1)) from a FactoredChain: `C_k = Bmat_k · chainQ(N_k) + u • Rmat_k`, then `A_k = chainA(...)`-style (unit-triangular chaining). The chart's "output" is the tuple of layer matrices `(A_0,...,A_L)`.
- `genBlkFlatStruct` reads DISJOINT free flat coords per boundary k: blocks K (Text(k+2)×Text(k+2)), X, N, E, W, and assembles: `Bmat(k+1) = bmatStack(K,X) = [K ; X·K]` (vertical stack), `Rmat(k+1) = rmatPad(E) = fromBlocks 0 0 0 E`, `Nblk(k+1)=N`, `Wblk(k+1)=W`. Identity boundary k=0: Bmat 0 = I, Rmat 0 = 0.
- `kLDU x` replaces each K-block `readK x k` by `kLens(readK x k) = matrixSplit.symm(lduCoreMap(matrixSplit K)) = (1+L_strict)·diag(q)·(1+U_strict)` where (l,q,u)=matrixSplit K (strict-lower/diag/strict-upper). So the chart's K-block is the LDU matrix; its det is the monomial ∏ q_i.
- The weighted axes E (the set in the InjOn domain) = the coordinates j with leafH_j > 0, i.e. the radial pivot (minAdm-1) + the LDU diagonal-pivot slots q_{s,i} (exponent (r+c)+2(t-1-i)) per boundary. The OFF-diagonal LDU params l,u and the X/N/E/W slots have leafH = 0 (NOT in E).

## The only existing templates (all fin_cases enumeration over a FIXED Fin N)
`chartParams3333_injOn` (Fin 27): recovers all 27 coords off {u0,u1,u4,u9≠0} by reading concrete matrix entries chartA/B/C i j with fin_cases + congrFun + hand-named h0..h26, divisions by u1/u9/u0, and two 2×2 "A-frame" systems of det u1·u4. `chartParams4422_injOn` (Fin 28) off {u0≠0}: similar. NO general-width `chartParamsGen_injOn` exists.

## My structural reading of the recovery (off E)
1. Top block of bmatStack gives K = kLens(readK x) directly (a layer-matrix sub-block).
2. `X·K` block ÷ K⁻¹ gives X — needs K invertible ⟺ LDU diag pivots q ≠ 0 (these ARE in E).
3. From K = (1+L)diag(q)(1+U), recover q (diagonal), then l, u (off-diagonal) by the LDU factorization being unique given q ≠ 0.
4. N via chainQ(N_k) inversion; E via Rmat (the u•Rmat additive term); radial u = x p from somewhere.

## Questions (be skeptical, decorrelated)
1. Is the InjOn statement even TRUE? Specifically: are the off-diagonal LDU params (l,u — leafH=0, NOT excluded) and X/N/E/W (leafH=0, NOT excluded) actually recoverable when only q≠0 and u_p≠0 are assumed? Or is there a degeneracy where two different x map to the same chart output (e.g. if some q_i appears but the recovery of l/u needs MORE than q≠0)?
2. Is recovering the radial scalar `u = x p` from the chart output sound off E? At (3,3,3,3) it was the LAST recovered coord via a specific entry — does an opaque-width analogue exist?
3. Realistic Lean effort to prove this over OPAQUE L and opaque per-layer widths WITHOUT fin_cases: is this a ~200-line generic-lemma development, a multi-hundred-line one needing new bmatStack/kLens/chainQ inversion lemmas, or is there a structural obstruction making it not provable in the available frame?
4. If you see a SPECIFIC step that fails to generalize from the anchor, name it precisely (which coordinate / which block / which nonvanishing assumption is missing).

Give a crisp verdict: TRUE-and-feasible (with effort estimate + lemma list), TRUE-but-very-heavy (what's the heaviest sub-lemma), or FALSE/obstructed (the precise counterexample or missing hypothesis).
