# Codex consult: cleanest route to `interiorLive_BparamsLeaf_injOn` (injOn#2)

## The target (Lean 4 + Mathlib, L=2 fixed)

I must prove, sorry-free:

```
theorem interiorLive_BparamsLeaf_injOn (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    Set.InjOn (BparamsLeaf ha)
      (kLDU M (tach M) ha
        '' (pivotBlowupOn (activeM M ha) (leafPivot M ha _ h0r h0c) '' interiorLiveInjDom ha h0r h0c))
```

i.e. `BparamsLeaf ha` is injective on the domain `D := kLDU '' (pbo '' injDom)`. Here `M : Fin 3 → ℕ`,
`L = 2`. On `D`, every coordinate of the point is NONZERO (injDom forces all coords ≠ 0; pbo scales the
active block by the pivot coord ≠ 0; kLDU only touches the K-slots via an LDU lens that preserves
nonzeroness of the q-pivots).

## What `BparamsLeaf` is

`BparamsLeaf ha y : Params M := chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirect ha y) y) hle`.

`chartParamsGen u M t B hle : Params M`, value at layer `s : Fin (L+1)` is `reindex (chainOfMt u M t B hle).A s.val`
(a width-reindex of the chain's layer matrix `A s`). So `BparamsLeaf ha y` is the tuple `(A 0, A 1)` of the
two chain-layer matrices (reindexed to genuine widths `M`), built with radial `u = 1`.

The chain layer at boundary `k` (for `k < L`): `A k = chainA(h)(N_k)(W_k)(C(k+1))` where
`chainA(h)(N)(W)(C) = [ C − N·W ; W ]` (vertical block over `Fin t ⊕ Fin (M'−t)`, reindexed), and
`C(k+1) = Cgen` at boundary `k+1`:
  - interior (`k+1 < L`): `C(k+1) = Bmat(k+1)·chainQ(N_{k+1}) + u·Rmat(k+1)`
  - leaf (`k+1 = L`): `C(L) = u·Rfin L = u·rfin` (the leaf residual block; here `u = 1`).

The block data from `genBlkFlatStruct` (interior boundary `s = j+1`, `j < L`):
  - `Bmat(j+1) = bmatStack(readK_j, readX_j) = [ K_j ; X_j·K_j ]` (vertical stack, the Schur frame's left col)
  - `Rmat(j+1) = rmatPad(readE_j) = [[0,0],[0, E_j]]`
  - `Nblk(j+1) = readN_j`, `Wblk(j+1) = readW_j` (lift)
  - identity boundary `j = 0`: `Bmat 0 = I`, `Rmat 0 = 0`, `Nblk 0 = 0`, `Wblk 0 = 0`.
  - leaf `Rfin L = rfinDirect ha y` (reads leaf slots directly from y).

`readK_j / readX_j / readN_j / readE_j / readW_j` each read a DISJOINT flat slot of `y` via the banked
bijection `chartIdxEquiv` (every reader is `y ∘ (some injection into Fin (routeMAmbient M))`, the slots
pairwise disjoint and jointly with the leaf slots covering exactly the "active" coords + spectators).
So the map `y ↦ (K_0, X_0, N_0, E_0, W_0, leaf)` is a LINEAR coordinate-permutation-projection of `y`
(literally reads disjoint entries). The NONLINEARITY enters only in how these blocks combine into
`A 0, A 1` (products `X·K`, `Bmat·chainQ(N)`, `N·W`).

At L=2: boundaries are j=0 (identity, contributes A 0 with N_0=0, W_0 the lift) and j=1... wait — careful:
`A k` for `k=0,1`. `A 0 = chainA(N_0=0)(W_0)(C_1)`, so `A 0 = [C_1 ; W_0]` (since N_0·W_0 = 0).
`C_1 = Bmat(1)·chainQ(N_1) + Rmat(1) = [K_0;X_0 K_0]·[I|N_0?]...` — the interior boundary 1 uses the
j=0 reader block (readK ⟨0⟩ etc.). And `A 1 = chainA(N_1)(W_1)(C_2)` with `C_2 = leaf residual` (= rfinDirect),
N_1/W_1 the boundary-1 readers, but at L=2 boundary 1 = L−1 so W_1 reads the lift to the leaf.

## The two candidate routes

**Route A (full block readback).** From `(A 0, A 1)` peel the vertical blocks:
`A 0 = [C_1 ; W_0]` ⟹ recover `W_0` (lower block) and `C_1` (upper). `A 1 = [C_2 − N_1 W_1 ; W_1]` ⟹
recover `W_1` (lower) and `C_2 − N_1 W_1` (upper). Then from `C_1 = [K;XK]·chainQ(N) + rmatPad(E)` and the
disjoint-slot structure, recover `K, X, N, E` (the K-block is the leading square block of `Bmat·chainQ`,
etc.). Then leaf `C_2 = rfinDirect` recovers the leaf slots. Compose all readbacks ⟹ `y = y'`. This is a
long but mechanical block-matrix inversion; the nonlinear products (X·K, etc.) invert because K is
INVERTIBLE on `D` (K = the kLDU-lensed K-slot, which on `D` has nonzero pivots / is unit-triangular·diag·
unit-triangular — actually K here is the genuine K-block read; on `D`, is K invertible? K = identity·diag(q)·
unit after kLDU? need to confirm).

**Route B (derivative / global-injectivity shortcut).** `BparamsLeaf` is polynomial in `y`. If I can show
its total derivative `D(BparamsLeaf)` is INJECTIVE (constant-rank full) at every point of `D`, that gives
LOCAL injectivity only, not InjOn on a non-convex set. So Route B alone is insufficient unless `D` is convex
AND the map is a global diffeo — neither is clean here. (We already have `interiorLive_abs_det` showing the
Jacobian det is a nonzero monomial on `D`, but that's local.)

## Questions for you

1. Is Route A the right call, or is there a cleaner structural shortcut I'm missing? In particular: is
   `BparamsLeaf` AFFINE in `y` once the radial is fixed to 1 and we restrict to the live-leaf chart? (The
   products X·K, N·W suggest NO — but maybe on `D` after kLDU the K-block is the IDENTITY (kLDU lenses K to
   LDU coords, and the chart reads... )? If K ≡ I on the relevant domain, then X·K = X and the map linearizes.)

2. For Route A, what is the MINIMAL invertibility fact about the K-block I need, and does it hold on `D`
   (all-coords-nonzero, kLDU-lensed)? The kLDU lens sends K-slots to LDU-coordinatized form
   `(1+L)·diag(q)·(1+U)`. On `D`, q-pivots ≠ 0, so K is invertible. Is the invertibility of K the ONLY
   nonlinearity-breaker, after which X, N, E, W, leaf are linear reads?

3. Is there a slicker route: prove `interiorLivePhi` (the WHOLE chart = `(BchartLeaf ∘ kLDU) ∘ pbo`) is
   injective DIRECTLY (e.g. via the rate identity `routeMCore ∘ phi = u²·V` + the explicit unit, recovering
   the radial coord and the residual coords jointly), bypassing `BparamsLeaf` injectivity entirely? The
   consumer is `interiorLive_injOn`; if I can prove THAT a different way, I drop the `BparamsLeaf` factor.

Give a concrete recommendation (A / B / slicker) + the key lemma chain. Exact algebra; flag any place the
all-coords-nonzero / K-invertible-on-D assumption is load-bearing or might FAIL.
