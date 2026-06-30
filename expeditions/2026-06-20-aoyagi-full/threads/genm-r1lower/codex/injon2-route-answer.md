# Codex xhigh verdict (final answer; reasoning trace trimmed)

codex
**Recommendation:** use Route A, but in the packed form already built for the determinant work. Do not peel raw `chainA` indices by hand.

`BparamsLeaf` is **not affine** after fixing radial `u = 1`. The layer-0 core is still

```lean
schurFrameMap (K,N,X,E) = (K, K*N, X*K, X*K*N + E)
```

and `kLDU` does **not** make `K = I`; it makes `K = (1+L)·diag(q)·(1+U)`. So the right proof is value-level triangular readback, not derivative/global-inverse.

Key route:

1. Add a Schur readback lemma:

```lean
theorem schurFrameMap_inj_of_det_ne_zero
    {t r c : ℕ} {z z' : SchurInc t r c}
    (hK : z.1.det ≠ 0)
    (h : schurFrameMap z = schurFrameMap z') :
    z = z'
```

Algebra:
- top-left gives `K = K'`;
- top-right gives `K*N = K*N'`, cancel left by invertible `K`;
- bottom-left gives `X*K = X'*K`, cancel right by invertible `K`;
- bottom-right then gives `E = E'`.

This is the only place where invertibility is load-bearing.

2. Prove the K determinant fact on the target domain:

```lean
lemma slotReadV0_K_det_ne_zero_of_mem
    {y : Fin (routeMAmbient M) → ℝ}
    (hy : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeM M ha) (leafPivot M ha _ h0r h0c) ''
        interiorLiveInjDom ha h0r h0c)) :
    (slotReadV0 ha y).1.det ≠ 0
```

Use `hy = ⟨x, ⟨x₀, hx₀, rfl⟩, rfl⟩`, duplicate/extract the existing `hpbo_ne` argument from `interiorLive_kLDU_injOn`, then use `readK_kLDU_det` and `Finset.prod_ne_zero_iff`.

Important correction: do **not** try to prove all coordinates of `y` are nonzero after `kLDU`. That can fail by cancellation inside `(1+L)·diag(q)·(1+U)`. What holds, and what you need, is only `det (readK y 0) ≠ 0`.

3. From `h : BparamsLeaf ha y = BparamsLeaf ha y'`, recover V0:

Use `reindexL0_BparamsLeaf0` to get equality of `layer0SchurMap`, then unfold its definition as

```lean
flatBlock hr hc (schurFrameMap (slotReadV0 ha y))
```

and apply `flatBlockLE.injective`, then `schurFrameMap_inj_of_det_ne_zero`. This gives

```lean
slotReadV0 ha y = slotReadV0 ha y'
```

so `K,N,X,E` are recovered.

4. Recover V1:

Use

```lean
rsL1_BparamsLeaf1 :
  rsL1 ha (BparamsLeaf ha z 1)
    = (Lfun ha z - Nfun ha z * Wfun ha z, Wfun ha z)
```

Equality gives `Wfun y = Wfun y'` from the second component. Since `Nfun` is already recovered from `slotReadV0`, the first component gives `Lfun y = Lfun y'` by adding back `N*W`.

5. Finish with `eIn` rather than a fresh coordinate split:

Use existing

```lean
eIn_projV0
dWdC_eq_eInV1
```

to prove `(eIn ha y) = (eIn ha y')`; then apply `(eIn ha).injective`. If needed, add tiny bridge lemmas saying `Nfun` is the `.2.1` component of `slotReadV0`, and `Wfun/Lfun` are the two readers in `dWdC_eq_eInV1`.

So: Route A is right, but the clean proof is “packed Route A” via `flatBlockLE`, `rsL1`, and `eIn`. The rate-identity/direct `interiorLivePhi` shortcut will not avoid this algebra; it only gives scalar rate information, while injectivity needs the full parameter readback.
tokens used
565,443
**Recommendation:** use Route A, but in the packed form already built for the determinant work. Do not peel raw `chainA` indices by hand.

`BparamsLeaf` is **not affine** after fixing radial `u = 1`. The layer-0 core is still

```lean
schurFrameMap (K,N,X,E) = (K, K*N, X*K, X*K*N + E)
```

and `kLDU` does **not** make `K = I`; it makes `K = (1+L)·diag(q)·(1+U)`. So the right proof is value-level triangular readback, not derivative/global-inverse.

Key route:

1. Add a Schur readback lemma:

```lean
theorem schurFrameMap_inj_of_det_ne_zero
    {t r c : ℕ} {z z' : SchurInc t r c}
    (hK : z.1.det ≠ 0)
    (h : schurFrameMap z = schurFrameMap z') :
    z = z'
```

Algebra:
- top-left gives `K = K'`;
- top-right gives `K*N = K*N'`, cancel left by invertible `K`;
- bottom-left gives `X*K = X'*K`, cancel right by invertible `K`;
- bottom-right then gives `E = E'`.

This is the only place where invertibility is load-bearing.

2. Prove the K determinant fact on the target domain:

```lean
lemma slotReadV0_K_det_ne_zero_of_mem
    {y : Fin (routeMAmbient M) → ℝ}
    (hy : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeM M ha) (leafPivot M ha _ h0r h0c) ''
        interiorLiveInjDom ha h0r h0c)) :
    (slotReadV0 ha y).1.det ≠ 0
```

Use `hy = ⟨x, ⟨x₀, hx₀, rfl⟩, rfl⟩`, duplicate/extract the existing `hpbo_ne` argument from `interiorLive_kLDU_injOn`, then use `readK_kLDU_det` and `Finset.prod_ne_zero_iff`.

Important correction: do **not** try to prove all coordinates of `y` are nonzero after `kLDU`. That can fail by cancellation inside `(1+L)·diag(q)·(1+U)`. What holds, and what you need, is only `det (readK y 0) ≠ 0`.

3. From `h : BparamsLeaf ha y = BparamsLeaf ha y'`, recover V0:

Use `reindexL0_BparamsLeaf0` to get equality of `layer0SchurMap`, then unfold its definition as

```lean
flatBlock hr hc (schurFrameMap (slotReadV0 ha y))
```

and apply `flatBlockLE.injective`, then `schurFrameMap_inj_of_det_ne_zero`. This gives

```lean
slotReadV0 ha y = slotReadV0 ha y'
```

so `K,N,X,E` are recovered.

4. Recover V1:

Use

```lean
rsL1_BparamsLeaf1 :
  rsL1 ha (BparamsLeaf ha z 1)
    = (Lfun ha z - Nfun ha z * Wfun ha z, Wfun ha z)
```

Equality gives `Wfun y = Wfun y'` from the second component. Since `Nfun` is already recovered from `slotReadV0`, the first component gives `Lfun y = Lfun y'` by adding back `N*W`.

5. Finish with `eIn` rather than a fresh coordinate split:

Use existing

```lean
eIn_projV0
dWdC_eq_eInV1
```

to prove `(eIn ha y) = (eIn ha y')`; then apply `(eIn ha).injective`. If needed, add tiny bridge lemmas saying `Nfun` is the `.2.1` component of `slotReadV0`, and `Wfun/Lfun` are the two readers in `dWdC_eq_eInV1`.

So: Route A is right, but the clean proof is “packed Route A” via `flatBlockLE`, `rsL1`, and `eIn`. The rate-identity/direct `interiorLivePhi` shortcut will not avoid this algebra; it only gives scalar rate information, while injectivity needs the full parameter readback.
