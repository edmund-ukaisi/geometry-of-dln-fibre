**Q1**

The `minAdm - 1` power does **not** come from “`u` times every `E` entry, including the pivot”. That would be the wrong chart.

The intended chart is:

```text
active normal coordinates = (u, z₁, ..., z_{m-1}),  m = minAdm
radial blow-up part       = (u, u z₁, ..., u z_{m-1})
Jacobian determinant      = u^(m-1)
```

So the pivot `u = x p` is a **distinct active slot** from the non-pivot residual slots scaled by `u`. In block language, the residual direction has one fixed entry `1`; `u` multiplies that fixed entry to produce the pivot output `u`, while it multiplies the other residual coordinates to produce `u zᵢ`.

Thus Hypothesis B is the right model, with one correction: the scaled non-pivot slots are not only `readE`; they include the nonfixed residual/leaf slots. For `(2,2,2)`, `minAdm = 3`, so the active normal block has three coordinates: one radial pivot plus two non-pivot coordinates. Net radial determinant is `|u|^2`.

Current Lean caveat: the implementation does **not yet encode this fixed residual slot correctly**. `readE` reads ordinary `E` variables, `structPivot` is hardcoded as flat coordinate `0`, `chartIdxEquiv` is opaque via `Fintype.equivFin`, and `genBlkFlatStruct` currently has `Rfin := fun _ => 0`. See [RouteMGenFlatStruct.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a008af4c8473e3063/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean:104>) and [RouteMFlatStructV.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a008af4c8473e3063/lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatStructV.lean:88>). As written, the full determinant target is not derivable; the decoder needs `pRad/fixedSlot` and nonzero leaf `Rfin` first.

**Q2**

Minimal determinant factorization, outer-to-inner list for `foldr`:

```text
[ final linear pack/reindex,
  chain factors,
  Schur-frame factors,
  LDU-core factors,
  radial blow-up factor ]
```

`foldr` applies the rightmost factor first, so radial is deepest.

Per-factor determinants:

```text
radial      : |u_p|^(active.card - 1) = |u_p|^(minAdm - 1)
LDU_s       : ∏ᵢ |q_{s,i}|^(2 * (t_s - 1 - i))
Schur_s     : |det K_s|^(r_s + c_s)
chain_s     : 1
linear pack : 1 in absolute value
```

For `(2,2,2)`: boundary `s = 1` has `K,X,N,E` all `1×1`, `r = c = 1`.

```text
radial      : |u|^2        since minAdm = 3
LDU         : 1            because K is 1×1
Schur       : |K|^2
chain       : 1
pack        : 1
total       : |u|^2 * |K|^2
```

So yes: the binding entry has `leafH p = 2 = minAdm - 1`. The `|K|^2` is a spectator Jacobian monomial.

**Q3**

For `(2,2,2)`, layer `s = 0` is the easy kept-row case: `Text 1 = Wext 0 = 2`, so the residual row block has size `0`. The proof shape is:

```lean
ext s i j
fin_cases s
· -- s = 0
  unfold chartParamsGen Agen
  rw [dif_pos (by decide)]
  -- expose the row as the kept block of chainA
  set hsplit := genWidthEq M222 t222 (hleStruct M222 t222 structAdm222) 0 (by decide)
  let i' : Fin (Text M222 t222 1) := Fin.cast (by decide) i
  have hrow :
      ((finCongr (show Wext M222 0 = M222 0 by decide)).symm i)
        = Fin.cast hsplit
            (Fin.castAdd (Wext M222 0 - Text M222 t222 1) i') := by
    apply Fin.ext
    simp [M222, t222, Wext, Text]
  rw [hrow, chainA_apply_castAdd]
  simp [Matrix.mul_apply]
```

The single hardest cast is `hrow`: aligning the row index produced by `chartParamsGen`’s `reindex` with the `Fin.cast h (Fin.castAdd c i)` row expected by `chainA_apply_castAdd` in [RouteMGenChainBridge.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a008af4c8473e3063/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChainBridge.lean:39>).

For the nontrivial bottom-row layer, the analogous hard cast is the `natAdd` version needed for `chainA_apply_natAdd`.