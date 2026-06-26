**Verdict**

Yes, your read is right. `chainA` and the Schur frame are different objects, and Phase B2 is not a quick “apply Phase A + telescope” build.

More precisely: `chainA` is the unit-triangular chaining map

```lean
A_s = [C_{s+1} - N_s W_s ; W_s]
```

while Phase A’s Schur frame constructs a compressed transition block

```lean
S(X,K,N,E) = [[K, K*N], [X*K, X*K*N + E]]
```

and gives the determinant contribution `|det K|^(r+c)`. The current `chartParamsGen` really outputs the `chainA` layers; see [RouteMGenChain.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChain.lean:93) and [RouteMGenChartId.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-ab65ad6d0ec4aad88/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChartId.lean:35). So `schurFrame_abs_det` does not attach directly to `D(chartParamsGen ∘ Bflat)`.

**On The Det-1 Shortcut**

There is a det-1 chaining fact, but it does **not** avoid the reconciliation. It only tells you that once the chart has been expressed in a square full-ambient coordinate system with independent `C_{s+1}` and `W_s` slots, the map

```lean
(C, W) ↦ (C - N*W, W)
```

contributes determinant `1`. It does not by itself compute the determinant of the existing `chainA`-based chart, because in the actual chart `C_{s+1}` is not an independent layer coordinate; it is produced by deeper Schur/LDU/radial factors.

The correct factorization is:

```text
Dφ =
  DQ
  · ∏ D(chain_s)          -- det 1
  · ∏ D(Schur_s)          -- |det K_s|^(r_s+c_s)
  · ∏ D(LDU_s)            -- ∏ |q_{s,i}|^(2(t_s-1-i))
  · D(radial)             -- |u_p|^(D-1)
```

with every factor evaluated at the appropriate prefix. The prefix issue is real: this is the same phenomenon as `Frame3333Deriv (Kparam3333 u)` in the concrete proof.

So yes: the total determinant should be “Schur · LDU · radial,” and chaining should be determinant `1`. But Lean still needs the full-ambient factorization and the proof that the packed factor-product chart equals the `chartParamsGen`/`chainA` chart used for the rate identity.

**Lean Shape I Would Use**

Do not try to compute the determinant directly from `chainOfMt`. That route reifies `GenBlk` into coordinates, differentiates `chainA`, manages dependencies, and proves triangularity anyway, but in a less transparent form.

Use a factor certificate/prefix fold:

```lean
structure ChartFactor (N : ℕ) where
  f      : (Fin N → ℝ) → (Fin N → ℝ)
  D      : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)
  hasD   : ∀ u, HasFDerivAt f (D u) u
  absDet : ∀ u, |LinearMap.det (D u).toLinearMap| = ...
```

Needed lemmas:

```lean
schurFrame_abs_det        -- already Phase A
lduCore_abs_det           -- still needed
chainUnit_abs_det         -- det 1 for (C,W) ↦ (C-NW,W), full-ambient
pivotBlowupOnDeriv_det    -- banked radial
outerReshape_abs_det      -- det 1 for pack + paramsEquivFlat
factorFold_abs_det        -- prefix-aware composition determinant
detK_prefix_pullback      -- det K_s(prefix_s u) = monomial in source q’s
leafH_prod_eq             -- final ∏ |u_j|^leafH j rewrite
```

For the opaque-width reconciliation, the useful local lemmas are generic versions of your concrete probe:

```lean
chainA_apply_castAdd :
  chainA h N W C (Fin.castAdd c i) j = (C - N*W) i j

chainA_apply_natAdd :
  chainA h N W C (Fin.natAdd t a) j = W a j
```

and analogous `chainQ` row lemmas. These make the `chainA` bookkeeping mechanical, but they do not eliminate the need for the global chart equality.

**Cost Read**

If “B2” means only “once the factor list and prefix determinant facts exist, telescope the determinants,” then bounded.

If “B2” means the actual goal

```lean
phiFlat_abs_det :
  |det D(paramsEquivFlat ∘ chartParamsFlat)| =
    ∏ j, |u j| ^ leafH j
```

starting from the current `chainA` chart, then no: not a few scoped lemmas. It is a genuine multi-pass design/build over opaque widths: full-ambient factors, prefix bookkeeping, `chainA`/Schur reconciliation, LDU pullback, and final `leafH` accounting.

I would re-scope: first bank `chainA_apply_castAdd/natAdd` + `chainUnit_abs_det`; then A3 `lduCore_abs_det`; then build the prefix factor scaffold. Only after those are green should `phiFlat_abs_det` be treated as a bounded final theorem.