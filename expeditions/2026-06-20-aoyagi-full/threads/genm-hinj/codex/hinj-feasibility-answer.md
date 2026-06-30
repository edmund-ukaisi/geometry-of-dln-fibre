**Verdict: FALSE/obstructed as stated.**

The off-diagonal LDU coordinates are not the problem. Once the LDU diagonal pivots `q_i` are nonzero, the LDU matrix
`(1+L) diag(q) (1+U)` determines `q`, then `L,U`; no extra nonvanishing of off-diagonal `l,u` is mathematically needed. Likewise `X,N` are recoverable from the Schur blocks once `K` is invertible, and `E` is recoverable only after the radial scalar is known and nonzero.

The obstruction is the **radial scalar**. Your stated map uses `genBlkFlatStruct`, whose interior residual block is read as a free `E` block and enters as

```lean
X * K * N + (x (structPivot M hN)) • E
```

There is no generic fixed `1` residual pivot in that map. The `(3,3,3,3)` proof recovers `u0` from the explicit `+ x 0` term in `chartA3333` at the bottom-right entry, then divides by `u0` later. That fixed additive radial anchor is not present in `genBlkFlatStruct`; it is the kind of thing the later `LiveR1`/fixed-`pivotEIndicator` construction introduces.

So the `3333` recovery step that fails to generalize is precisely:

```lean
h0 : u 0 = v 0
```

from `A(2,2)`, using the concrete `+ x 0` entry. In the opaque-width `genBlkFlatStruct` version, the corresponding block gives only `known + u * E`, not `known + u`.

There is also a formal slot wall: `structPivot M hN = ⟨0,_⟩` is not proved to be outside the reader slots, and `chartIdxEquiv` is built through `Fintype.equivFin`. The repo already records this issue elsewhere: one cannot generally pin whether `structPivot` coincides with a chosen reader slot, so complement-slot constructions were used.

A corrected theorem is plausibly true but **very heavy**, not a 200-line lemma. It would need at least:

- a fixed radial anchor, e.g. `genBlkFlatLiveR1`/`pivotEIndicator`, or an explicit hypothesis proving the radial coordinate is independently recoverable;
- a generic layer readback theorem for `chartParamsGen`;
- Schur block inverse lemmas recovering `K, X, N, E, W`;
- `kLens`/`lduCoreMap` injectivity on nonzero diagonal pivots;
- role-reader extensionality through `chartIdxEquiv`.

So: **do not try to prove this exact theorem**. First change the map/hypotheses so the radial scalar has a fixed recoverable occurrence.