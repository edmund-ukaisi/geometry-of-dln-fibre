**FACT**

(a) **Reachable: yes.** I found no chart constraint excluding the curve. The split is a translation plus role-respecting coordinate reindex, and `regGaugeSlotEquiv` is a homeomorphism from `(reg,spec)` onto all per-layer `X/Y/Z` reads; the `T_s` core reads are a separate free core slot. See [DeepestSplitConcrete.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitConcrete.lean:28), [DeepestSplitReindex.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:543), and [DeepestGaugeConstruction.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:110).

The frame facts do not impose equations among your reads. `hcorner` normalizes the fixed deepest basepoint/frame, not every nearby split point. The cutoff does not save the statement: your reads tend to `0`, so the curve is eventually inside the inner ball where the cutoff equals the honest Schur shift.

Exact algebra agrees with your computation:

```text
C0 = [[1, 0, t], [-t^2, t, -t^3]]
C1 = [[1, -t^2], [t, 0], [0, t]]

C0 C1 = [[1, 0], [0, 0]] = B
```

So `loss = 0`, `Sreg = 0`. Meanwhile

```text
S0 = T0 - Z0 Y0 = [t, 0]
S1 = T1 - Z1 Y1 = [t^3, t]^T
S0 S1 = t^4
coreΦ = t^8

K = Z1 Y0 = [[0, t^2], [0, 0]]
Rcore = S0 (I-K) S1 = 0
Score = 0
```

**INFERENCE**

(b) **Refutation of the squeeze as stated: yes.** For every neighborhood of the deepest point, the tail of this curve lies in it. Along that tail,

```text
loss = 0
Sreg_E + coreΦ = 0 + t^8 > 0
```

so no `c₁ > 0` can satisfy

```text
c₁ * (Sreg_E + coreΦ) ≤ loss.
```

The frame leaf `loss ≍ Sreg + Score` is not the failing part; here both sides are `0`. The false step is replacing the global Schur core `Score` by the per-layer product core `coreΦ`. Equivalently, the asserted germ charge `|Score - coreΦ| ≤ C*Sreg` fails because the left side is `t^8` and the right side is `0`.

(c) **Rescuable by using `Score`: yes, for the loss squeeze.** A corrected squeeze with the core term `frobSq(Rcore) = Score` is exactly what the loss tracks. With front pivot and `Sreg_E = Sreg`, the repaired target is `Sreg_E + Score`.

But this is **not cosmetic**. `coreΦ = frobSq(S0 S1)` is the reduced per-layer core product after `coreAbsorb`; `Score = frobSq(S0(I-K)S1)` is the global Schur complement and depends on the regular/spectator reads through `K`. Your curve proves these are not pointwise comparable in the published coordinates.

For RLCT: the headline value is not refuted by this curve alone. It may still be recoverable by proving a separate local change-of-variables/unit-peel from `Score` to the reduced core contribution. But the current downstream use of the `coreΦ` squeeze is not justified as stated.

(d) **Severity:** build-stopper for the producer close as currently stated. It directly kills `deepest_loss_squeeze` with `coreΦ` and any proof step depending on that two-sided lower bound. It does not by itself disprove the headline `RLCT = 1/2 * codim`; it invalidates this intermediate squeeze route unless repaired with `Score` plus a new RLCT-equivalence argument.