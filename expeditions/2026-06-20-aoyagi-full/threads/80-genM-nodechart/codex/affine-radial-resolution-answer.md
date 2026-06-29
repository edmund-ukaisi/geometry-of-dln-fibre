**Verdict:** yes for the concrete `(2,2,2)` chart. The affine-radial worry is not present there.

`pivotBlowupOn` is purely multiplicative: pivot stays `x p`; active non-pivot slots become `x p * x i`; spectators stay fixed. No additive constant is in that map. See [S1G5Charts.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean:384).

For `(2,2,2)`, the factorization is exactly:

```lean
pb222 = pivotBlowupOn {0,6,7} 0
T222  = bsubst222 ∘ shear222 ∘ pb222
chartParams222 = pack222 ∘ T222
phi222 = paramsEquivFlat ∘ chartParams222
```

The explicit `pb222_apply` is `[u0, ..., u0*u6, u0*u7]`, with no affine term, and `T222_apply` only adds the Schur/shear bilinear corrections after that. See [RouteM222Det.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:549) and [RouteM222Det.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:575). The final determinant is proven as `|u 0|^2 * |u 4|` in `phi222_abs_det`, so the radial part is exactly `|u0|^(minAdm-1)` and the engine/spectator part is `|u4|`. See [RouteM222Det.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:840).

The subtle correction: “`B` is u-free” should mean **no external radial parameter and no radial determinant factor**, not “`B` ignores coordinate `0`.” Here
`B = paramsEquivFlat ∘ pack222 ∘ bsubst222 ∘ shear222`; it still reads the pivot coordinate as an ordinary input coordinate, but its Jacobian determinant is the engine `|u4|`, not another `u0` factor.

Your conflation diagnosis is right. In the chart matrix, `C 2 = x0 · !![1, x7]`; the literal `1` becomes the pivot coordinate contribution `x0`, not an additive chart-output constant. See [RouteM222Det.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteM222Det.lean:180). The R1 live decoder similarly has a fixed `pivotEIndicator`, but `phiFlatLiveR1` reads the radial scalar from `structPivot`; that is a decoder-level fixed indicator, not an affine radial layer. See [RouteMFlatLive.lean](/tmp/RouteMFlatLive.lean:47) and [RouteMFlatLive.lean](/tmp/RouteMFlatLive.lean:263).

For general `M`, I would phrase the status skeptically:

- The faithful route is the **actual map** route: `pack/T/pb` or its `composeFold` analogue as maps. The failed `phiGen 1 (genBlkFlatLiveR1) + smulRmatRfin` route is not the right decomposition.
- The radial factor itself can remain `pivotBlowupOn active structPivot`; the generic wrapper already proves `|det| = |u_p|^(active.card-1)`. See [RouteMRadialFactor.lean](/tmp/genm-subbox-review/lean/DLNFibre/DLN/RLCT/Validate/RouteMRadialFactor.lean:33).
- The real general-M obligations are not affine-radial. They are: prove the actual `B` map identity, prove `det DB = engine` for the actual fderiv, and prove `active.card = minAdm` with the fixed pivot separated from the free angular budget.

So: **pure-multiplicative radial is resolved for `(2,2,2)`; no affine layer is needed.** Multi-dimensional K-cores do not by themselves break the radial story, but they do make the general `B` determinant/local-iso proof the hard part.