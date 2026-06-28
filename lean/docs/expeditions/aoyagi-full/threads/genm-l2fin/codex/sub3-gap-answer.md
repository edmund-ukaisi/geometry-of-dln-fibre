**Q/Q2:** Yes, `h11/h12/h21` are provable, but not because `Aψ` and `Aq` are identified. Without invertibility of `Pf/Qf`, the abstract layer parameters are not pinned. What is pinned is the sandwiched observable:

```lean
endpointP0 * prod Aψ * endpointQL = prod (framedParamsPivot (psiSplitRawL2 q))
endpointP0 * prod Aq * endpointQL = prod (framedParamsPivot q)
```

via `endpoint_telescoping_eq`. So the clean path is exactly:

1. Rewrite each residual:
   ```lean
   endpointP0 * (prod A - B) * endpointQL
   =
   endpointP0 * prod A * endpointQL - endpointP0 * B * endpointQL
   ```
2. Use `endpoint_telescoping_eq` with `hframe₁/hframe₂` and `hinterface` to replace the `endpointP0 * prod A * endpointQL` terms by framed products.
3. Cancel/rewrite the common `endpointP0 * B * endpointQL` term, e.g. to the shared `fromBlocks 1 0 0 0`.
4. Prove the `{11,12,21}` block equalities for
   ```lean
   reindex (prod (framedParamsPivot (psiSplitRawL2 q)))
   =
   reindex (prod (framedParamsPivot q))
   ```
   using the L=2 readback/product lemmas.

So the entry point is not wrong if you are committed to `deepestEFull_sq_sum_eq_of_resid_blocks`; the telescope hypotheses are precisely what let abstract `Aψ/Aq` disappear. A different entry point comparing framed products directly may be shorter, but then it is a different route.

**Critical {12}:** do not apply `e2_regPreserve` naively to the `toBlocks` of the framed factors unless you have a framed version. The raw identity is about raw blocks `A0,Y0,Y1,T1,T1'`. A last-layer frame such as `Qf last` can change the apparent `{12}`/`T` blocks of the framed factor.

Thus, with certainty from the stated data: raw `e2_regPreserve` does not by itself justify the framed-factor `{12}` computation. The robust route is to telescope/de-frame the product so internal frames disappear, reduce the `{12}` preservation to the raw L=2 formula, then account for endpoint frames via the existing reindex/endpoint-frame lemmas.