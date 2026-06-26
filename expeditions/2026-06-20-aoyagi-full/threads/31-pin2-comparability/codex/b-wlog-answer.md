1. **Q1: SOUND, with one qualification.**  
For *local* `rlctAt`, the measure-preserving coordinate permutation `τ_Π` gives equality only at corresponding germs:

`rlctAt (dlnLoss H B) w0 = rlctAt (dlnLoss H (B·Π)) (τ_Π w0)`.

So if the theorem literally compares `w0(B)` with the freshly constructed `w0(B·Π)`, you either need **exact** equivariance:

`w0(B·Π) = τ_Π(w0(B))`

or a bridge showing both local values equal the same global minimum.

The clean sound route is the **global-loss-zero-set argument**: `τ_Π` is a global measure-preserving diffeomorphism and maps the zero set of `dlnLoss H B` bijectively to the zero set of `dlnLoss H (B·Π)`. Therefore the **global RLCT minimum over the zero set** is preserved. Then the fresh deepest chart for `B·Π` computes that preserved minimum. This avoids needing pointwise deepest-construction equivariance.  
Exact: loss identity, rank preservation, front-pivot after Π.  
Inference: global-min bridge is sound if the formal statement is global RLCT or already proves deepest local RLCT equals the global minimum.

2. **Q2: B is decisively less Lean than A′.**  
A′ requires two large, unbuilt geometric/reindexing components:

- corrected non-clean `Pπ` telescope;
- FACT2 reindex identity for `M·Pπ`;

then Frobenius comparability.

B replaces that with mostly standard algebraic transport:

- mechanical loss identity under last-layer column permutation;
- determinant/measure-preserving fact for a coordinate permutation;
- existing or standard `rlctAt`/RLCT invariance under MP homeomorphism;
- fresh invocation of the already designed front-pivot gauge construction;
- front-pivot existence by column permutation.

So B is lower risk and shorter unless `rlctAt` measure-preserving invariance is not banked at all. Even then, proving a general MP invariance lemma is more reusable and cleaner than building the special `Pπ` telescope plus FACT2.

3. **Q3: Caveat avoided.**  
Yes. Because B constructs a fresh chart for `B·Π`, Π is not forced into the old `QL`, and no commutation with the old frame is needed. The residual obligation is only to show the new target has front pivots and that the fresh chart’s hypotheses apply.

The sound, less-Lean route is **B** because it reduces the problem to global MP invariance plus a fresh front-pivot chart, avoiding the unbuilt `Pπ` telescope and FACT2; B's `rlctAt`-invariance rests on **banked X** if MP germ/global invariance already exists, otherwise on a single reusable unbuilt invariance lemma.