**1. VERDICT**  
For the real `(2,2,2)` blow-up node, the lemma is **not a sound substitute for the blow-up cover**: MP reindexing exists, but the intended Schur squeeze is not obtained from raw `Params` by that MP chart; the non-MP blow-up weight must be explicit.

**2. THE CHART vs THE BLOW-UP**  
Your distinction is partly right: `paramsEquivFlat`-style coordinate reindexing is genuinely measure-preserving and is not `step1A`. The Explore agent is wrong if it literally says no MP product homeomorphism exists. But the crucial extra hypothesis is `hsq`, not just `hmp`. For `(2,2,2)` at the zero-core origin, the hard-pivot Schur form only appears after the blow-up `A = y₀·Â` with `Â₀₀ = 1`. A raw MP reindex of `Params` keeps the original bilinear loss `‖AB‖²`, whose generator Jacobian has rank `0`; it is not locally squeezable by a positive regular-square block of the hard-pivot form. So the chart and blow-up are separate maps, but the squeeze secretly needs the post-blow-up coordinates.

**3. THE REAL LOCATION OF y0³**  
`y₀³` belongs in the **weighted change-of-variables/cover**, not in an ordinary unweighted `rlctAtOn (G²)`. The change of variables gives  
`∫ |F|^{-c} dx = ∫ |F(step1A y)|^{-c} · |y₀|³ dy`.  
If `F(step1A y) = y₀²·Q(y)`, the exceptional divisor has threshold `(3+1)/(2·1)=2`; without the Jacobian it would be `1/2`. That shift is real. Downstream blow-ups used to compute `rlctAtOn(Q)` or `rlctAtOn(G²)` correctly carry their own Jacobians, but they do not automatically carry the upstream `y₀³` unless the cover/weighted-threshold statement includes it. In `(2,2,2)` the `y₀` divisor is nonbinding, so dropping it may accidentally leave the final value `3/2`; it is still not a sound descent principle.

**4. IF VACUOUS — THE FIX**  
Keep the MP squeeze lemma only for genuine MP/unit-Jacobian phases or for a post-blow-up `flatCore` already living in blown-up coordinates. For blow-up nodes, use a weighted cover/transport statement:
`weightedThreshold F 1 = weightedThreshold (F ∘ π) |Jac π|`, then evaluate monomial/smooth-block leaves with the Jacobian weight. A non-MP “chart” lemma must expose the vanishing Jacobian; a plain `rlctAtOn_comp_homeomorph` route is the wrong tool for blow-ups.