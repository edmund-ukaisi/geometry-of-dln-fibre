**Q1.** FACT: The RLCT of `||f||^2` is local along `{f=0}`; points where the pulled-back loss is bounded below by a positive constant do not affect the pole or finiteness threshold.

FACT: Your `Qb*` lies on `{rank Qb <= 1}` but, by FACT 2, is a positive-loss point for the original loss chart. Therefore that dense-torus component of `I_2(Qb)` is not something the RLCT of `L` is forced to resolve.

INFERENCE: `I_2(Qb)` is forced by ROUTE 1 because the substitution `Delta = Gamma Qb` divides by the volume of the image map and creates the Jacobian factor `det(Qb Qb^T)^(-p/2)`. That is an artifact of eliminating `Gamma`, not an intrinsic component of the zero-locus resolution of `L`.

**Q2.** FACT: In ROUTE 2 the actual generators remain the entries of the coupled product expression, with `Gamma` still present as a coordinate. The centers are residual-block origins in the current chart, and det-1 Schur transforms are analytic unit changes, so they do not introduce a determinantal center.

FACT: The sharing of the same tail `C2.C3` does not by itself force Plucker minors. The common tail means the same radial exceptional variable is shared by the pivot and corank terms when the next residual block is peeled. That is exactly what avoids the false “fresh radial per generator” ledger.

INFERENCE: A non-coordinate center would be forced only if, after all coordinate residual-block peels and unit Schur clears, some unresolved vanishing depended on rank conditions of `Qb` rather than on vanishing of the actual residual product blocks. Given FACT 3, that failure does not occur: the recursion reaches a sum of squared monomials without forming `det(Qb Qb^T)`.

**Q3.** VERDICT: **(b) COORDINATE CENTERS SUFFICE.**

FACT: `I_2(Qb)` contains dense-torus rank-drop points which are not coordinate-stratum phenomena.

FACT: At the exhibited dense-torus rank-drop point, the original loss is positive, so that point is not part of the singular zero-locus contribution to the RLCT.

INFERENCE: Therefore the layer-by-layer resolution of the original loss need not principalise `I_2(Qb)`. The determinantal ideal is a ROUTE-1 artifact caused by integrating out `Gamma` over full space and changing variables through a rank-varying linear map.

**Q4.** INFERENCE: Coordinate centers sufficing does not make the proof short or trivial. It is still a substantial construction: one must track a finite staircase of residual blocks, shared exceptional radials, unit Schur transforms, and the resulting monomial exponents. The construction is elementary in the sense that its centers are smooth coordinate subspaces, but it is not small; the bookkeeping is the proof.