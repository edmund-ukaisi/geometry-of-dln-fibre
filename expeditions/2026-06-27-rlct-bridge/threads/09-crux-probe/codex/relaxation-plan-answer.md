**Q1**

**NO material risk.** `IsReduced (orbitScheme M)` is obtained through `IsDomain (orbitRing M)`, hence reducedness of the affine ring, then reducedness of `Spec`; no algebraic-closedness-specific reducedness is involved. Jacobson/rational-point facts in this path are either field/finite-type facts or explicit orbit-evaluation kernels, not `k`-points = closed-points.

**Q2**

**YES.** In Mathlib v4.29 the chain is: `IsDomain A` gives no zero divisors/nontriviality, TC infers `_root_.IsReduced A`, and `AlgebraicGeometry.Properties` has the instance `[IsReduced R] : IsReduced (Spec R)`. So once `orbitRing_isDomain` is relaxed to `[Infinite k]`, `IsReduced (Spec (.of (orbitRing M)))` should resolve automatically.

**Q3**

**YES, relax bottom-up.** Do `OrbitVariety`, then `OrbitSmooth`, then `SmoothPointRegular`, then `OrbitTangentCotangent`, building after each layer. Main gotcha: section-level `variable [IsAlgClosed k]` should become narrower section variables, and existing `omit [IsAlgClosed k]` lines may need replacement by `omit [PerfectField k] [Infinite k]` to keep helper signatures clean. Downstream callers with `[IsAlgClosed k]` should still work: Mathlib v4.29 has `IsAlgClosed → PerfectField` and `IsAlgClosed → Infinite`; only brittle fully explicit `@lemma` calls may need argument adjustment.

**Q4**

**Route R2.** Use the local/linear-map base-change route, not integer matrix rank: `DLNFibre.Core.finrank_range_baseChange` already proves `finrank K (range (f.baseChange K)) = finrank k (range f)`. I am confident these v4.29 names exist: `LinearMap.toMatrix'`, `LinearMap.baseChange`, `LinearMap.baseChange_eq_ltensor`, `Module.finrank_baseChange`, and local `finrank_range_baseChange`; I did not find a ready `Matrix.rank_map_eq`/`Matrix.map_rank` lemma. L7 is packaging: prove `deformationδ_K (M.map ι)` is conjugate to `(deformationδ_ℝ M).baseChange K` under the standard tensor/Pi/matrix equivalences; the integer entries are unnecessary for R2.

**GO/NO-GO**

**GO:** the relaxation is mechanical; no new math, only typeclass/signature cleanup plus L7 packaging.