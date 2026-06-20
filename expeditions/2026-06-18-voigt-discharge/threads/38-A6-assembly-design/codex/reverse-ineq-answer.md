**Q1.** Verdict: **INTRINSIC**.
(fact: local/Mathlib) `Ideal.Cotangent`, `Ideal.Cotangent.lift`, your generic cotangent-localization finrank lemma, and M3 already line up with `m_M`. (judgement) This genuinely avoids the radical/WRINKLE issue because it never introduces `span rankMinorSet`; it works directly in `R ⧸ vanishingIdeal orbitSet`. The hidden work is not Jacobian comparison, but proving orbit directions kill `I` at first order.

**Q2.** Verdict: use direct `pderiv` + `Ideal.Cotangent.lift`; do not use L2a.
(fact: Mathlib) `Ideal.Cotangent.lift` factors a `k`-linear map `m → k` through `m/m²` once it vanishes on products. (judgement) Define `D_v f = ∑ x, eval a (pderiv x f) * v x`, descend it through `R ⧸ I` using `D_v f = 0` for `f ∈ I`, then restrict to `m` and factor through cotangent. The load-bearing discharge is: `f ∈ I = ker orbitPullback M`, evaluate `orbitPullback M f = 0` at the dual-number group element `1 + εφ`, and identify the ε-coefficient with `D_{δφ} f`.

**Q3.** Verdict: injection is the better shape.
(fact: Mathlib) `Module.Dual.dual_finrank_eq` exists at this pin, and `LinearMap.finrank_le_finrank_of_injective` is available once the dual codomain is finite-dimensional. (judgement) Injectivity is easy after tangent inclusion: if the functional from `v` is zero, test it on the cotangent classes of `X_x - a_x`, giving `v_x = 0` for every coordinate. The hard part is not nondegeneracy; it is exactly the first-order orbit-tangent inclusion `D_v(I)=0`.

**Q4.** Verdict: prove L7 additively, not by `ENat.toNat` or subtraction.
(fact: local) `finrank_cochain1 d d = ∑ i, d i.succ * d i.castSucc`. (fact: Mathlib/local) `Nat.card (RepCoord d)` reduces by `Fintype.card_sigma`, `Fintype.card_prod`, `Fintype.card_fin` to the same sum. (judgement) Use
`codimRep + r = card`, `varietyDim = r`, `card = finrank C¹`, and `orbitLinearCodim + r = finrank C¹`; then cancel the finite `r : ℕ∞`. This avoids lossy `toNat`; only use subtraction if you already have `r ≤ finrank C¹` and a finite-coe subtraction lemma.

**Q5.** Verdict: no `[CharZero k]` for the reverse inequality.
(fact) The first-order orbit calculation with dual numbers is characteristic-free. (judgement) The reverse module needs `[IsAlgClosed k]` only because M3/smooth point and the orbit-ideal primeness/kernel infrastructure are stated that way; CharZero enters only through A4’s separability/generic differential-rank side.

**Q6.** Verdict: yes, there is a real reindexing obligation for L4d.
(fact: local) `ringKrullDim_localizationAtPrime_isMaximal_eq` is stated over `MvPolynomial (Fin n) k`. (judgement) Add a finite-index wrapper using `Fintype.equivFin`, `MvPolynomial.renameEquiv`, `Ideal.quotientEquivAlg`, and a localization-at-prime equivalence for the transported maximal ideal. This is bounded boilerplate, slightly heavier than L0 because localizations/maximal ideals must be transported too.

**ROUTE RECOMMENDATION:** **INTRINSIC**. It is shorter and cleaner because all later comparisons are already about `m_M` in `orbitRing M = R ⧸ vanishingIdeal orbitSet`; no minors, no radical, no comparison between a thickened determinantal scheme and the reduced orbit closure. A5/WRINKLE is not needed. In fact, the proposed WRINKLE is dangerous: radical equality plus smoothness of the reduced quotient does not imply same cotangent for `R/J`; e.g. `J = m²`, `rad J = m`.

**Hardest Sub-Lemma:**
(judgement) `range_deformationδ_le_zariskiTangent`: for `v = δφ`, prove `D_v f = 0` for every `f ∈ orbitIdeal M`. Kill-condition: have `orbitPullback M f = 0`, evaluate at the dual-number base change `P_v = 1 + εφ`, and prove the ε-coefficient of `f(M + εδφ)` is exactly `D_v f`.

**Extra Traps:**
(fact) `vanishing on k-points` is not itself first-order vanishing; use the landed `vanishingIdeal_range_orbitMap_eq_ker` or equivalent polynomial identity.
(fact) `m_M.Cotangent` is naturally over the residue field; use `κ(m)=k`/`residueFieldNormalFormEquiv` consistently when comparing `k`-finrank to M3’s residue-field finrank.
(judgement) Avoid `ENat.toNat` in L7 until finiteness is proved; additive cancellation is safer.
(judgement) Do not let L2a into the intrinsic proof: it computes the cotangent of a chosen finite presentation, exactly where the radical thickening problem reappears.
