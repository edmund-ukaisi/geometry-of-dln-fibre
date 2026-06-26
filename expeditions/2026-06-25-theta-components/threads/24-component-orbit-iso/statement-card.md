# Statement card — `Core.FibreComponentOrbitIso` (thread 24, task #138 — the variety-level `e`)

**Status:** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. Module built standalone
(3085 jobs). Module: `lean/DLNFibre/Core/FibreComponentOrbitIso.lean`. Standalone geometric deliverable
(operator-approved enrichment) — **NOT on the critical path**: smoothness (fully unconditional via
`Core.FibreComponentOrbitTransport`), the θ-count, and the bundle do not consume it.

## Honest scope finding (Codex-adjudicated, persisted `codex/eiso-answer.md`)

The thread-20 consumer `isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` wanted
`sweepFibreRing⧸I ≃ₐ[k] MvPolynomial η (orbitRing M_shifted)` (poly wrapper on the orbit side, SHIFTED
orbit over `d−r`). **That shape is globally false / unreachable** from the chart transport: the chart
`e_β = chartLocalizedAlgEquiv` is intrinsically *localized* (`Away dsig ≃ Away gF`), `gF = detSchurS`
is a pivot-chart determinant (not a unit mod `I`), so the chart only sees the dense principal open
`D(g_I)`. Tracing the component lands the OPPOSITE shape (poly on the FIBRE side, full-`d` orbit) and
only after localization. Neither the un-localized nor the shifted-orbit form is extractable
(cancellation `R[x]≅S[y] ⇏ R≅S[…]` invalid). So the honest reachable `e` is **localized**.

## Landed — Rung 1 (the chart-localization component transport, the named "heart")

```lean
noncomputable def schurComponent_chartQuotientEquiv [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq)) :
    SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] (sweepFibreRing k d r hp hq ⧸ I)
      ≃ₐ[k] Localization.Away (chartDsig k d r hp hq) ⧸ chartComponentIdeal d r hp hq I
```
English: for a fibre component ideal `I`, the C-part-tensored component `SchurLoc ⊗_k (R_F⧸I)` is
`k`-algebra isomorphic to the quotient of the localized chart ring `Away (chartDsig)` by the
pulled-back component ideal. This is the genuine new rung the route map named ("the heart"). Proof:
`Algebra.TensorProduct.tensorQuotientEquiv` (base change of a quotient) glued to the product keystone
`reducedFibre_chartDsig_tensorEquiv_reducedVariety` by `Ideal.quotientEquivAlg`
(`chartComponentIdeal = comap Φ (I.map includeRight) = (I.map includeRight).map Φ.symm`, via
`Ideal.comap_symm`).
- `chartComponentIdeal` — the fibre component pulled to `Away chartDsig` along the product keystone.

## Landed — the assembled headline (rung 1 + the precise residual conditional)

```lean
def LocalizedChartDescent ... (I) : Prop :=
  ∃ (d' : Fin (N+1)→ℕ) (M : Tuple d') (Δ : orbitRing M),
    Nonempty ((Away (chartDsig …) ⧸ chartComponentIdeal d r hp hq I) ≃ₐ[k] Localization.Away Δ)

theorem exists_localized_schurComponent_fullOrbitEquiv_of
    [IsAlgClosed k] [CharZero k] [Infinite k] (d r hp hq) (I)
    (hdesc : LocalizedChartDescent d r hp hq I) :
    ∃ (d' : Fin (N+1)→ℕ) (M : Tuple d') (Δ : orbitRing M),
      Nonempty ((SchurLoc … ⊗[k] (sweepFibreRing k d r hp hq ⧸ I)) ≃ₐ[k] Localization.Away Δ)
```
English: GIVEN the residual descent `LocalizedChartDescent` (the (i)+(ii)+(iii) sub-wall packaged as a
precise `Prop`), the C-part-tensored fibre component is `k`-algebra iso to a **localized full-`d`**
orbit ring. Proof: rung 1 `.trans` the descent. Otherwise fully proved; the single open input is
`LocalizedChartDescent`. Names honestly localized + full-`d` (NOT global, NOT shifted-orbit), and
explicitly advances neither smoothness nor the θ-count.

## The residual `LocalizedChartDescent` (NOT built — the genuine sub-wall)

Descends `(Away chartDsig)⧸chartComponentIdeal` to a localized full-`d` orbit ring. Pieces exist but
need assembly (~mid-hundreds LoC, multi-tide): (i) `chartComponentIdeal`'s contraction is a sigma
top-dim minimal prime with `dsig` avoidance — needs a bridge from the product keystone to the
`e_β`-stated no-drop lemmas (two different isos of `Away chartDsig`); (ii) the localization-quotient
iso `(Away f)⧸(map p) ≃+* Away (mk p f)` (inside
`TopDimMinPrimesLocalization.ringKrullDim_quotient_map_localizationAway_eq`, extract as `AlgEquiv`);
(iii) the W0 descent to `orbitRing (realizerD m)` (`exists_sigma_topComponent_orbitRingEquiv`). The
LHS-form `SchurLoc ⊗ (R_F⧸I) = (MvPolynomial SchurVar (R_F⧸I))[1/g_I]` is the banked
`FibreBundleReduced.mvPolynomialAwayMapTensorAlgEquiv`.

## Aggregator import line (for the controller)
`import DLNFibre.Core.FibreComponentOrbitIso`
(after `DLNFibre.Core.FibreBundleReduced` and `DLNFibre.Core.FibreComponentOrbit`; new transitive
imports already in the library).
