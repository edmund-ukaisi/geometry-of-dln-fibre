# Roadmap — formalising the geometry of DLN multiplication fibres

The programme-level map: the destination, the bundles of work toward it, and what each depends on. Written
to be elementary; pick up a **bundle** only when it is *whole-in-reach*, rather than nibbling one lemma at a
time. Update at each expedition close.

## The destination, plainly

For tuples of composable matrices $A_\ast=(A_1,\dots,A_N)$ with $A_i:k^{d_{i-1}}\to k^{d_i}$ and the
multiplication map $\operatorname{mult}(A_\ast)=A_N\cdots A_1$, we want, in honest Lean:

- the **codimension** $C$ and **number** $\theta$ of top-dimensional irreducible components of the rank-$r$
  product locus and of the fibre $\operatorname{mult}^{-1}(B)$;
- the paper's **three computations** of $(C,\theta)$ (Poincaré series · quadratic integer program · explicit
  formula) and the **permutation invariance** of $(C,\theta)$ in $\underline d$;
- the payoff: $\operatorname{rlct}(K^{\mathrm{DLN}}_B)=C/2$ (the square-Frobenius loss; DLNs are "mildly
  singular").

## The map (paper §§2–8)

```
   Rep_d, mult, Σ^r, fibres        (§4 — the ambient objects)
        │  type-A quiver translation (§2: Gabriel ⟹ orbits ↔ Kostant partitions ↔ rank patterns)
        ▼
   orbit decomposition + closure order (§3, Thm 3.8) + Ext codimension (§3, Cor 3.5)
        │
        ▼
   (C, θ):  Poincaré series (§5, Thm 5.5) ─► permutation invariance (Cor 5.10)
            quadratic integer program (§6, Thm 6.1)
            explicit lattice-point formula (§7, Thm 7.10)
        │
        ▼
   rlct(K^DLN_B) = C/2   (§8, Thm 8.6;  via the cited rlct = ½·codim equality, Aoyagi/Watanabe)
```

Everything above "rlct" is **network-free** → `DLNFibre.Core`. The loss + RLCT payoff → `DLNFibre.DLN`.

## What Mathlib provides (resolved)

**What does Mathlib already provide?** Quiver representations, the type-A / `A_n` story, Gabriel's theorem,
`Ext` for quiver reps / representations of a category, equivariant cohomology. The answer decides how much of
the engine is *reuse* vs *build-from-scratch* — and the build-from-scratch part *is* the reusable asset, so
getting its API right is high-value. **Resolved** (the Bundle sections below record the outcome): Mathlib
had no type-A Gabriel classification, no `Ext`-codimension for these representations, and no orbit-closure
order for the chains — the engine was built from scratch as `DLNFibre.Core`.

## The bundles

Pick up a bundle only when it is whole-in-reach.

### Bundle 1 — the combinatorial core  ·  `DLNFibre.Core` (Codim / RankPattern)
**Plainly.** The parts that are *elementary combinatorics + linear algebra*, largely independent of heavy
quiver-rep infrastructure: rank patterns ↔ Kostant-partition multiplicities and the inclusion-exclusion
inversion (§3, Prop 3.1); the quadratic integer program (§6, Thm 6.1); the explicit codimension formula and
the closest-lattice-point component count (§7, Thm 7.10); the reductions rank-$r$ → rank-$0$ and fibre-codim
(§4, Lemmas 4.5–4.6). **Reachability:** the most reachable bundle — finite types, matrices, ℕ-combinatorics.
**Landed (expedition `core-quiver-engine`, reviewed + bedrock):** the ambient objects
(`Core.Setup`: `mult`, `Σ^r`/`Σ^{≤r}`, `fibre`); the matrix-side rank pattern (`Core.Submult`:
`submult`/`rankPattern`, `r_{ii}=d_i`); and **Prop 3.1 in BOTH directions** — the abstract `cumul`↔`diff`
inversion (`Core.RankPattern.cumulDiffEquiv`) AND, for an *arbitrary tuple*, `r_{ij}` = `cumul` of its
Gabriel multiplicities with the Kostant constraint (Prop 3.1b, `Core.Gabriel.exists_barcode_rankPattern`).
**Landed (expedition `c-theta`, reviewed + bedrock; pure ℕ-combinatorics on the proven Cor 3.5 form, no
AG):** the combinatorial $(C,\theta)$ as the minimisation of $\sum m_{i-1,j-1}m_{uv}$ over the Kostant
partitions of $\underline d$ with $m_{0N}=r$ (`Core.CTheta`: `cCodim`/`numTop`, rank-shift
`cCodim_rankShift`); **the QIP (Thm 6.1)** as the full equality `cCodim_eq_qipMin` (`Core.CThetaQIP`/
`CThetaQIPConverse`, `Monotone d`); and **the explicit formula (Thm 7.10, $r=0$)** in both parts —
**$C$**: `qipMin_eq_cValue : qipMin d = cValue d` with the closed form
$C=\tfrac12(d_0^2-\sum_{i=1}^m(d_i-d_0)^2+m(a-d_0)^2+2(a-d_0)\delta+|\delta|)$ (`Core.CThetaValue`,
$m=$`qipM` a `Nat.findGreatest`, $a=\lfloor S/m+\tfrac12\rfloor$, $\delta=S-ma$), via the drop-to-$m$
active-support reduction (`Core.CThetaDropM`: `qip_minimiser_support_le_m`) + the square-completion bridge
and the **elementary integer-square lemma** `isLeast_sumSq` (`Core.CThetaExplicit`) **replacing the paper's
Conway–Sloane closest-vector apparatus**; and **$\theta$**: `qipNumMinimisers_eq_cTheta : \#\{\text{QIP
minimisers}\}=\binom{m}{|\delta|}$ via a minimiser↔$|\delta|$-subset bijection. Witnesses (decide+kernel):
$(2,2,2)\!\to\!(3,1)$, Ex 6.3 $\to\!(55,4)$, matching the paper. All axiom-clean.
**Landed (expedition `perm-invariance`, PR #6, reviewed + bedrock):** **permutation invariance
(Cor 5.10) — Proved, zero-cited** (`Core.CThetaPermInvariance.cCodim_comp_perm`/`numTop_comp_perm`),
via a reproof of the **Poincaré-series formula Thm 5.5** (`Core.QSeriesThm55.thm55`) and the **fivegon
Thm 5.6** (`Core.QSeriesFivegon.fivegon` = RWY 2018), built on a from-scratch $q$-series sub-library
(Bundle 3's combinatorial route succeeded — see Bundle 3). The **aggregate** geometric reading is now
also **Proved**: $C=\operatorname{codim}\overline{\Sigma}{}^r$
(`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`) and
$\theta=\#\{\text{top-dim components of }\overline{\Sigma}{}^r\}$
(`Core.CCodimZeroStrict.numTop_eq_ncard_topComponents`, unconditional), transported across permutations
in `Core.CThetaGeometricPerm`.
**Landed (expedition `explicit-ctheta`, reviewed + bedrock):** the **explicit closed form for an
arbitrary (non-monotone) $\underline d$** — composing the sort bridge (`cCodim_comp_sort`) with the
`Monotone`-gated `cValue`/`cTheta` drops the monotonicity gate:
$C=\operatorname{cValue}((\underline d-r)\circ\operatorname{sort})$,
$\theta=\operatorname{cTheta}((\underline d-r)\circ\operatorname{sort})$ for any $\underline d$
(`Core.CThetaArbitrary.cCodim_eq_cValue_comp_sort`/`numTop_eq_cTheta_comp_sort`; witness $(2,3,2)\to(4,2)$).
**Remaining in Bundle 1 (future):** the §4 **fibre-codim reduction (Lemma 4.6)** — the per-orbit
geometric reading (`codimForm` = geometric codimension of the orbit closure $\bar O_M$) is **Proved**
(Bundle 2 / `voigt-discharge`).

**Lemma 4.6 bundle-shift `codim(fibre B) = C + r(d₀+d_N−r)` — PROVED unconditionally, zero-cite for the
geometry (expedition `fibre-codim`, 2026-06-25).** `Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`:
for any rank-`r` `B` over an algebraically closed char-0 field (`k : Type 0`),
`codimRepCanonical (fibre d B) = (cCodim d r h).toNat + r·(d_N + d_0 − r)` — **no Cited interface for the
geometry**. Build green, `scripts/sorries` 0, `#print axioms = [propext, Classical.choice, Quot.sound]`
(no `sorryAx`). Minimal-hyp form: only `[IsAlgClosed][CharZero]` + `h : (kostantPartitions d r).Nonempty`
+ `B.rank = r`. **Double-gated by independent decorrelated review:** `e`-fidelity (#67 PASS) and codim↔paper
fidelity (#68 PASS — matches LR Lemma 4.6, `(2,2,2)` checked by hand+`decide`, no overclaim;
`reviews/68-codim-final-fidelity.md`).
**The route that broke the earlier residual (route-β):** the `BundleShiftInterface` residual — the deep
flat/smooth trivialization of `Σ̄^r`, left by the 2026-06-24 outcome as a "circular-as-a-Lean-route,
≥2-module from-scratch AG sub-project" — was BUILT directly as the **localized chart `AlgEquiv`**
`Core.ChartLocalizedAlgEquiv.chartLocalizedAlgEquiv : O(Σ^r)[1/Δ] ≃ₐ[k] O(F)⊗stratum[1/g]`, staying
**radical-insensitive (vanishingIdeal-side) throughout** so the `IsReduced`-then-build circularity never
arises. Seams A–E (the Ψ/Φ comorphism descents + the gauge-group-law round-trips, the matrix-inverse wall
sidestepped at the units level); fed with the **source no-drop** `Core.SourceNoDrop` (Fact B `detΔ∉P` +
the ℕ∞ catenary, riding only the *free* orbit-in-Σ^r containment — no closure-density entanglement) through
`Core.ChartSweepWiring.sweep_of_localizedChartAlgEquiv` → **hSweep** (`varietyDim Σ^r = δ + varietyDim F`,
now a Proved lemma) → the route-c assembly `Core.RouteCAssembly` (carries the in-repo `hClosure`).
**Scope:** `k : Type 0` (the DLN field — ℝ/ℂ; a universe lift is roadmap-able, loses nothing for the
application). **Still Cited (out of scope):** `rlct = ½·codim` (Aoyagi/Watanabe). **Payoff DISCHARGED
(#52):** `DLN.BundleShiftDischarge` proves the bundle shift from Core (`bundleShift_of_core`); the rewired
`rlct_lossDLN_eq_half_cCodim_add_shift` rests on ONLY the Cited Aoyagi `RlctInterface` — the destination
`rlct = C/2` is realized (geometric half zero-cite; only the Aoyagi `rlct = ½·codim` equality Cited). Full record:
`expeditions/2026-06-23-fibre-codim/synthesis.md`.

**Aoyagi closed form recovered def-by-def (expedition `fibre-codim`, 2026-06-25).** `DLN.Aoyagi.ClosedForm`:
`codimRepCanonical_fibre_eq_two_paperLambda` — `codim(mult⁻¹ B) = 2·paperLambda`, with `paperLambda` Aoyagi
Thm 2's displayed λ at *her own* Definition-3 active-set size `paperEll` (certified the unique solution of her
Definition-3 conditions; the paper's `(ℓ−1)→ℓ` misprint corrected). Zero-cite, axiom-clean.

**Type-universe lift (Core) — roadmapped, low priority.** The codim/θ geometric results sit at `k : Type`
(universe 0; covers ℝ/ℂ/`AlgebraicClosure ℚ`). Lift `Core.FibreCodimFinal`, the Schur-side no-drop, and the
chart machinery (`Core.ChartLocalizedAlgEquiv`) to `Type u`. Mechanical refactor, no new math; unblocks
fully-general statements. Deferred behind the θ side.

**θ / top-component side + rest of Lemma 4.6 — CLOSED (expedition `theta-components`, 2026-06-26).** Full
record: `expeditions/2026-06-25-theta-components/synthesis.md`. The substantive mathematics is **Proved,
unconditional, axiom-clean** (`k : Type 0`, whole library green 3805):
- **Fibre θ-count, arbitrary rank-`r` `B`** — `numTop(mult⁻¹ B) = cTheta(d−r) = C(m,|δ|)` for ANY `B` with
  `B.rank = r`: `Core.FibreThetaCountArbitrary.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank`
  (`Type 0`). The normal-form case `E_r` is
  `Core.FibreThetaCount.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus` (the `TopDimMinPrimes` count chain
  through the chart `e`, reducedness-free via `detΔ`-unit; `Monotone d` + rank + Kostant-nonempty hyps);
  the same-rank transport `ncard_topDimMinPrimes_fibre_eq_of_rank_eq` (`mult⁻¹ B` a `GL×GL` translate of
  `mult⁻¹ E_r` ⟹ iso ⟹ equal count) lifts it to arbitrary `B`. Resolves #54. (The transport proof goes
  directly via `exists_baseChange_of_rank_eq` + `image_smul_fibre` + `vanishingIdeal_image_smul` +
  quotient-equiv + radical-insensitivity — `reducedFibre_baseChangeHomogeneous` is morally the same
  homogeneity but is not the literal proof dependency. Generality added in PR #11 review round 1.)
- **θ-formula finding (precision):** three distinct invariants — the component count `C(m,|δ|)` (Lean
  `cTheta`; LR's θ), Aoyagi's SLT pole order (the rlcm) `a(ℓ−a)+1`, and the log-log coefficient
  `a(ℓ−a)` (= rlcm − 1; the expression LR print in the rlcm slot). Agree iff `|δ| ≤ 1`, diverge for
  `|δ| ≥ 2` (witness `(2,2,2,2,2)` r=0: 6/5/4). Root of the discrepancy (operator ruling 2026-07-22):
  a θ-type component count is not a pole multiplicity — the quantity in that slot is not an rlcm, so
  no erratum/correspondence is pursued; the distinction is recorded, not litigated. The `rlct = C/2`
  story is unaffected. Written up: `docs/expositions/theta-invariants-distinction.md`.
- **Generic smoothness of the fibre — FULLY UNCONDITIONAL** (`Core.FibreComponentOrbitTransport.isSmoothAt_sweepFibre_topComponent`,
  `[IsAlgClosed k]`): a fibre top component is an fp domain over an alg-closed field, hence generically
  smooth (`IsSmoothAt k ⊥`); lifted via the C1 localization-recovers-component bridge. The OrbitSmooth/orbit-iso
  route was unnecessary for smoothness. Chart-level form: `isSmoothAt_chartDsig_topComponent_nonvacuous`
  (smooth on a NONEMPTY basic open `D(h)`, `¬IsNilpotent h`) — the stronger, non-vacuous statement; the
  weaker `exists_isSmoothAt_chartDsig_unconditional` (smooth on *some* basic open, incidence with the chosen
  component not certified) is superseded by it. Full component-incidence `D(h)∩V(I)≠∅` is residual 5.
- **Σ̄^r component ↔ orbit labeling — unconditional** (`exists_sigma_topComponent_orbitRingEquiv`): the first
  genuine "label a top component by an orbit ring".
- **Bundle — the per-pivot local-product atlas over the rank-`=r` open** (`Core.FibreBundleLocallyTrivialFull.reducedFibre_pivotLocalProductAtlasOnRankOpen`):
  scheme open-cover by the per-pivot Schur charts + the cover→`PivotDatum` bridge (`pivotOfCover`, PR #11
  C1) connecting a covering chart to its trivialization + trivializations into the standard fibre `SchurLoc
  ⊗ sweepFibreRing` + the base-side overlap-restricted transition (`overlapRestrict` /
  `chartOverlapTransition_restrict`, PR #11 C2) + the intertwining (`e_β` cancels) + the k-point rank-tie.
  Honestly **NOT** `locallyTrivial`. The `transitionFactors` field is a common-target cancellation (NOT an
  overlap cocycle — corrected in C2); the full overlap-restricted *trivialization* cocycle is a residual.
- **`e` (fibre-component↔orbit), localized chart transport — rung 1** (`Core.FibreComponentOrbitIso.schurComponent_chartQuotientEquiv`).
- **Reusable spin-outs:** `mvPolynomialAwayMapTensorAlgEquiv`, `exists_invertible_minor_of_rank` (Mathlib
  v4.29 gap: rank-`r` ⟹ invertible `r×r` minor), the `awayOverlap`/`awayTriple` cocycle engine,
  `localizationAtPrimeQuotientAlgEquiv`, `Algebra.Smooth.tensorProduct`,
  `isSmoothAt_bot_of_finitePresentation_domain`.

**Roadmapped residuals (deferred at the honest ceiling — all genuinely non-trivial / off-critical-path;
items 4–5 are the honest residuals surfaced by the PR #11 owner review):**
1. **Bundle → bare scheme-theoretic `locallyTrivial`:** the prime-level **residue-field-rank bridge**
   (`P ∈ rankROpen ↔ universal matrix over κ(P) has rank r`) is now **LANDED** — S1
   `FibreRankBridge.mem_rankROpen_iff_rank_universalMatrixResidue_eq` (fibration-geometry), as a
   set-of-primes identity. What remains toward a bare scheme-theoretic `locallyTrivial` is the over-base
   **projection compatibility** + the overlap-gluing cocycle (R1) — see the fibration-geometry close
   section below.
2. **`e` → full localized iso:** rung 1 (`schurComponent_chartQuotientEquiv`) + the assembled CONDITIONAL
   headline `exists_localized_schurComponent_fullOrbitEquiv_of` are landed (axiom-clean); the open input is
   the typed Prop `LocalizedChartDescent` — the chart→sigma→orbit descent of `(Away chartDsig)⧸chartComponentIdeal`
   to `Away Δ (orbitRing (realizerD m))`. Reassessed as a **multi-tide sub-wall** (D1: bridge the keystone
   `Φ` and the chart `e_β` so the W1/chartE lemmas apply; extract the localization-quotient AlgEquiv; W0
   descent), off every critical path (smoothness is unconditional without it), consumed by nothing. NOTE: the
   *global* / *shifted-orbit* shapes are FALSE — only the localized full-`d`-orbit form is reachable; two dead
   consumers relabeled as superseded scaffolding.
3. **Type-universe lift** (Core, `k : Type 0 → Type u`): mechanical, deferred.
4. **Bundle full overlap *trivialization* cocycle** (PR #11 C2 residual): the atlas has the base-side
   overlap-restricted transition (`overlapRestrict`); the full overlap-restricted *trivialization* cocycle
   square needs a target-side localization comparison `targetOverlapTransition` — the per-pivot chart map is
   only a `k`-algebra (gauge) map, not `sweepSigmaRing`-algebra, so the localization-subsingleton trick
   fails. Genuinely new/heavy; the current `transitionFactors` is honestly a common-target cancellation.
5. **Smoothness full component-incidence** (PR #11 C4 residual): the chart-smoothness witness is non-vacuous
   (`isSmoothAt_chartDsig_topComponent_nonvacuous`: `D(h) ≠ ∅`), but full incidence `D(h) ∩ V(I) ≠ ∅` (the
   smooth open meets the chosen top component) needs faithfully-flat lying-over of `includeRight :
   sweepFibreRing → SchurLoc ⊗_k sweepFibreRing` — needs `Module.FaithfullyFlat` (not TC-discoverable:
   `Module.Free k SchurLoc` + `Nontrivial` + a tensor-orientation flip). The `sweepFibreRing`-level
   `isSmoothAt_sweepFibre_topComponent` IS per-component; only the chart-level transport drops incidence.

### Bundle 2 — quiver / orbit geometry  ·  `DLNFibre.Core` (Quiver / Orbit)
**Plainly.** The representation-theoretic engine: type-A quiver representations, the $G_{\underline d}$-action,
orbits = isomorphism classes (Thm 2.4), Gabriel's interval-module decomposition (Thm 2.5), orbits ↔ Kostant
partitions (Cor 2.9), the orbit-closure order (Thm 3.8), and the $\operatorname{Ext}(M,M)$ normal-slice
codimension (Cor 3.5, Voigt). **Depends on:** the Mathlib-coverage answer. **Reachability:** real work;
possibly build-from-scratch for Gabriel/`Ext` in this special type-A case.
**Landed (expedition `core-quiver-engine`, reviewed + bedrock; built from scratch — Mathlib had no type-A
Gabriel — on the `Tuple`-as-representation encoding):** the $G_{\underline d}$-action (`Core.BaseChange`);
**type-A Gabriel existence** (Thm 2.5) on abstract chains (`Core.Barcode.hasBarcode_of_isSubrep`) carried to
tuples (`Core.Gabriel.hasBarcode_tuple`); the **complete $G_{\underline d}$-invariant**
`rankPattern A = rankPattern B ↔ A ~ B` + the Gabriel **normal-form object** `g·A = ⊕ M^m` (`Core.Orbit`);
and **orbits ↔ Kostant (Cor 2.9)** as `Core.OrbitKostant.orbitKostantEquiv`.
**Landed (expedition `ext-codimension`, reviewed + bedrock; standard hereditary route built from scratch on
the Phase-A `Tuple` δ):** the **$\operatorname{Ext}(M,M)$ codimension (Cor 3.5)** — the algebraic content
$\dim\operatorname{Ext}^1(M,M)=\sum_{1\le i\le u\le j\le v\le N} m_{i-1,j-1}m_{uv}$ **Proved** via the
2-term deformation/Ringel complex (`Core.DeformationExt`); the tangent codimension
$\operatorname{orbitLinearCodim}=\dim\operatorname{Ext}^1$ **Proved** (`Core.OrbitLinearCodim`); and the
geometric codimension $\operatorname{codim}(\operatorname{orbitRankLocus} M)=\sum m_{i-1,j-1}m_{uv}$
stated **conditional on one named hypothesis `hVoigt`** (Voigt's lemma) (`Core.OrbitCodim`) — at that
expedition's close `hVoigt` was the sole remaining input; it is now discharged (see below).
**Landed (expedition `voigt-discharge`, reviewed + bedrock; an AG dimension-theory library built from scratch
— affine-variety codimension via `Ideal.height`; orbit smoothness; $\dim\mathcal O=\dim G-\dim\operatorname{Aut}$,
i.e. tangent $=\operatorname{im}\delta$):** `hVoigt` is **Proved** unconditionally
(`Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim`, `[IsAlgClosed k] [CharZero k]`) — the A4
submersion bound and the A6.1 reverse inequality squeeze to $\operatorname{varietyDim}\bar O_M=\operatorname{finrank}(\operatorname{range}\delta^0)$,
and the additive L7 cancellation yields Voigt's lemma — so `Core.OrbitCodim`'s conditional geometric headline
becomes **unconditional** (`codimRepCanonical_orbitRankLocus_eq_multSum_unconditional`). The orbit-closure
order (**Thm 3.8**, $\operatorname{orbitRankLocus} M=\bar O_M$) is **Proved in-engine**
(`Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`, the Abeasis–Del Fra theorem at the
ideal/closure level). The **per-orbit** geometric reading (combinatorial codimension form $=$ geometric
orbit-closure codimension) is then **Proved** (`Core.CThetaGeometric.codimRepCanonical_orbitRankLocus_eq_codimForm`,
and `cCodim_eq_inf_geomCodim`: $C=\min$ over Kostant partitions of the genuine geometric codim).
**Landed (closed-locus aggregate, post-PR #6) — the $\overline{\Sigma}{}^r$-aggregate reading is Proved.**
$\operatorname{codim}\overline{\Sigma}{}^r = C$ (`Core.SigmaCodim`), its irreducible components are the
orbit closures (`Core.SigmaComponents`), and
$\theta = \#\{\text{top-dim components of }\overline{\Sigma}{}^r\}$
(`Core.CCodimZeroStrict.numTop_eq_ncard_topComponents`, unconditional) — see Bundle 1. The one piece
**not** separately built is the *exact-rank* $\Sigma^r$ (rank *exactly* $r$) as its own variety; but
$\operatorname{codim}\Sigma^r = \operatorname{codim}\overline{\Sigma}{}^r$ (the Zariski closure
preserves codimension, LR Cor 4.4 + Lemma 4.5), so the closed locus already carries the aggregate
$(C,\theta)$ content and carving $\Sigma^r$ out separately is not needed.

### Bundle 3 — the topology  ·  `DLNFibre.Core` (Poincaré)
**Plainly.** The Poincaré series (Thm 5.5) and the permutation invariance it yields (Cor 5.10).
**Landed (expedition `perm-invariance`, PR #6, reviewed + bedrock) — zero-cited; the combinatorial route
won.** Rather than equivariant cohomology (Mathlib-absent), Thm 5.5 and Cor 5.10 were reproved from
scratch via a from-scratch $q$-series sub-library: the fivegon (Thm 5.6 = RWY 2018,
`Core.QSeriesFivegon.fivegon`) → the per-corner Poincaré product (Thm 5.5, `Core.QSeriesThm55.thm55`,
through an inverse-Pochhammer orthogonality `Core.QSeriesOrth.orth` — no $q$-binomial library needed) →
the manifestly multiset-symmetric closed form ⟹ Cor 5.10 (`Core.CThetaPermInvariance`). Nothing here is
Cited.

**How it was proved (supersedes the 2026-06-18 `c-theta`-close scoping).** That close framed Cor 5.10 as
an open lift with two candidate routes — (1) an elementary combinatorial bridge, (2) the paper's
equivariant-cohomology Poincaré series. **Route 1 won, in a sharpened form.** The bridge is
`cCodim_comp_sort`/`numTop_comp_sort` ($(C,\theta)$ of $\underline d$ = that of its sorted form), itself a
corollary of the full $q$-series reproof of Thm 5.5 above — **not** a bare adjacent-transposition
bijection: the Kostant sets are *not* equinumerous across a permutation (so no value-preserving bijection
exists), and the invariance is read off the symmetric generating function instead. The
`numTop d 0 = qipNumMinimisers` link the scoping flagged as "not yet built" is now
`Core.CThetaThetaBridge.numTop_zero_eq_cTheta`. Combined with the explicit closed form (Bundle 1,
expedition `explicit-ctheta`), $(C,\theta)$ now has an explicit formula for **arbitrary** $\underline d$.

### Bundle 4 — the DLN / RLCT application  ·  `DLNFibre.DLN`
**Plainly.** The square-Frobenius loss $K^{\mathrm{DLN}}_B$, its zero-set = the fibre, and the payoff
$\operatorname{rlct}=C/2$ (Thm 8.6). The geometric codimension is Bundle 1/2 content; the analytic direction
$\operatorname{rlct}\le\tfrac12\operatorname{codim}$ is **Cited** (Aoyagi / Watanabe) — named as such, never
folded into a theorem name. **Depends on:** Bundle 1 (the codimension value).

**Deferred seam — the θ analytic-multiplicity (future expedition).** The `aoyagi-full` expedition
proved the learning coefficient **value** $\lambda = $ `aoyagiLambda` (the four headlines, S2-free) but
NOT the RLCT **multiplicity** — the pole ORDER at $-\lambda$, Aoyagi's
$r_{\mathrm{order}} = a(\ell-a)+1$ (her Lemma 5). **TWO DISTINCT θ-INVARIANTS — do not conflate**
(non-identity machine-verified 2026-07-19): Aoyagi's $r_{\mathrm{order}} = a(\ell-a)+1$ (the RLCT
pole order, a binding-branch count) is **NOT** this repo's Bundle-1 $\theta_{\mathrm{geo}} =$
`numTop`/`cTheta` $= \binom{m}{|\delta|}$ (the number of top-dimensional components of
$\bar\Sigma^r$). Witness: at $d=(2,2,2,2,2)$, `cTheta` $= \binom{4}{2} = 6$ while
$a(\ell-a)+1 = 2\cdot 2+1 = 5$ — they coincide at small cases by accident. The earlier Lean
placeholder (`aoyagiTheta_eq`, a bare `sorry`) resting on the `opaque monomialOrderAnalytic` + the
`monomial_rlct.2` axiom conjunct was **excised** (Stage B, `genm-excise`) rather than sorry-carried —
a placeholder on an opaque is not honest content (standing-decision-6). The `aoyagiTheta`
*definition* survives; the **combinatorial** $r_{\mathrm{order}}$ count (Lemmas 4–5, the two-envelope
binding-branch count — no analytics) is a live build item (expedition aoyagi-engine build-list #2).
What remains beyond it: bind the **analytic** pole-multiplicity of the DLN zeta at $-\lambda$ to
$a(\ell-a)+1$ — **never to `numTop`** (the mint guard). Statement + kill-condition:
[`cards/theta-analytic-multiplicity-seam.md`](expeditions/2026-06-20-aoyagi-full/cards/theta-analytic-multiplicity-seam.md).
The value ($\lambda$) headline does not need it. See
`docs/expositions/notes/theta-invariants-non-identity.md`.
### Bundle 4b — generic RLCT foundation (LARGELY LANDED · expedition `rlct-foundation`, 2026-07-06)

**Status: the headline honesty win is BANKED.** The payoff no longer leans on an opaque assumed
`rlct : Loss → ℝ`: that map (`rlctReal`) is **retired**, and the payoff now reads a **defined, cite-free**
invariant. RLCT is **not** DLN-specific — only Aoyagi's computation is — so the foundation lives in `Core`,
outside `DLN`. (The caveat at the end of this bundle predicted exactly this first slice — "value-only
integrability threshold + core invariances + quadratic block `λ=c/2` + axiom retirement is the headline
honesty win"; that is now done.)

**LANDED (cite-free unless noted; `Core/Analysis/RLCT/` + `DLN/`).**
- **Citation cordon** (`@[cited]` attribute + the forget-proof batched `#assert_banked_clean_batch` root gate + the `scripts/cordon` source grep, both via `scripts/cordon-all`; `CITED=3`) —
  every cited axiom named + located, and a cite's *non-vacuity* is a build-time obligation (round-7 lesson).
- **Local RLCT value** `rlctAt K x = sSup{c≥0 : K^{-c} loc-integrable at x}` (`Local.lean`, Def 8.1(ii)) + the
  **regional** threshold `integrabilityThreshold K U` (`Integrability.lean`).
- **Global RLCT** `rlctGlobal K = sSup{c≥0 : ∀x, K^{-c} loc-integrable}` (`Global.lean`, Def 8.1(i)); the
  `rlctGlobal ≤ rlctAt` half + the inf-over-zero-locus characterization (Prop 8.3(iii)) as a clean conditional.
- **Local zeta pair** `ζ_{K,φ}(s)=∫K^s φ` with cite-free convergence for `Re s>0` (`Zeta.lean`); the ONE
  bundled **continuation monument** (`Cited.lean`, Atiyah 1970 + Saito/SLT): meromorphic continuation, poles
  ⊂ ℚ_{<0}, largest pole `= −rlctAt K x₀` of order `m`; `RLCTPair (λ,m)` + Link 1 `λ = rlctAt` (`Pair.lean`).
  `m` is **define-only** (pole order, NOT the DLN `θ` — that boundary is now stated, not smuggled). Cite
  non-vacuity proven by the axiom-clean witness `zetaSetupSq` (`Witness.lean`, K=x²).
- **Smooth quadratic block** `rlctAt(∑ᵢxᵢ²) 0 = C/2` (`SumSq.lean`, `rlctAt_sumSq`, `C≥1`) + the reusable ball
  threshold `integrableOn_ball_norm_rpow_iff` (‖x‖^s integrable on a ball ⟺ `-dim < s`).
- **Payoff rewired** onto `rlctGlobal` (`DLN/RlctPayoff`, `DLN/RLCT/AoyagiCited`) via Watanabe-upper +
  Aoyagi-lower; `rlctReal` **retired**. The payoff's `#print axioms` = std-3 + those two DLN bounds ONLY (the
  ζ-continuation cite is off the value path — it enriches `(λ,m)` only).
- **Foundation validated (R9, in PR #23):** the payoff's central object now carries an in-file witness
  `rlctGlobal (sumSq C) = C/2` (`GlobalWitness`); the regular-point lemma
  `localAdmissibleExponents K x = Set.Ici 0` (`K` cont., `K x ≠ 0` — no `0≤K` needed) records "regular point
  ⟹ no pole" (`RegularPoint`); the `RLCT.Global.rlctAt = RLCT.rlctAt` `rfl` bridge closes the two-copies fork
  (`GlobalBridge`); local down-set + germ-monotonicity (`LocalMono`); the power rule
  `rlctAt (K^k) x = rlctAt K x / k` (`k≥1`, no `BddAbove`; hardens the "no second ½" trap — `PowerRule`); and
  on-cite positivity `rlctAt S.K S.x₀ > 0` + the `zetaSetupSq.K = sumSq 1` coherence (cite-free `rlctAt = 1/2`
  = cited `(rlctPair).lam` — `CiteCoherence`). Cite-free items std-3; the two on-cite items carry ONLY
  `cited_local_zeta_pole` (off the payoff path).

**REMAINS (roadmap; all off the payoff's critical path). Structured as the designed follow-on
`rlct-invariance` (PR #23 reviewer addendum; operator scope call — roadmap, not scope-creep into the close-out
PR). Deliverable = a complete invariance calculus for `rlctAt`/`rlctGlobal`, the substrate the eventual `K_B`
constant-rank bridge consumes.**

*Layer-completion — ✅ **LANDED (R9, in PR #23; see the LANDED block above)**: A (`rlctGlobal` witness),
A1 (regular-point), B1 (`rfl` bridge), B2 (down-set + germ-monotonicity), B4 (power rule), B5 (on-cite
positivity) + the coherence check. The one hardening item held back to the follow-on:*
- **Bounded-unit invariance** `0<c₁≤U≤c₂` near `x` ⟹ `rlctAt (U·K) x = rlctAt K x` (B3) — two-sided
  domination; the germ-invariance calculus proper (new substrate, not completion of what's staked). The first
  lemma the Bridge-B discharge / germ surgery reach for.

*The follow-on's analytic rungs (each a genuine build):*
- **Fubini additivity** (LR Prop 8.3(iv)) `rlctAt (K₁(x)+K₂(y)) (x₀,y₀) = rlctAt K₁ x₀ + rlctAt K₂ y₀` for
  nonnegative product germs — with `rlctAt_sumSq` it evaluates any `Σqᵢ² + core` germ; the `≥` direction is not
  AM-GM-cheap. The single most valuable next analytic theorem.
- **`rlctAt` diffeo-invariance** `rlctAt K (φ x) = rlctAt (K∘φ) x` (local C¹ diffeo, `det φ'≠0`) — BUILDABLE
  (`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` present).
- **Bridge B F1** (regional↔local unconditional, ball/box: the `hSubThreshold`/cap analytic core) + the
  **`hGlue`** reverse inequality (Prop 8.3(iii) as an equality where the payoff lives; de-risked by the witness).
- **Invariance suite tail** (two-sided-comparability · spectator · sum-of-squares-generator), the
  **normal-crossing atlas** + product pole formula, 1-D Mellin, and the cited **equivalences** (zeta-pole ↔
  threshold ↔ volume-asymptotic).

*The eventual consumer (monument-adjacent — a genuine gap, not this follow-on):*
- **Constant-rank / Morse–Bott normal form** → `rlctAt K_B (smooth fibre pt) = C/2`: v4.29 has inverse+implicit
  FT but NO constant-rank theorem / Morse lemma (verified). Once built, the payoff's cited bracket becomes a
  computation `rlctGlobal(K_B) = nReg/2 + rlct(core)` with no new analytic machinery. The payoff does not need
  it today (it rides the global cites).
- **Namespace unification** — bare-`RLCT` (`Fin n→ℝ`) vs polymorphic `RLCT.Global`; includes the `rfl` bridge
  above, and a re-check of joint cite consistency once the two `rlctAt`s become interchangeable. A safe refactor.

_The Canonical-definitions / BUILD / CITE lists below were the original plan; the LANDED list above is the
shipped state (they overlap — treat the LANDED/REMAINS split as authoritative)._

**Canonical definitions (generic, in `Core`).**
- **Value, via the integrability threshold** (Lean-friendly; the repo already has `rlctAt` / `rlctAtOn` /
  `weightedThreshold` to build on): `λ_x(K) = sup { c ≥ 0 : K^{-c} is locally integrable near x }`. Fibre value
  `λ_Z(K) = inf_{x∈Z} λ_x(K)`.
- **Full pair, via the local zeta pole** (the honest multiplicity story): `ζ_x(z) = ∫_U K^z φ`, meromorphically
  continued; `λ_x` = location of the largest pole on the negative real axis, `m_x` = its **order**. `RLCTPair K x
  = (λ_x, m_x)`. **Honesty point:** `m` is *pole order*, not a combinatorial count — so calling the DLN `θ`
  (currently `#` top-dim components, Bundle 1) a "multiplicity" requires either a theorem (count = pole order) or
  a citation. The foundation forces that boundary to be stated.
- **Ideal / sum-of-squares form:** `λ_x(f_1,…,f_s) = λ_x(Σ fᵢ²)`, with **generator invariance** (same local
  analytic ideal ⟹ same RLCT), proved for the value via two-sided comparability `C₁ Σfᵢ² ≤ Σgⱼ² ≤ C₂ Σfᵢ²`.

**BUILD (detail-at-scale — real RLCT theorems, far short of re-proving Aoyagi):** germ invariance · bounded-
positive-unit invariance · two-sided-comparability invariance (value) · smooth-prior/cutoff invariance · local-
diffeo / analytic-coordinate-change invariance · spectator-variable invariance · sum-of-squares generator
invariance · the **smooth quadratic block** `λ_0(x_1²+…+x_c²) = c/2` · monomial integrability thresholds · 1-D
Mellin continuation `∫ t^{az+b} φ(t) dt` · product normal-crossing ζ-continuation + pole formula
`λ = min_{aᵢ>0} (bᵢ+1)/aᵢ`, `m = #{ i : (bᵢ+1)/aᵢ = λ }` (denominator `2aᵢ` for squared losses) · normal-crossing
**atlas** theorem (combine finitely many chart certificates; global value = min over charts, global order = max
attaining, with the noncancellation hypotheses).

**CITE (monuments — quarantined in a small generic `Core/.../RLCT/Cited.lean`):** meromorphic continuation of
local ζ for arbitrary real-analytic loss · equivalence zeta-pole RLCT ↔ integrability-threshold RLCT ↔
volume-asymptotic RLCT · general resolution / principalization existence · general pole-order-from-resolution.
**DLN-specific cites (under `DLNFibre/DLN/RLCT`):** Aoyagi's `λ` computation · Aoyagi's `θ` / pole-order · the
Watanabe codimension upper bound (if retained as a separate inequality).

**Module split:**
```text
Core/Analysis/RLCT/{Basic, Integrability, Local, Zeta, Cited, Pair, Bridge, Witness, Global, SumSq}.lean
DLN/{RlctPayoff, RlctPayoffGeneral}.lean · DLN/RLCT/{AoyagiCited, BundleShiftDischarge}.lean   -- shipped
```
**Honest payoff reading (the boundary, now realized):** *defined* `rlctGlobal` (Def 8.1(i), cite-free);
*defined* `K_B(A) = ‖A_N…A_1 − B‖_F²`; *proved* `Z_B = K_B^{-1}(0) = mult^{-1}(B)`; *proved* `codim_ℝ(Z_B)` =
the Core algebraic codimension; *cited* Watanabe-upper + Aoyagi-lower: `rlctGlobal(K_B) = codim_ℝ(Z_B)/2`;
*therefore* the L&R/Aoyagi `rlct = C/2`. The opaque assumed map is gone; those two DLN bounds are the only
value-path cites (the ζ-continuation monument enriches `(λ,m)` only, off the value path).

**Caveat — domain risk:** this is real-analysis (ζ, Mellin, integrability, meromorphic continuation), unlike the
algebraic-geometry work so far; **Mathlib analysis coverage is the unknown.** Pick this up **recon-first** (map
coverage + lock the build-vs-cite boundary), and scope the first slice tight — the **value-only integrability
threshold + the core invariances + the quadratic block `λ=c/2` + axiom retirement** is the headline honesty win;
defer the zeta-pole *multiplicity* and the full normal-crossing *atlas* (where the analysis monuments cluster).
Connects to the existing `rlct-runway-target` note (kill-condition: a singular-locus lower bound — the smooth
locus alone gives only an upper bound).

## Dependency sketch

```
  Bundle 1 (combinatorial core) ──┐
                                  ├─► (C, θ) value ──► Bundle 4 (rlct = C/2, cited analytic bound)
  Bundle 2 (quiver / orbit)    ───┘        ▲
                                           │
  Bundle 3 (topology) ─────────► permutation invariance (sharpens / cross-checks (C, θ))
```

## Process / harness uplift (cross-cutting — not a math bundle)

These are **expedition-infrastructure** debts that tax every Lean expedition, distinct from the math
bundles above. The operational fix lands in [`docs/policies/expedition.md`](docs/policies/expedition.md)
§Isolation (+ a helper script / worktree hook); this section tracks the intent and the acceptance bar.
Both surfaced concretely while standing up the `explicit-ctheta` expedition (2026-06-22): a fresh
worktree cost a full `cache get` + from-scratch `DLNFibre` build, and the controller could not get true
teammate isolation because it was itself in a worktree.

### Uplift A — share the Lean dependency cache across worktrees
**Plainly.** A fresh `git worktree add` checkout has no `.lake`, so making it buildable runs
`lake exe cache get` (fetch Mathlib + decompress ~8000 oleans, minutes) **and** rebuilds `DLNFibre`'s
own oleans from scratch — per worktree. With ~20 live worktrees this repeated tax is why expeditions
have defaulted to "share the controller's one built worktree" instead of true per-teammate isolation.
`expedition.md` §Isolation already states the principle ("reuse/symlink `.lake/packages` across
worktrees"); it is **not operationalised**. **Uplift:** a worktree-creation helper (script or hook)
that symlinks the shared `.lake/packages` (Mathlib + deps, read-only at build time) into each new
worktree, so only the project's own small oleans rebuild — making worktree-per-teammate near-free.
**Decide:** the canonical location of the shared `.lake/packages`; symlink vs hardlink; confirm safety
under concurrent reads. **Acceptance:** a new worktree is `lake build`-green in seconds, no
per-worktree Mathlib fetch/decompress.

### Uplift B — only a main-checkout controller can give teammates isolated worktrees
**Plainly.** The harness exposes exactly one isolation lever — `isolation: worktree` — and **no
per-spawn cwd override**. That lever yields *distinct per-teammate* worktrees **only when the controller
runs from the main checkout**. When the controller is **itself in a worktree**, spawned
`isolation: worktree` teammates **collapse onto the controller's worktree** (all share one), so they
must run **serially** — one editor at a time — to avoid clobbering each other. The main checkout is
therefore a *single* resource: **at most one controller** can use it to get truly-parallel isolated
teammates; every other controller must run from a worktree and gets only serial teammates. (A
controller legitimately living in the main checkout — e.g. by an expedition's design — is correct, not
a squat; it just means that slot is taken.)

**Is the collapse actually a problem?** Often not. For a **sequential** expedition (a rung-ladder where
teammates run one after another anyway), serial teammates in one shared worktree are fine — the
centralized merge stays clean and Uplift A keeps each build cheap. The genuine loss is only for
**wide parallel fan-out** (many independent finders / reviewers / tides at once): a worktree-based
controller cannot parallelize those, while a main-checkout controller can.

**Options to evaluate:** (i) **accept + schedule** — reserve the main checkout for whichever expedition
most needs parallel fan-out; run other controllers from worktrees on sequential work (serial teammates,
cheap builds). (ii) **a manual workaround to verify** — a worktree-controller pre-creates per-teammate
worktrees (`git worktree add`) and has each teammate `EnterWorktree(path)` into its own (the harness
does let a pinned-cwd agent switch into an existing worktree); feasibility hinges on teammates having
that tool and the controller still being able to merge from those trees — **untested**. (iii) a harness
change making teammate isolation produce genuine nested worktrees from a worktree-based controller.

**Tie-in (corrected):** Uplift A removes the *build-cost* reason isolation was avoided, but it does
**not** dissolve B — B is a **topology** limit, not a cost one. A makes the *serial* collapse case
cheap; it does not grant a worktree-controller parallel teammates. **Acceptance:** a controller that is
not on the main checkout can still run teammates in genuinely isolated, parallel worktrees (via (ii) or
(iii)).

## fibration-geometry expedition (closed 2026-06-27) — status + residuals

**Landed (all bedrock: green, sorry-free, axiom-clean, hardener-cleared).** The DLN reduced fibre
family over the rank-`= r` open is, **chartwise over the in-chart Schur ring `SchurLoc`**, an honest
over-base local product with flatness:

- **S1** `FibreRankBridge.mem_rankROpen_iff_rank_universalMatrixResidue_eq` — `rankROpen` IS the
  residue-field rank-`= r` locus (set-of-primes identity).
- **S2 / S2c** `FibreSmoothBlock` / `FibreSmoothBlockExists` — the smooth-block certificate (Kähler `Ω`
  free, `rank(Ω) + codim = ambient`), hypothesis-free under the Kostant gate
  (`exists_topComponent_smoothBlock_certificate`; generic engine `topDimMinPrimes_nonempty`). The
  RLCT-runway upper-bound local model.
- **S3** `FibreFlatness` — cheap-flatness verdict + localization/standard-model/`UniversallyOpen` facts.
- **S4 / S4b** `FibreLocallyTrivial` / `FibreOverBaseTriv` — the `SchurLoc`-linear (over-base)
  trivialization `Away(chartDsigAt) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing` (over the honest
  structure map, non-circular) + chartwise flatness over `SchurLoc`.
- **S5** `FibreBundleHeadline` — the capstone `reducedFibre_existsOverBaseProductChartAt_rankEq`.

Exposition: `expeditions/2026-06-27-fibration-geometry/expositions/fibration-geometry.md`.

**Residuals (roadmap; sequence as listed — items 1–4 are genuinely reachable; item 5 is the genuine
wall, the next expedition):**

1. **Projection compatibility** — that the in-chart structure map
   `schurToDsigAt : SchurLoc → Away(chartDsigAt s t)` is the pullback of `mult`'s projection from the
   target/base rank-chart. (`SchurLoc` is the in-chart base direction; `Away(chartDsigAt s t)` is the
   *source/total* chart, already `≅ SchurLoc ⊗ fibre` — so this is NOT a "`SchurLoc ≅ sweepSigmaRing|chart`"
   bridge, which would lose the fibre.) This compatibility is what lets the chartwise `SchurLoc`-flatness
   read as genuine fibre-family flatness over the base. A real build, **ahead of** R1.
2. **R1 — `targetOverlapTransition`** (the overlap-gluing cocycle). Assembles the per-chart data into a
   single global `Flat π` / fibre-bundle morphism over all of `rankROpen`. After projection compatibility.
3. **S2b — conormal companion** `I/I²` free of rank `= codim` (the RLCT-relevant dual of S2's Kähler
   side; conormal exact sequence + rank additivity). A real build.
4. **S1 in-file non-vacuity `example`** (a concrete `P ∈ rankROpen` in the achievable regime) — a
   bedrock-hygiene nicety.
5. **Singular-locus split / RLCT lower bound** (→ the next expedition): the smooth-block gives only the
   `rlct ≤ ½·codim` upper-bound local model; the equality needs a singular-locus lower bound
   (`rlct ≥ ½·codim` everywhere). This is the wall the `rlct = ½·codim` Cited axiom rests on; teed up,
   not closed.

## Open edges — headline results not yet fully general (relative to L&R)

The [formalisation-status table](README.md#formalisation-status) marks **one** row short of the paper's full
generality (field generality, Gap 2). Gap 1 (below) is now **closed**. What remains:

### Gap 1 — geometric `θ` for the fibre `mult⁻¹(B)` at non-monotone `d` — ✅ **CLOSED** (expedition `rlct-foundation`, 2026-07-06)
- **Was:** `#comp(mult⁻¹(B)) = cTheta(d−r)` proved **only for `Monotone d`**
  (`ncard_topDimMinPrimes_fibre_eq_cTheta_dminus`, via the sorted Schur/localization chart).
- **Now (arbitrary `d`):** `Core.FibreThetaCountUnconditional.ncard_topDimMinPrimes_fibre_eq_numTop`
  (+`_of_rank`) — the fibre top-dim component count `= numTop d r` for arbitrary `d`; and the closed form
  `Core.CThetaSortClosedForm` → `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort` (+`_of_rank`)
  `= cTheta((d∘Tuple.sort d) − r)`. The **only** added hypothesis is the rank-feasibility `hr : ∀ i, r ≤ d i`
  (disclosed); `Monotone d` is **gone**. Under `Monotone d` the sort recovers the old `cTheta(d−r)` headline.
  Non-vacuity: witnesses on the non-monotone `d = ![1,2,1]` (`decide`, over `AlgebraicClosure ℚ`) — a vector
  unstatable under the old gate. The *rank-locus* count `#comp(Σ̄ʳ) = numTop d r` was already arbitrary-`d`
  (`numTop_eq_ncard_topComponents`).
- **Route (as this section predicted):** the Monotone-free `numTop_comp_sort` reroute + the already-landed
  perm-invariance (no new cite; the anticipated *geometric* fibration transfer was **not** needed —
  perm-invariance sufficed once the count chain was traced to be `Monotone`-free but for one cosmetic E0 step).
  `[IsAlgClosed]` + `Type 0` remain — those are Gap 2, not this gap.

### Gap 2 — field generality (an *unrealized* generality, not a mathematical restriction)
The algebraic theorems carry `[CharZero] [Infinite]` (codim), plus `[IsAlgClosed]` + universe `Type 0`
(counts); L&R state everything over an arbitrary field and **prove that generality on purpose**
(`thm:base_field` §3.4 + Voigt's lemma: orbit reps are 0/1 partial-permutation matrices over the prime
field, every orbit is `G/H` for split-connected `G = ∏ GLᵈⁱ`, hence geometrically irreducible;
`codim(O_M) = dim Ext¹` with the Ext-dims combinatorial). So `C`, `θ` are field-independent — each Lean
hypothesis is a **proof-route artifact**, not a truth condition. The codim theorems **already hold over any
char-0 infinite field** (ℚ, ℝ, ℚ_p); the remaining pieces, by value/cost:
- **(a) Counts over non-closed char-0 fields (ℝ, ℚ)** — `thm:base_field` is the tool: prove over `k̄`,
  transport by the split-orbit-closure geometric-irreducibility bijection. Needs absolute irreducibility of
  `orbitRankLocus` + a base-change bijection of top-dim minimal primes. Expedition-scale but bounded;
  removes `[IsAlgClosed]` for counts.
- **(b) Positive characteristic (drop `[CharZero]`)** — reprove `codim(O_M) = dim Ext¹` char-free via
  `dim(orbit) = dim G − dim Stab`, `Stab = Aut(M) =` unit group of `End(M)` (smooth in every char) + the
  Euler form; localized to the Voigt layer, medium effort. Gives char-`p` infinite fields.
- **(c) Finite fields (drop `[Infinite]`)** — `[Infinite]` is baked into the *definition*
  `codimRepCanonical = height(vanishingIdeal(coord '' Z))` (wrong object over finite `k`); needs a
  scheme-theoretic redefinition + re-proving every codim theorem. Largest lift.
Orthogonal to the DLN payoff (over ℝ/ℂ) → low priority.

### Gaps 3–4 (minor)
- **Explicit-formula syntactic shape:** `cValue` is proved `= codim`, not rendered in thm:main-codim's exact
  `(m/2){S̃/m}(1−{S̃/m}) − …` fractional-part form. Semantically equivalent; the `θ` binomial is verbatim.
- **Gabriel finiteness:** the orbit ↔ Kostant bijection is proved; "finitely many orbits" is not stated as a
  `Finite`/`Fintype` theorem (implicit — the index `kostantPartitions` is a `Finset` by construction).

## Convention

Pick up a **bundle** only when it is whole-in-reach — don't nibble it one lemma at a time. **Reachable-now
sharpenings** of landed work may be done anytime. Mark every result Proved / Assumed / Cited / Deferred
([`docs/policies/precision.md`](docs/policies/precision.md)); the `rlct = ½·codim` reading is **Cited** until
(if ever) the analytic bound is itself formalised. Update this file at each expedition close.
