# Roadmap — formalising the geometry of DLN multiplication fibres

The programme-level map: the destination, the bundles of work toward it, and what each depends on. Written
to be elementary; pick up a **bundle** only when it is *whole-in-reach*, rather than nibbling one lemma at a
time. This is a **first cut**; the `core-quiver-engine` expedition sharpens the ladder and, via an opening recon,
resolves the load-bearing unknown (what Mathlib already provides). Update at each expedition close.

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

## Top open question (resolve first)

**What does Mathlib already provide?** Quiver representations, the type-A / `A_n` story, Gabriel's theorem,
`Ext` for quiver reps / representations of a category, equivariant cohomology. The answer decides how much of
the engine is *reuse* vs *build-from-scratch* — and the build-from-scratch part *is* the reusable asset, so
getting its API right is high-value. **The `core-quiver-engine` expedition's opening recon resolves this.**
Until it lands, the reachability tags below are estimates.

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

**Next: the θ / top-component side (expedition `theta-components`, 2026-06-25).** Resolve the order θ and the
rest of Lemma 4.6 (full bundle, scope B) — see `expeditions/2026-06-25-theta-components/brief.md`. Key open
finding: Aoyagi's order `θ = a(ℓ−a)+1` and the LR/Lean component-count `θ = C(m,|δ|)` **diverge for `|δ| ≥ 2`**
(smallest witness `(2,2,2,2,2)`, r=0: 5 vs 6) — agreeing only for `|δ| ≤ 1` (hence `(3,3,3)` = 2). Design goal:
the full local-trivial bundle `mult⁻¹(B) → Mat^{=r}` should consolidate codim + θ + smoothness and may retire
the codim hand-built trivialization (promoting `e` to a genuine bundle chart, climbing the reducedness wall the
codim expedition routed around).

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

## Convention

Pick up a **bundle** only when it is whole-in-reach — don't nibble it one lemma at a time. **Reachable-now
sharpenings** of landed work may be done anytime. Mark every result Proved / Assumed / Cited / Deferred
([`docs/policies/precision.md`](docs/policies/precision.md)); the `rlct = ½·codim` reading is **Cited** until
(if ever) the analytic bound is itself formalised. Update this file at each expedition close.
