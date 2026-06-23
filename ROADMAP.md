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
   rlct(K^DLN_B) = C/2   (§8, Thm 8.6;  uses the cited rlct ≤ ½·codim bound, Aoyagi/Watanabe)
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

### Uplift B — controller-in-worktree collapses teammate isolation
**Plainly.** Per `expedition.md` §Isolation, if the controller runs from a worktree (not the main
checkout), spawned `isolation: worktree` teammates **collapse onto the controller's worktree** —
isolation becomes nominal and the team must run **serially** (one editor at a time). The natural
"controller home" is the main checkout, but it is frequently occupied (e.g. the live `aoyagi-full`
mega-expedition currently squats the main checkout, partly from a crash) — so concurrent expeditions
cannot each get a clean isolated controller home. **Uplift options to evaluate:** (i) a convention
that every expedition controller gets its **own dedicated checkout** (never the shared main checkout),
with isolation working from there; (ii) make teammate isolation robust to a worktree-based controller
(genuine nested per-teammate worktrees); (iii) a discipline that the main checkout stays a **free
controller home on `dev`** and no expedition squats it (the crash that parked aoyagi there is the
anti-pattern to prevent). **Tie-in:** once Uplift A makes worktrees near-free, giving every controller
its own checkout (option i) is cheap and dissolves most of B. **Acceptance:** two concurrent
expeditions each run teammates in genuinely isolated worktrees with parallelism intact.

## Convention

Pick up a **bundle** only when it is whole-in-reach — don't nibble it one lemma at a time. **Reachable-now
sharpenings** of landed work may be done anytime. Mark every result Proved / Assumed / Cited / Deferred
([`docs/policies/precision.md`](docs/policies/precision.md)); the `rlct = ½·codim` reading is **Cited** until
(if ever) the analytic bound is itself formalised. Update this file at each expedition close.
