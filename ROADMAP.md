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
**Remaining in Bundle 1 (future):** **permutation invariance (Cor 5.10) — a genuine lift, NOT free.**
`cValue`/`cTheta` read $\underline d$ through order-sensitive prefix sums and the closed form requires
`Monotone d`; relating $\underline d$ to its sorted form needs either a sort-normalisation bridge or the
paper's **Poincaré-series route (Bundle 3)**. Also the §4 fibre-codim reduction (Lemma 4.6). The
**per-orbit** geometric reading (`codimForm` = geometric codimension of the orbit closure $\bar O_M$) is now
**Proved** (Bundle 2 / expedition `voigt-discharge`); the **aggregate** reading
"$C=\operatorname{codim}\Sigma^r$" (over the whole rank-$r$ locus $\Sigma^r$) stays open — it needs
$\Sigma^r$-as-variety and its orbit stratification, not `hVoigt`. The combinatorial $(C,\theta)$ does not
depend on either.

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
**Remaining (future): the $\Sigma^r$-aggregate reading** — `numTop` as the number of top-dimensional
**geometric** components of the *whole* rank-$r$ locus $\Sigma^r$ — needs a geometric definition of $\Sigma^r$,
its orbit stratification, and a component-count, none of which depend on `hVoigt`.

### Bundle 3 — the topology  ·  `DLNFibre.Core` (Poincaré)
**Plainly.** The Poincaré series in equivariant cohomology (Thm 5.5) and the permutation invariance it yields
(Cor 5.10). **Reachability:** the heaviest; equivariant-cohomology machinery may be absent in Mathlib. A
likely **cited** layer, with permutation invariance possibly reachable by an independent combinatorial route
from Bundle 1.

**Permutation invariance (Cor 5.10) — the open lift, scoped (`c-theta` close, 2026-06-18).** $(C,\theta)$
depend only on the multiset $\{d_0,\dots,d_N\}$, not the order. We did **not** prove this: the landed
$(C,\theta)$ (Bundle 1) read $\underline d$ through order-sensitive prefix sums ($m,S,a,\delta$) and the QIP /
closed-form equalities (`cCodim_eq_qipMin`, `qipMin_eq_cValue`) require `Monotone d`; a permuted $\underline d$
is non-monotone and falls outside them, and `cCodim`/`codimForm`/`kostantPartitions` carry **no manifest
permutation symmetry** and **no sort-normalisation bridge**. Two routes, cheapest first:
1. **Combinatorial-bridge recon (do this first).** Probe whether $\min_{\text{Kostant}(\underline d)}$ of the
   quadratic form is permutation-invariant by an *elementary* argument — a bijection on Kostant partitions
   under transposition of adjacent $d_i$, or a `cCodim d = cCodim (sort d)` normalisation lemma. If it exists,
   Cor 5.10 is a **contained Lean tide** (a scout/pen-and-paper recon scopes it; θ needs the same bridge plus a
   `numTop d 0 = qipNumMinimisers` link, not yet built). The paper did **not** take this route, so its
   existence is itself an open question.
2. **Poincaré series (Thm 5.5), the paper's route.** Equivariant cohomology of the strata; the series is
   manifestly symmetric in $\underline d$, so invariance falls out of its shape. Heavy, Mathlib-absent — if
   route 1 fails, Cor 5.10 stays **Cited** to this argument, named as such.

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

## Convention

Pick up a **bundle** only when it is whole-in-reach — don't nibble it one lemma at a time. **Reachable-now
sharpenings** of landed work may be done anytime. Mark every result Proved / Assumed / Cited / Deferred
([`docs/policies/precision.md`](docs/policies/precision.md)); the `rlct = ½·codim` reading is **Cited** until
(if ever) the analytic bound is itself formalised. Update this file at each expedition close.
