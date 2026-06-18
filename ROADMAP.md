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
**Remaining in Bundle 1 (future expeditions):** the QIP (Thm 6.1), the explicit lattice-point formula
(Thm 7.10), and the §4 rank-$r$→rank-$0$ / fibre-codim reductions.

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
and **orbits ↔ Kostant (Cor 2.9)** as `Core.OrbitKostant.orbitKostantEquiv`. **Remaining (future):** the
orbit-closure order (Thm 3.8) and the $\operatorname{Ext}(M,M)$ codimension (Cor 3.5).

### Bundle 3 — the topology  ·  `DLNFibre.Core` (Poincaré)
**Plainly.** The Poincaré series in equivariant cohomology (Thm 5.5) and the permutation invariance it yields
(Cor 5.10). **Reachability:** the heaviest; equivariant-cohomology machinery may be absent in Mathlib. A
likely **cited** layer, with permutation invariance possibly reachable by an independent combinatorial route
from Bundle 1 — to be probed.

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
