---
title: "Setup — the multiplication map and its fibres"
status: draft
source: paper-note
topics: [setup, matrix-tuples, quiver-representations]
created: "2026-06-12T18:00:00+00:00"
updated: "2026-06-12T18:00:00+00:00"
---

# Setup — the multiplication map and its fibres

**Stub.** The first expedition (`expeditions/2026-06-12-paper-digest/`) fleshes this into the
formalisation-ready substrate. For the full reader-facing map see
[`../docs/expositions/paper-digest/high-level-overview.md`](../docs/expositions/paper-digest/high-level-overview.md);
the primary source is `../paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex`.

## The core objects

Fix a dimension vector $\underline d=(d_0,d_1,\dots,d_N)$. The ambient space is the set of composable
matrix tuples

$$
\operatorname{Rep}_{\underline d}=\prod_{i=1}^N \operatorname{Mat}_{d_i,d_{i-1}}(k),
$$

with the **multiplication map**

$$
\operatorname{mult}:\operatorname{Rep}_{\underline d}\to\operatorname{Mat}_{d_N,d_0},
\qquad (A_1,\dots,A_N)\mapsto A_N A_{N-1}\cdots A_1 .
$$

The objects of interest are the **rank-$r$ product locus**
$\Sigma^r_{\underline d}=\{A_\ast:\operatorname{rank}(\operatorname{mult}(A_\ast))=r\}$ (and its closure),
the **zero-product locus** $\Sigma^0_{\underline d}$, and the **fibres**
$\operatorname{mult}^{-1}(B)$. The invariants are the codimension $C$ of the top-dimensional components
and their number $\theta$.

## The two layers (mirrors the Lean `Core` / `DLN` split)

- **Engine (network-free).** Everything about $\operatorname{Rep}_{\underline d}$, $\operatorname{mult}$,
  the rank loci and fibres, and the type-A quiver translation that computes $(C,\theta)$.
- **Application (DLN).** The square-Frobenius loss $K^{\mathrm{DLN}}_B(A_\ast)=\lVert\operatorname{mult}(A_\ast)-B\rVert_2^2$,
  whose zero-set is exactly $\operatorname{mult}^{-1}(B)$, and the RLCT payoff $\operatorname{rlct}=C/2$.

## To be filled by the first expedition

- the type-A quiver translation (orbits ↔ Kostant partitions ↔ rank patterns) at formalisation grain;
- the precise statements of the reductions (§4) and the three $(C,\theta)$ computations (§§5–7);
- the Mathlib-coverage map that decides what is reuse vs build-from-scratch.
