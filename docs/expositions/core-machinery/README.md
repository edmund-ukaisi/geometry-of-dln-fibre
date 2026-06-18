---
title: "The Core Machinery: the Type-A Quiver Classification"
status: draft
source: exposition
topics: [core-machinery, index, quiver-representations, orbit-classification]
created: "2026-06-14"
updated: "2026-06-14"
---

# The Core Machinery: the Type-A Quiver Classification

This part is a self-contained, graduate-level development of the classification
that underlies the paper *Geometry of the fibers of the multiplication map of
deep linear neural networks* (Lehalleur–Rimányi 2024). It treats Sections 2–3 of
the paper as the first chapters of a textbook: the question is how a chain of
matrices composes, and the answer is a finite combinatorial classification of the
chains up to change of basis. The reader is assumed mathematically mature but not
assumed to know quiver representations, Gabriel's theorem, or singular learning
theory; each is built up locally.

This is the **network-free engine**. It mentions deep linear networks only as
motivation; the loss function and the real-log-canonical-threshold payoff belong
to a later, application-specific part and are not used here.

## The chapters

1. **[Composable matrix tuples and the multiplication map](01-tuples-and-the-multiplication-map.md)** —
   the objects: the space $\operatorname{Rep}_{\underline d}$ of composable
   tuples, the multiplication map, and the product-rank loci and fibers whose
   geometry is the goal.
2. **[Quiver representations and the base-change group](02-quiver-representations-and-the-base-change-group.md)** —
   a tuple is a representation of the quiver $0 \to 1 \to \cdots \to N$; the
   base-change group $G_{\underline d}$ acts, its orbits are the isomorphism
   classes, and the interval ranks are constant on them.
3. **[Gabriel's theorem: interval modules and the barcode](03-gabriels-theorem-interval-modules-and-the-barcode.md)** —
   every tuple is a direct sum of interval modules, recorded as a barcode; this
   makes the orbit set finite.
4. **[Rank patterns and Kostant partitions](04-rank-patterns-and-kostant-partitions.md)** —
   two records of a barcode and the inclusion–exclusion (Proposition 3.1) that
   converts between them; uniqueness of the Gabriel decomposition follows.
5. **[The classification: orbits and Kostant partitions](05-the-classification-orbits-and-kostant-partitions.md)** —
   the rank pattern is a complete invariant, so orbits, isomorphism classes,
   realizable rank patterns, and Kostant partitions of $\underline d$ are one
   finite set (Corollary 2.9).

A single running example, the dimension vector $(2,2,2)$, is carried through:
its zero-product locus, its barcode, its rank pattern, and finally its six orbits
and three irreducible components.

## Formalisation

The central definitions and results of every chapter are formalised in Lean 4 +
Mathlib, in the library `DLNFibre.Core`, sorry-free and axiom-clean. The chapters
point to the specific declarations in collapsible "Formalised in Lean" notes, at
central definitions and results only. The map from chapter to module:

| Chapter | Lean module(s) |
|:---|:---|
| 1 | `Core.Setup`, `Core.Submult` |
| 2 | `Core.BaseChange` |
| 3 | `Core.IntervalModule`, `Core.Barcode`, `Core.Gabriel` |
| 4 | `Core.RankPattern`, `Core.Gabriel`, `Core.IntervalModule` |
| 5 | `Core.Orbit`, `Core.OrbitKostant` |

What is **not** formalised, and is cited to the paper where used: the
orbit-closure order (Theorem 3.8), the $\operatorname{Ext}(M,M)$ codimension
(Corollary 3.5), the three computations of $(C, \theta)$ (Sections 5–7), and the
RLCT identity (Theorem 8.6). These build on the classification developed here and
are the subject of later work; see [`ROADMAP.md`](../../../ROADMAP.md).

## Sources

The paper source is at
`paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`, and a map of the
whole paper — including the parts beyond this engine — is the
[high-level overview](../paper-digest/high-level-overview.md).
