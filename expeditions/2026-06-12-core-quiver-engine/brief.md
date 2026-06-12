# Expedition brief — core-quiver-engine

## Central question

Build the foundational layer of the **network-free quiver engine** `DLNFibre.Core` in Lean: the ambient
objects ($\operatorname{Rep}_{\underline d}$, $\operatorname{mult}$, the product-rank loci) and the spine
correspondence **orbits ↔ Kostant partitions ↔ rank patterns** (paper §§2–3) that every downstream
codimension result stands on — to a green, sorry-free, axiom-clean, reviewer-audited slice with statement
cards.

Scope: this is `DLNFibre.Core` work (network-free). The `DLN` application and the RLCT cap are **out of
scope** here. Reader-facing paper *digestion* is the operator's own activity (`docs/expositions/`), **not** a
deliverable of this expedition — threads read the paper's §§2–3 as **primary source** only to pin the exact
statements to formalise.

## Why this chunk

The orbit ↔ Kostant ↔ rank-pattern correspondence is the spine: the `Ext` codimension (Cor 3.5), the
reductions (§4), and the three $(C,\theta)$ computations (§§5–7) all read off it. Getting it onto bedrock —
exact definitions, the inclusion-exclusion inversion as a *characterisation*, non-vacuity witnesses — is the
foundation the rest of the engine rises over.

## The load-bearing unknown (resolve first, as recon)

What does Mathlib provide for **quiver representations**, the **type-A / $A_n$** indecomposables, **Gabriel's
theorem**, and **`Ext`** of representations? This decides what is reuse vs build-from-scratch — and the
build-from-scratch part *is* the reusable asset, so its API matters. A `scout` reconnaissance thread answers
this in the opening tick. It is recon, not a digest.

## Rungs (controller sequences after recon; ambitious but bedrock-first)

1. **Ambient objects.** `Rep_d` (tuples of composable matrices over a field), `mult`, the product-rank loci
   $\Sigma^r$ / fibres $\operatorname{mult}^{-1}(B)$ as Lean defs. Pure setup; reachable now.
2. **Rank patterns + Kostant partitions as data.** The arrays $r_{ij}$ (ranks of composites) and $m_{ij}$
   (interval-module multiplicities); the Kostant-partition compatibility predicate ($d_k=\sum_{i\le k\le j}m_{ij}$).
3. **Prop 3.1 — the inclusion-exclusion correspondence.**
   $m_{ij}=r_{ij}-r_{i,j+1}-r_{i-1,j}+r_{i-1,j+1}$ and its inverse $r_{ij}=\sum_{k\le i\le j\le l}m_{kl}$,
   as a **characterisation** (a bijection between the two encodings). Pure combinatorics / linear algebra —
   the most reachable real theorem and the likely first statement-carded result.
4. **Orbits ↔ Kostant (Cor 2.9 via Gabriel, Thm 2.5).** The representation-theoretic identification. Depends
   on the recon; may be build-from-scratch for type-A Gabriel. Name what is **Proved** vs **Cited**.

Rungs 1–3 are the **bedrock target**; rung 4 is the ambitious reach (land it if whole-in-reach, else hand a
sharp successor to the next expedition). The `Ext` codimension (Cor 3.5) is explicitly the **next** expedition.

## Closing criterion

1. A green, sorry-free, axiom-clean `DLNFibre.Core` slice with rungs 1–3 landed, each **statement-carded**
   (Proved / Assumed / Cited / Deferred) and reviewer-audited for fidelity to the paper's statements.
2. A **Mathlib-coverage map** (reuse vs build) for the quiver / representation layer, in `synthesis.md` and
   folded into `ROADMAP.md`.
3. A named, justified **next rung** (orbits ↔ Kostant if not landed, else the `Ext` codimension).

## Pointers

- Disposition + process: `../../CLAUDE.md`, `../../docs/policies/expedition.md`. **Read `../../lean/CLAUDE.md`
  before any Lean** (the Core/DLN split, build, v4.29 Mathlib notes).
- Library shape + ladder: `../../ROADMAP.md` (Bundles 1–2), `../../theory/setup.md`.
- Paper §§2–3 (primary source): `../../paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex`.
