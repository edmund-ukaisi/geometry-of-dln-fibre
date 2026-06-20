# Expedition brief — voigt-discharge

**Branch:** `expedition/voigt-discharge` (worktree `.claude/worktrees/voigt-discharge`), off `dev` (`9e99e01`).
**Mandate (operator, 2026-06-18):** drive to the end as **one expedition**, **zero new cited interfaces**.
If Mathlib lacks a foundation, **build it as far as needed** to fully discharge the hypothesis. Controller
holds discipline + ambition throughout; seat-bounded teammates, stood down at close.

## Central question

Discharge **`hVoigt`** to unconditional bedrock. Concretely, prove (currently an assumed hypothesis in
`Core.OrbitCodim`):

> `codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`

i.e. the **geometric** codimation (`Ideal.height` of the vanishing ideal of the orbit-rank-locus, read through
the canonical linear flattening) equals the **tangent** codimation `orbitLinearCodim M = dim Ext¹(M,M)` (already
**Proved**, `Core.OrbitLinearCodim`). Then `codimRep_orbitRankLocus_eq_multSum` becomes unconditional, and the
geometric codimation of the rank loci is honest Lean.

## The route — tangent space + smoothness (NOT classical determinantal)

The rank loci are rank conditions on **products** `A_j···A_{i+1}` (variety-of-complexes / quiver-loci), so the
classical generic-matrix determinantal-height theorem does **not** apply. The clean route, which avoids both
classical determinantal **and** the full algebraic-group orbit-stabilizer theory:

The deformation complex is **2-term** (`Ext¹ = coker δ⁰`, tangent-to-orbit `= im δ⁰`), so
`orbitLinearCodim = finrank C¹ − finrank (range δ⁰) = dim Rep − dim(tangent to orbit)` — the **algebra side is
done**. `hVoigt` reduces to the AG bridge:

1. **orbit-rank-locus is irreducible** (closure of `G_d · M`; `G_d` = product of `GL`'s is irreducible).
2. **`M` is a smooth point**, Zariski tangent space `= im δ⁰` (homogeneity: `G_d` acts transitively, smooth
   locus is dense + `G`-stable ⇒ smooth everywhere; tangent = image of the orbit-map differential, concrete).
3. **smooth point ⇒ local dim = tangent dim** (regularity).
4. **`height(I(Z)) = dim Rep − dim Z`** for the irreducible `Z` (dimension formula / catenary in
   `MvPolynomial (RepCoord d) k`).

Combine: `codim = dim C¹ − dim(im δ⁰) = dim coker δ⁰ = dim Ext¹`. ∎

Open sub-question for the recon: is `orbitRankLocus` **defined as** the orbit closure, or as the rank locus
with `orbitRankLocus = orbit closure` (Thm 3.8) currently **Cited**? If the latter, that identification is part
of the zero-cited target too. Also pin the **field hypotheses** the discharge needs (algebraically closed?
char 0 for generic smoothness?) and confirm they are compatible with how `codimRep`/`hVoigt` are stated.

## Opening move — Mathlib recon (thread 01)

A single `scout` maps Mathlib coverage for the four AG/commutative-algebra pillars, returns the **build ladder**
(present vs must-build, in dependency order, with size reads), pins the field hypotheses, and confirms the
tangent/smoothness chain at the Lean level against our existing defs. Decorrelated Codex. Then the controller
structures the build in layers.

## Closing criterion

`hVoigt` discharged: `codimRep_orbitRankLocus_eq_multSum` (and the canonical-coord headline) hold
**unconditionally** (no `hVoigt` hypothesis), whole library green, `scripts/sorries` 0/0/0/0, axiom-clean,
**zero new cited interfaces** (field hypotheses like `[IsAlgClosed k]` are hypotheses, not citations). Any
Mathlib infrastructure built along the way stated at full generality where natural. Synthesis + statement
cards + ROADMAP update at close.
