# Expedition brief — ext-codimension

**Branch:** `expedition/ext-codimension` (worktree `.claude/worktrees/ext-codimension`), stacked on
`expedition/core-quiver-engine`. The exposition review runs in parallel on the main checkout; this
expedition touches `DLNFibre.*` Lean, not `docs/expositions/`.

## Central question

Formalise, in honest Lean, the **codimension $C$** of the orbit closures / product-rank loci of the
multiplication map — i.e. Lehalleur–Rimányi (2024) Corollary 3.5 (the $\operatorname{Ext}(M,M)$
normal-slice codimension) and what it rests on — by **building the standard algebraic and
algebro-geometric machinery on top of Mathlib and raising it until our case is a corollary.** Ambition
and correctness over economy: develop the well-established mathematics (modules over the path algebra,
$\operatorname{Hom}/\operatorname{Ext}$, the Euler form; the representation variety, orbit dimension,
tangent spaces, Voigt) — not a bespoke shortcut.

The target submerged: the geometric codimension $C$ of the orbit closures in $\operatorname{Rep}_{\underline
d}$ is proved equal to the combinatorial $\operatorname{Ext}^1$ formula, with every step a standard
mathematical development. (The number $\theta$ and the closure order Thm 3.8 ride along where natural.)

## Steering discipline (controller)

- **Well-established mathematics is the hardened standard.** The controller makes the calls on where and
  how the sea rises, judging each layer against: *is this the textbook development of this object?* A
  bespoke, non-standard construction is the analogue of an ugly theorem — information that we are off the
  path.
- **`/local-codex-consult` fired regularly** on the standardness question: is this the way the
  mathematics is actually developed; are we building on the right Mathlib foundations; is the
  generality the natural one.
- Mark every result **Proved / Assumed / Cited / Deferred**. Aim: Proved, by standard development. A
  Cited interface is acceptable only where the standard mathematics genuinely sits outside reach and is
  named as such.

## Scope

- **In:** equioriented type $A$ (hereditary), modules over the path algebra $kQ$; $\operatorname{Hom}$,
  $\operatorname{Ext}^1$; the Euler/Ringel form; $\operatorname{Ext}^1$ between interval modules; the
  representation variety, $G_{\underline d}$-orbit dimension, tangent space, Voigt's
  $\operatorname{codim}\mathcal O_M = \dim\operatorname{Ext}^1(M,M)$; Cor 3.5; and (where natural) the
  orbit-closure order (Thm 3.8).
- **Out:** full ADE Gabriel; non-equioriented orientations; the $(C,\theta)$ *computations* (Poincaré /
  QIP / lattice-point, §§5–7) and the RLCT payoff (§8) — later bundles.

## Architecture: two views, one bridge (not a rebuild)

`Tuple d` **is** the representation variety $\operatorname{Rep}(Q,\underline d) = \prod_i
\operatorname{Mat}_{d_{i+1},d_i}$ — the home of the geometry (orbits, codimension, closures). The path
algebra $kQ$ and $kQ$-modules are the home of the homological algebra ($\operatorname{Hom}$,
$\operatorname{Ext}$). Voigt is the bridge: $\operatorname{codim}\mathcal O_M$ (in the variety) $=
\dim\operatorname{Ext}^1(M,M)$ (in $kQ$-Mod). So the equivalence `Tuple d ≃ kQ-modules of dim d` is a
load-bearing object, not redundancy. **We do not refound the engine** (its Gabriel crux is already on
abstract chains and its inversion is foundation-free combinatorics); we stack the new layers and bridge.
Refactor incrementally only if the bridge proves awkward.

## Plan (two phases)

- **Phase A — the Ext algebra** (whole-in-reach): $kQ$ and $kQ$-Mod on Mathlib; the `Tuple ≃ kQ-Mod`
  equivalence; $\operatorname{Hom}/\operatorname{Ext}^1$ (Mathlib derived `Ext` via projective
  resolutions); the Euler form and $\langle d,d\rangle = \dim\operatorname{Hom} -
  \dim\operatorname{Ext}^1$; $\operatorname{Ext}^1$ between interval modules; additivity → the
  **algebraic** identity $\dim\operatorname{Ext}^1(M,M) = \sum_{1\le i\le u\le j\le v\le N}
  m_{i-1,j-1}m_{uv}$.
- **Phase B — the orbit-dimension AG**: representation variety, the $G_{\underline d}$-action, orbit
  dimension $= \dim G - \dim\operatorname{Aut}$, tangent space, Voigt $\Rightarrow
  \operatorname{codim}\mathcal O_M = \dim\operatorname{Ext}^1(M,M)$; the orbit-closure order (Thm 3.8).
  Closes the geometric $C$.

## Opening recon (before the ladder is committed)

Two decorrelated threads, in parallel:

1. **Mathlib-coverage map** (`scout`): across both halves — (algebra) path algebras / quiver
   representations / `ModuleCat` / derived `Ext` / projective resolutions / hereditary algebras;
   (AG) affine varieties + Krull/codimension, algebraic-group actions, orbits + orbit dimension,
   tangent spaces, anything toward Voigt. What exists, what we build, what we build *on*.
2. **Mathematical design** (`pen-and-paper`): $\operatorname{Ext}^1(M_{ij}, M_{uv})$ between interval
   modules (the indicator); the Euler form $\langle d,d\rangle$ for equioriented $A_{N+1}$; verify
   $\dim\operatorname{Ext}^1(M,M) = \sum m_{i-1,j-1}m_{uv}$ on $(2,2,2)$; the $\operatorname{Hom}$ side;
   what the Voigt orbit-dimension argument requires; the standardness check (decorrelated Codex). A
   certificate, no Lean.

Recon reports → controller synthesis → Phase-A ladder committed.

## Closing criterion

Phase A: the algebraic $\dim\operatorname{Ext}^1(M,M)$ formula, green/sorry-free/axiom-clean, on standard
$kQ$-module foundations, with the `Tuple ≃ kQ-Mod` bridge. Phase B: the geometric
$\operatorname{codim}\mathcal O_M = \dim\operatorname{Ext}^1(M,M)$ (Cor 3.5) and the closure order.
Synthesis + ROADMAP update + statement cards at each phase close.
