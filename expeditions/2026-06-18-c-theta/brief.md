# Expedition brief — c-theta

**Branch:** `expedition/c-theta` (worktree `.claude/worktrees/c-theta`), stacked on
`expedition/ext-codimension`. Uses the proven quadratic form from `Core.DeformationExt`/`Core.OrbitCodim`
and the Kostant/`multiplicityArray` engine. Pure ℕ-combinatorics — no algebraic geometry, no `voigt`.

## Central question

Compute, in honest Lean, the **codimension $C$** and the **number $\theta$** of top-dimensional
irreducible components of the rank-$r$ product locus (Lehalleur–Rimányi §§5–7). With Cor 3.5 proved as the
quadratic form, this is the optimisation

$$
C \;=\; \min_{\underline m}\ \sum_{1\le i\le u\le j\le v\le N} m_{i-1,j-1}\,m_{uv},
\qquad
\theta \;=\; \#\{\text{minimisers}\},
$$

over the **Kostant partitions $\underline m$ of $\underline d$ with $m_{0N}=r$**. Targets:
the quadratic integer program (Thm 6.1), the explicit closest-lattice-point formula (Thm 7.10), and the
**permutation invariance** of $(C,\theta)$ in $\underline d$ (Cor 5.10).

## Architecture

Build `DLNFibre.Core` combinatorics on top of the existing engine. The orbit codimation per Kostant
partition is `Core.OrbitCodim`/`DeformationExt`'s $\sum m_{i-1,j-1}m_{uv}$ (Proved). The geometric reading
"$C = \operatorname{codim}\Sigma^r$" rides on the deferred `hVoigt`; **the combinatorial $(C,\theta)$ does
not** — it is defined and proved purely from the form. Name accordingly (combinatorial $C,\theta$; the
geometric identification stays modulo `hVoigt`).

## Ladder (recon to sharpen)

- **Layer 1 — define $C,\theta$ (bedrock now).** The Kostant partitions of $\underline d$ with $m_{0N}=r$
  as a `Finset`; the quadratic form on them; `C := Finset.min'` of the form's image, `θ :=` minimiser
  count. Non-vacuity: $(2,2,2)$, $r=0$ ⟹ $C=3,\theta=1$ (the six $m_{02}=0$ partitions; min codim 3, unique).
- **Layer 2 — QIP (Thm 6.1).** Reformulate $C$ as $\min G_{\underline d}(\underline e)$ over
  $\underline e\in\mathbb N^N$, $\sum e_i=d'_0$ (the weakly-increasing rearrangement $\underline d'$);
  prove equal to Layer 1's min. Medium combinatorics.
- **Layer 3 — explicit formula (Thm 7.10).** Closed-form $C$ and $\theta$ via closest lattice points in a
  type-A simplex; $\theta$ a binomial coefficient. The hard combinatorial core — recon scopes it.
- **Layer 4 — permutation invariance (Cor 5.10).** $(C,\theta)$ depends only on the multiset
  $\{d_0,\dots,d_N\}$. Either a corollary of Thm 7.10, or an independent combinatorial route (Bundle 3's
  Poincaré is the paper's route; likely avoidable here).

## Steering

Standard combinatorics, controller makes the calls; `/local-codex-consult` on standardness / the QIP and
lattice-point routes. Mark Proved / Assumed / Cited. Reachable bundle — finite types, `Finset` optimisation,
ℕ-arithmetic. Mathlib: `Finset.min'`/`argmin`, `Finset.filter`/`card`, lattice-point counting.

## Opening recon

Chart the ladder + the Thm 7.10 closed-form difficulty + Mathlib `Finset`-optimisation / lattice coverage;
verify $(2,2,2)$ and a second case ($(2,3,2)$ or $(2,4,2)$) numerically; decorrelated Codex. Then build
Layer 1 (define $C,\theta$) and assess Layers 2–4.

## Closing criterion

Layer 1: $C,\theta$ defined + the $(2,2,2)$ witness, green/sorry-free/axiom-clean. Then as far up the ladder
(QIP → explicit formula → permutation invariance) as is whole-in-reach, each Proved. Synthesis + statement
cards + ROADMAP update at close.
