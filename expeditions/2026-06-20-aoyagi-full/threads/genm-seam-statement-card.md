# genm-seam statement card — the §2 gauge-absorption lemma (crux ii)

> **Claim.** At a block-normalized corank-`q` point of the product rank-drop locus (each layer
> `A_s = fromBlocks 1 0 0 (Ĉ_s)`, a `q`-dim identity thread ⊕ shifted complement `Ĉ_s`), every
> first-order deformation of the thread block and the two thread↔complement cross-blocks lies in the
> image of the linearized end-to-end base-change action; the shifted-complement block is the free
> normal direction. (§2 seam chart, discuss-at-close #80 §2; the "one genuinely-new brick".)
>
> - **Lean:** `DLNFibre.DLN.RLCT.SeamGauge.gaugeAbsorption`
>   (`lean/DLNFibre/DLN/RLCT/Validate/SeamGaugeAbsorption.lean` @ `d2bb1574`, branch
>   `origin/genm-seambuild`; not yet wired into `DLNFibre.lean` — controller batch-integrates)
> - **Gloss.** For any width data (thread type `r`, complement widths `m : ℕ → Type*`, ring `α`),
>   any chain of complement maps `Ĉ : (s:ℕ) → Matrix (m s) (m (s+1)) α`, any length `L`, and any
>   targets `tTL : ℕ → Matrix r r α`, `tTR : (s) → Matrix r (m (s+1)) α`, `tBL : (s) → Matrix (m s) r α`,
>   there EXISTS a node-indexed gauge deformation `ξ : (i:ℕ) → Matrix (r ⊕ m i) (r ⊕ m i) α` (with its
>   complement block `δ = 0`) such that the linearized base-change deformation
>   `gaugeDeform Ĉ ξ s = blockLayer Ĉ s * ξ (s+1) − ξ s * blockLayer Ĉ s` has `toBlocks₁₁ = tTL s`,
>   `toBlocks₁₂ = tTR s`, `toBlocks₂₁ = tBL s` for every layer `s < L`. (The `toBlocks₂₂` / BR block is
>   left unconstrained — the shifted-complement normal direction.)
> - **Proved.** Unconditionally: the three targets are all realized simultaneously, by the explicit
>   forward accumulators `gaugeAlpha` (TL: `α_{s+1}−α_s = tTL_s`), `gaugeBeta` (TR:
>   `β_{s+1}−β_s Ĉ_s = tTR_s`) and the backward accumulator `gaugeGamma` (BL: `Ĉ_s γ_{s+1}−γ_s = tBL_s`,
>   via a fuel `=L−s` countdown, `gaugeGammaFuel`). No matrix inverse is taken — all three telescopes are
>   exact. This is the concrete Ext-free content of "`M_{0N}` projective + injective" (forward solve from
>   the source, backward solve from the sink). Over any `Ring α` (no commutativity used).
> - **Assumed.** None (no hypotheses beyond the ambient `Fintype`/`DecidableEq` typeclasses on the index
>   types, which the statement carries).
> - **Cited.** None. Axiom footprint `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`,
>   olean-deleted recompile). Imports only `Mathlib.Data.Matrix.Block` + `Mathlib.Tactic`; NO
>   `DLNFibre.Core`, NO `Ext`/quiver/codim — independence preserved.
> - **Deferred.** This lemma is the LINEARIZED surjectivity crux (ii) only. It does NOT by itself close
>   the sole remaining headline sorry `sjJointResolution` (a MEASURE finiteness of `gammaPeelIntegral`).
>   The seam-chart route from here — (iii) upgrade the infinitesimal surjectivity to a local
>   measure-preserving change of variables (IFT/diffeo, controlled Jacobian), (iv) loss-identification,
>   (v) a.e. pivot-indexed chart cover + monomialisation → `hIH` on the shifted chain + banked monomial
>   endpoint — is NOT built here. See the spend verdict below.
> - **Structure & ideas observed.** The block-derivative of the end-to-end base change
>   `δA_s = A_s ξ_{s+1} − ξ_s A_s` (conjugating the product, endpoints free) splits into four blocks:
>   TL `= α_{s+1}−α_s`, TR `= β_{s+1}−β_s Ĉ_s`, BL `= Ĉ_s γ_{s+1}−γ_s`, BR `= Ĉ_s δ_{s+1}−δ_s Ĉ_s`.
>   The thread's presence at EVERY node is what makes all three accumulators well-typed at every layer
>   (never falls off an end). Genre-identical to the banked `psiSplitRawGen` forward/backward chain
>   accumulator. Numerically pre-verified (block formula + all three solves, random L=3, q=2, varying
>   widths).
> - **Route.** Direct: mirror `psiSplitRawGen`'s ℕ-indexed abstract-type-width chain idiom
>   (`DeepestPsiSplitGenMoved`); state at the matrix level over an abstract `Ring`; three structural
>   accumulators + `fromBlocks_multiply`/`fromBlocks_sub` block algebra + `toBlocks_fromBlocks` reads.
> - **Status.** sorry-free (fidelity review pending — reviewer to be spawned).
