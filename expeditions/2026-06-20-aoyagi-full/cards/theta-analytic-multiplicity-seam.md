# Statement card — the θ analytic-multiplicity SEAM (DEFERRED; standing-decision-6)

**Status:** DEFERRED SEAM — documented, not a Lean rung. The RLCT-side attempt at the θ
(component-count / multiplicity) was a Lean PLACEHOLDER resting on an OPAQUE; it was **excised**
(strand `genm-excise`, Stage B) rather than carried as a sorried/opaque rung. This card re-homes the
claim per standing-decision-6. The `aoyagiTheta` **definition** survives; only the unproven binding is
gone.

## What θ is (the object)
`aoyagiTheta (ℓ a : ℕ) : ℕ := a * (ℓ − a) + 1` (`Foundations/Lambda.lean:92`) — the paper's number of
**top-dimensional components** of the fibre `mult⁻¹(B)` (Lehalleur–Rimányi §5; the `θ` in the pair
`(C, θ)`). In Watanabe's RLCT theory the learning coefficient is a **pair** `(λ, m)`: `λ` the
coefficient (the leading pole of the zeta), `m` the **multiplicity** (that pole's order). The paper's
content is that for DLNs the multiplicity `m` equals the component count `θ = a(ℓ − a) + 1`.

## What this expedition PROVED vs what is the seam
- **PROVED (primary, complete, S2-free):** the coefficient `λ = aoyagiLambda H r` — the four headline
  results `aoyagi_learning_coefficient_L2` / `_gen` / `aoyagi_learning_coefficient_gen_le` /
  `aoyagi_deepest_reduction_gen`. `λ` comes from the **minimum axis-ratio** over the resolution charts
  (`monomialThreshold = ⨅ⱼ axisRatio`), which the proven identity `monomialThreshold_eq_iInf_axisRatio`
  establishes S2-free.
- **THE SEAM (deferred):** the **multiplicity** `m` — the pole ORDER at `−λ`, i.e. the count of charts
  achieving the minimum ratio (the top-dimensional components) — matched to `aoyagiTheta`. The
  multiplicity is genuinely subtler than the value: `λ` needs only the `min` of the ratios; `m` needs
  to COUNT the achievers and prove that count is `a(ℓ − a) + 1` and that the analytic pole order equals
  that combinatorial count.

## What was excised (Stage B, `genm-excise`) — and why
Three interlocking non-honest Lean objects, deleted together (zero live proof-term uses):
1. `aoyagiTheta_eq` (`Skeleton.lean:1705`) — a **bare `sorry`**: `∃ ℓ a d (k h : Fin d → ℕ),
   monomialOrder d k h = aoyagiTheta ℓ a`. A weak-existential placeholder; never proved.
2. `monomialOrderAnalytic` (`Skeleton.lean:101`) — an **`opaque` def** (unprovable by construction):
   the analytic pole order.
3. `monomial_rlct.2` — the axiom conjunct `(∃ j, k j ≠ 0) → monomialOrderAnalytic d k h =
   monomialOrder d k h`, binding the opaque analytic order to the combinatorial `monomialOrder`.
A `sorry` resting on an `opaque` bound by an `axiom` is not honest content (precision/bedrock): it
looks like a theorem but proves nothing. Excising it (vs sorry-carrying it) is the bedrock choice —
the honest state is a documented seam, not a green-but-vacuous rung.

## The honest θ content that DOES exist (elsewhere)
The **Core engine** computes `(C, θ)` combinatorially — network-free, via the type-A quiver / Kostant
partitions / the `Ext`-codimension (`DLNFibre.Core`; ROADMAP §"(C, θ)"). That is the **geometric**
component count, independent of any RLCT/analytic input. The seam below is specifically the
**analytic** side (binding the zeta's pole multiplicity to that geometric `θ`).

## Kill-condition / what would discharge the seam
An honest computation of the **analytic multiplicity** of the DLN square-Frobenius zeta at its leading
pole `−λ` — i.e. the normal-crossing multiplicity of the resolution at the deepest stratum — proved
equal to `aoyagiTheta ℓ a = a(ℓ − a) + 1` (equivalently: the number of resolution charts whose
`axisRatio` achieves the `⨅`, counted with the correct order). Dies if that pole order is NOT
`a(ℓ − a) + 1`, or if the analytic order ≠ the combinatorial `monomialOrder` (the gap the excised `.2`
axiom papered over). This is a genuine analytic result (Watanabe-style multiplicity analysis), not a
corollary of the value computation already done.

## Scope note
This is the **secondary** deliverable. The paper's headline payoff — the learning coefficient
`λ = C/2` (mild singularity) — rests on the VALUE, which is complete and S2-free. The multiplicity `θ`
sharpens `(λ, m)` to the full RLCT pair but is not needed for the `λ` headline. Roadmapped as a
future analytic-multiplicity expedition.
