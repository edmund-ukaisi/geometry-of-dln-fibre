# Thread 10 — RLCT payoff (Phase D + R, r = 0) — statement card

Module: `lean/DLNFibre/DLN/RlctPayoff.lean` (378 LoC, sorry-free, axiom-clean).
Build: whole `DLNFibre` library green (`lake build`, 3676 jobs); `scripts/sorries` = 0 sorry / 0 #exit
/ 0 native_decide / 0 axiom.
Axioms (`#print axioms`): `[propext, Classical.choice, Quot.sound]` on every delivered theorem,
including the payoff `rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi` — the Cited Aoyagi content is a
carried structure FIELD (`RlctInterface.cited_aoyagi_dln`), NOT a global axiom.
Pinned commit: `d3650f4` (branch `expedition/rlct-payoff`).

## The destination, plainly

The paper's RLCT payoff at corner `r = 0`: the square-Frobenius DLN loss `K^DLN_0` has real
log-canonical threshold `C/2`, where `C = cCodim d 0` is the combinatorial codimension — "DLNs are
mildly singular". The geometric codimension identity `codim mult⁻¹(0) = C` is the new content, proved
here; the `rlct = ½·codim` reading is the Cited analytic interface (Aoyagi / Watanabe).

## D2 — the loss and its zero-set (field = ℝ)

> **Claim.** The DLN square-Frobenius loss `K^DLN_B(A) = ‖mult A − B‖²_F` is nonnegative and vanishes
> exactly on the multiplication fibre `mult⁻¹(B)`.
>
> - **Lean:** `DLNFibre.DLN.lossDLN`, `lossDLN_nonneg`, `zeroLocus_lossDLN_eq_fibre`.
> - **Gloss.** `lossDLN d B A := Tr((mult A − B)ᵀ (mult A − B))` over ℝ; `0 ≤ lossDLN d B A`;
>   `{A | lossDLN d B A = 0} = fibre d B`.
> - **Proved.** Both, unconditionally over ℝ. Frobenius core `Tr(MᵀM) = 0 ↔ M = 0` from Mathlib
>   `trace_conjTranspose_mul_self_eq_zero_iff` (over ℝ, `conjTranspose = transpose` since `TrivialStar ℝ`).
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free.

## D3 — the geometric codimension of the zero-product fibre

> **Claim (bridge a).** `codim mult⁻¹(0) = min` codimension over its orbit closures.
>
> - **Lean:** `codimRepCanonical_fibre_zero_eq_iInf_orbitCodim` (`[IsAlgClosed k]`).
> - **Gloss.** `codimRepCanonical (fibre d 0) = ⨅ M ∈ {corner ≤ 0}, codimRepCanonical (orbitRankLocus M)`.
> - **Proved.** "codim of a finite union = min codim of its components": `height (sigmaIdeal d 0)`
>   = inf over its minimal primes (`minimalPrimes_sigmaIdeal_eq`, landed Core); each is an orbit ideal,
>   and every orbit ideal contains a minimal one of `≤` height (`exists_minimalPrimes_le` + `height_mono`).
> - **Assumed.** `[IsAlgClosed k]` (orbit-ideal primality).
> - **Cited / Deferred.** none.

> **Claim (bridge b).** `codim mult⁻¹(0) = C = cCodim d 0`.
>
> - **Lean:** `codimRepCanonical_fibre_zero_eq_cCodim` (`[IsAlgClosed k] [CharZero k]`).
> - **Gloss.** `((codimRepCanonical (fibre d 0)).toNat : ℤ) = cCodim d 0 h`.
> - **Proved.** The orbit-codim infimum (bridge a) equals the combinatorial `cCodim`. Lower bound:
>   every corner-`0` orbit's Gabriel partition (`Core.CCodimCornerMono.gabrielPartition`) is a corner-`0`
>   Kostant partition realising the same orbit, so its codim `= codimForm ≥ cCodim` (at `r = 0` the
>   Gabriel corner is the product rank `= 0` directly — no corner-monotonicity). Upper bound: the
>   realizer (`Core.ThetaComponentCount.realizerD`) of a minimising partition is a corner-`0` orbit
>   attaining `cCodim`. Consumes the LANDED `cCodim_eq_inf_geomCodim` + `codimRepCanonical_orbitRankLocus_realizerD`.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]` (the Voigt-discharge scope where `cCodim` is the
>   geometric codimension); `(kostantPartitions d 0).Nonempty`.
> - **Cited / Deferred.** none. (Bridge b is PROVED — the design's "Deferred" estimate was superseded by
>   the landed `realizerD` / `gabrielPartition` infrastructure.)

## R — the RLCT payoff through a Cited interface

> **Claim.** `rlct(K^DLN_0) = C/2`, with `rlct = ½·codim mult⁻¹(B)` Cited to Aoyagi.
>
> - **Lean:** `RlctInterface` (structure); `rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`.
> - **Gloss.** `RlctInterface d K ι` carries an opaque `rlct : (Tuple ℝ d → ℝ) → ℝ` and the **Cited**
>   field `cited_aoyagi_dln : ∀ B r, B.rank = r → r ≤ min d → rlct (lossDLN d B) = (codim (fibre K d (B.map ι)))/2`.
>   The payoff: `(I : RlctInterface d K ι) (h) : I.rlct (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ)/2`.
> - **Proved.** The transport: from `I.cited_aoyagi_dln` at `B = 0, r = 0` (so `(0).map ι = 0`) into the
>   zero-product codimension, then through bridge (b) `codim mult⁻¹(0) = C`. (Also the intermediate forms
>   `…_eq_half_codimFibre_via_aoyagi` and `…_eq_half_iInf_orbitCodim_via_aoyagi`.)
> - **Assumed.** the interface `I` itself (explicit hypothesis; the Cited dependency is in the type);
>   `[IsAlgClosed K] [CharZero K]`; `(kostantPartitions d 0).Nonempty`.
> - **Cited.** `I.cited_aoyagi_dln` = Aoyagi Thm 1 / Lehalleur–Rimányi Thm 8.6 — the rlct definition +
>   the equality `rlct(K^DLN_B) = ½·codim mult⁻¹(B)`. A carried structure field, NOT a global axiom (so
>   `#print axioms` stays clean). The equality stops at `½·codim mult⁻¹(B)`, so the payoff is genuine
>   transport, not a restatement.
> - **Deferred.** the general-`r` payoff (the Lemma 4.6 bundle shift `codim = C + r(d₀+d_N−r)`) —
>   roadmapped, out of scope here. `θ` is NOT in R (paper: no simple rlct↔θ relation).
> - **Name = content.** `via_aoyagi` is in every payoff name; `I : RlctInterface` is explicit in every
>   payoff type. No theorem named `rlct_…_eq_half_codim` without the interface in scope.

## Field interplay (the one subtlety)

The loss is over ℝ; the geometric codimension lives over an alg-closed char-`0` field `K`. The
`RlctInterface` carries `K`, a ring embedding `ι : ℝ →+* K`, and bridges real-loss rlct to the codim of
the base-changed fibre `mult⁻¹(B.map ι)` over `K` — the real↔complex passage Aoyagi Cites. No
from-scratch real↔complex codimension base-change lemma is needed.

## (2,2,2) non-vacuity

> - `codimRepCanonical_fibre_d222_zero : (codimRepCanonical (fibre (AlgebraicClosure ℚ) d222 0)).toNat = 3`
>   — the geometric reading of `cCodim d222 0 = 3` (LANDED `Core.CTheta.cCodim_d222_zero`, LR Ex 4.3).
> - `rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi (I : RlctInterface d222 ℂ Complex.ofRealHom) :
>   I.rlct (lossDLN d222 0) = 3/2` — the payoff `rlct = C/2 = 3/2` on the worked example, over ℂ (which
>   carries `ℝ →+* ℂ`; there is no ring hom `ℝ →+* ℚ̄`, so the codim witness is over ℚ̄ and the rlct
>   witness over ℂ).

## Status

sorry-free; reviewer fidelity check requested (AUDIT gate).
