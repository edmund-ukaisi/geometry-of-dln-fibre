# Statement card — Thread 04: thin RLCT interface (cite only `rlct = ½·codim_ℝ`, prove the geometry)

> **SUPERSEDED ON THE TRANSFER (thread 11, capstone).** This card lists the real↔complex transfer
> `T` (`codim_ℝ = codim_K`) as **Cited / Assumed / Deferred** and the boundary as
> `{watanabe_upper, aoyagi_lower, T}`. As of thread 11 (`expedition/rlct-bridge-discharge`), `T` is a
> **PROVED theorem** (`DLNFibre.DLN.codimRealFibre_eq_codimRepCanonical_baseChange`): both sides equal
> the same field-independent `C + δ`. The `hT` hypothesis is removed from every payoff. The cited
> boundary is now `{watanabe_upper, aoyagi_lower}`. See
> `threads/11-discharge-hT/statement-card.md` — the sections below describing `T` as cited are stale.

Branch `expedition/rlct-bridge-04-thin-interface`, commit `a3bd2b5f` (tightening pass). Files:
`lean/DLNFibre/DLN/{RlctPayoff,RlctPayoffGeneral,BundleShiftDischarge}.lean`.

---

> **Claim.** The DLN square-Frobenius RLCT payoff `rlct(K^DLN_B) = ½·codim mult⁻¹(B)` (over an
> algebraically-closed char-0 field `K`) rests on a MINIMAL cited boundary: two analytic bounds
> bracketing the rlct between `½·codim_ℝ` of the *real* fibre (both under the inhabited-fibre guard),
> plus one cited real-vs-complex transfer `codim_ℝ = codim_K`. The real codimension, the connector, the
> non-vacuity witness, and the codim-transfer's catenary reduction are PROVED, not cited.
>
> - **Lean (interface + analytic equality + witness):** `DLNFibre.DLN.RlctRealInterface` (fields
>   `cited_watanabe_upper`, `cited_aoyagi_lower`), `DLNFibre.DLN.rlctRealInterfaceWitness`,
>   `DLNFibre.DLN.rlct_lossDLN_eq_half_codimRealFibre` (`lean/DLNFibre/DLN/RlctPayoff.lean` @ `a3bd2b5f`).
> - **Lean (the transfer + its reduction + nonemptiness):** `DLNFibre.DLN.codimRealFibre`,
>   `DLNFibre.DLN.codimRealFibre_eq_codimRepCanonical_of_dimTransfer`,
>   `DLNFibre.DLN.fibre_zero_nonempty`, and the payoff theorems
>   `rlct_lossDLN_eq_half_codimFibre_of_transfer`, `rlct_lossDLN_zero_eq_half_{codimFibre,iInf_orbitCodim,cCodim}_via_aoyagi`,
>   `rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi` (`RlctPayoff.lean`);
>   `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`, `rlct_lossDLN_d222_one_eq_two_via_aoyagi`
>   (`RlctPayoffGeneral.lean`); `rlct_lossDLN_eq_half_cCodim_add_shift`, `rlct_lossDLN_d222_one_eq_two`
>   (`BundleShiftDischarge.lean`), all @ `a3bd2b5f`.
> - **Gloss.**
>   - `codimRealFibre d B := codimRepCanonical (k:=ℝ) (fibre ℝ d B)` — the `Ideal.height` of the
>     vanishing ideal of the REAL points of `mult⁻¹(B)` (the bare real-locus codim; not the complex one).
>   - `RlctRealInterface d` carries an opaque `rlct : (Tuple ℝ d → ℝ) → ℝ` + two bounds, BOTH under the
>     guard `0 < N → B.rank = r → (∀ k', r ≤ d k')` (= the fibre-nonempty condition, the monolith's exact
>     guard): `cited_watanabe_upper` (`rlct (lossDLN d B) ≤ ½·(codimRealFibre d B).toNat`) and
>     `cited_aoyagi_lower` (`½·(codimRealFibre d B).toNat ≤ rlct (lossDLN d B)`).
>   - `rlctRealInterfaceWitness d : RlctRealInterface d` — a PROVED inhabitant; its `rlct` reads
>     `½·(codimRepCanonical ℝ {A | F A = 0}).toNat` off the loss's own real zero-set, so on `lossDLN d B`
>     the connector `zeroLocus_lossDLN_eq_fibre` makes both bounds hold by `le_refl`. NOT the analytic rlct.
>   - `rlct_lossDLN_eq_half_codimRealFibre` = `le_antisymm` of the two bounds ⟹ `rlct = ½·codim_ℝ`.
>   - `codimRealFibre_eq_codimRepCanonical_of_dimTransfer`: from `hdim` (varietyDim_ℝ = varietyDim_K of
>     the fibre images) + both fibres nonempty, derives `codim_ℝ = codim_K` via the field-generic
>     catenary `codimRepCanonical + varietyDim = card(RepCoord d)` + `WithTop.add_right_cancel`. **Banked
>     but currently unused** — the payoffs thread the codim-level `hT` directly.
>   - The payoff theorems carry `hT : codimRealFibre d B = codimRepCanonical K (fibre K (B.map ι))`
>     (the codim-level Cited transfer) and conclude `rlct = ½·codim_K` (then `= C/2`, `= (C+shift)/2`).
> - **Proved (unconditional, axiom-clean `[propext, Classical.choice, Quot.sound]`).** The real-locus
>   codim definition; the non-vacuity witness `rlctRealInterfaceWitness` (so the interface type is
>   inhabited); the analytic equality from the two bounds (`le_antisymm`); the zero-fibre real
>   nonemptiness (`fibre_zero_nonempty`, `mult d 0 = 0` for N≥1); the catenary reduction of `codim_ℝ =
>   codim_K` to the real-dim = complex-dim equality; the connector `zeroLocus_lossDLN_eq_fibre`; the
>   geometry `codim_K = C` / `= 2λ` / `= cCodim + shift` (banked Core/ClosedForm).
> - **Assumed (carried hypotheses, visible in the type — NOT global axioms).** The two analytic bounds
>   (fields of `RlctRealInterface`, both guarded by `0 < N → B.rank = r → (∀ k', r ≤ d k')` — the
>   inhabited-fibre scope, load-bearing for soundness on the upper bound); the transfer `hT`
>   (`codim_ℝ = codim_K`, a standalone explicit hypothesis on each payoff theorem).
> - **Cited (named, sourced — the permanent boundary `{watanabe_upper, aoyagi_lower, T}`).**
>   - `cited_watanabe_upper` — Watanabe's universal log-canonical-threshold upper bound `rlct ≤ codim/2`.
>   - `cited_aoyagi_lower` — Aoyagi Thm 1 / Lehalleur–Rimányi §8 (`thm:aoyagi-rlct`, the `rlct = ½·codim`
>     theorem; the literal section is the paper's `\ref`, not a hardcoded number).
>   - `T` (`codim_ℝ = codim_K`) — the real-vs-complex transfer; TRUE (smooth full-dim real points of the
>     top components make real points Zariski-dense ⟹ real dim = complex dim) but not bounded-provable at
>     Mathlib v4.29. The payoffs cite the codim-level `hT`; the banked reduction shows `hT` follows from
>     the real-dim = complex-dim equality + both-fibres-nonempty, but that route is not threaded this tide.
> - **Deferred (named, roadmapped — NOT done).** A hypothesis-free proof of the transfer `T`: a smooth
>   full-dim real point in each top-dimensional component ⟹ real points Zariski-dense ⟹ real dim =
>   complex dim (a future real-algebraic-geometry expedition; cf. `rlct-runway-target`). For general-rank
>   `B`, real-fibre nonemptiness (a real rank-`r` factorization) is also deferred — which is why the
>   codim-level `hT` is threaded through consumers rather than the dim-transfer + nonemptiness via the
>   (banked) catenary reduction.
> - **Status.** sorry-free (full `scripts/lb DLNFibre` green; `#print axioms` force-checked on all 11
>   load-bearing decls = `[propext, Classical.choice, Quot.sound]`). Awaiting reviewer fidelity re-check.

---

### Caveat next to the claim (precision)
This is **not** an unconditional `rlct = ½·codim` theorem. The `_via_aoyagi` names signal the cited
analytic source; the `hT` hypothesis signals the cited geometric transfer; the guard
`0 < N → B.rank = r → (∀ k', r ≤ d k')` signals the inhabited-fibre scope (without it the upper bound
is uninhabitable by the true rlct: off `image(mult)` the fibre is empty, `(codim_ℝ).toNat = 0`, forcing
`rlct ≤ 0`). The real codim `codim_ℝ` is the BARE real-locus codim — the `x² + y²` discriminator (real
locus `{0}` has codim 2, matching `height(vanishingIdeal ℝ {0}) = (x,y)`, NOT the generator-ideal
height 1) is in the `codimRealFibre` docstring; the transfer to the complex codim is the cited `T`.
