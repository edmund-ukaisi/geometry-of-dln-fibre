# Statement card — Thread 04: thin RLCT interface (cite only `rlct = ½·codim_ℝ`, prove the geometry)

Branch `expedition/rlct-bridge-04-thin-interface`, commit `c07c5c5d`. Files:
`lean/DLNFibre/DLN/{RlctPayoff,RlctPayoffGeneral,BundleShiftDischarge}.lean`.

---

> **Claim.** The DLN square-Frobenius RLCT payoff `rlct(K^DLN_B) = ½·codim mult⁻¹(B)` (over an
> algebraically-closed char-0 field `K`) rests on a MINIMAL cited boundary: two analytic bounds
> bracketing the rlct between `½·codim_ℝ` of the *real* fibre, plus one cited real-vs-complex transfer
> `codim_ℝ = codim_K`. The real codimension, the connector, and the codim-transfer's reduction to an
> atomic dimension equality are PROVED, not cited.
>
> - **Lean (interface + analytic equality):** `DLNFibre.DLN.RlctRealInterface` (fields
>   `cited_watanabe_upper`, `cited_aoyagi_lower`) + `DLNFibre.DLN.rlct_lossDLN_eq_half_codimRealFibre`
>   (`lean/DLNFibre/DLN/RlctPayoff.lean` @ `c07c5c5d`).
> - **Lean (the transfer + its reduction):** `DLNFibre.DLN.codimRealFibre`,
>   `DLNFibre.DLN.codimRealFibre_eq_codimRepCanonical_of_dimTransfer`,
>   `DLNFibre.DLN.fibre_zero_nonempty`, and the payoff theorems
>   `rlct_lossDLN_eq_half_codimFibre_of_transfer`, `rlct_lossDLN_zero_eq_half_{codimFibre,iInf_orbitCodim,cCodim}_via_aoyagi`,
>   `rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi` (`RlctPayoff.lean`);
>   `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`, `rlct_lossDLN_d222_one_eq_two_via_aoyagi`
>   (`RlctPayoffGeneral.lean`); `rlct_lossDLN_eq_half_cCodim_add_shift`, `rlct_lossDLN_d222_one_eq_two`
>   (`BundleShiftDischarge.lean`), all @ `c07c5c5d`.
> - **Gloss.**
>   - `codimRealFibre d B := codimRepCanonical (k:=ℝ) (fibre ℝ d B)` — the `Ideal.height` of the
>     vanishing ideal of the REAL points of `mult⁻¹(B)` (the bare real-locus codim; not the complex one).
>   - `RlctRealInterface d` carries an opaque `rlct : (Tuple ℝ d → ℝ) → ℝ` + `cited_watanabe_upper`
>     (`∀ B, rlct (lossDLN d B) ≤ ½·(codimRealFibre d B).toNat`, universal) + `cited_aoyagi_lower`
>     (`∀ B, 0<N → ½·(codimRealFibre d B).toNat ≤ rlct (lossDLN d B)`, DLN-specific).
>   - `rlct_lossDLN_eq_half_codimRealFibre` = `le_antisymm` of the two ⟹ `rlct = ½·codim_ℝ`.
>   - `codimRealFibre_eq_codimRepCanonical_of_dimTransfer`: from `hdim` (varietyDim_ℝ = varietyDim_K of
>     the fibre images) + both fibres nonempty, derives `codim_ℝ = codim_K` via the field-generic
>     catenary `codimRepCanonical + varietyDim = card(RepCoord d)` + `WithTop.add_right_cancel`.
>   - The payoff theorems carry `hT : codimRealFibre d B = codimRepCanonical K (fibre K (B.map ι))`
>     (the codim-level Cited transfer) and conclude `rlct = ½·codim_K` (then `= C/2`, `= (C+shift)/2`).
> - **Proved (unconditional, axiom-clean `[propext, Classical.choice, Quot.sound]`).** The real-locus
>   codim definition; the analytic equality from the two bounds (`le_antisymm`); the zero-fibre real
>   nonemptiness (`fibre_zero_nonempty`, `mult d 0 = 0` for N≥1); the catenary reduction of `codim_ℝ =
>   codim_K` to the atomic real-dim = complex-dim equality; the connector `zeroLocus_lossDLN_eq_fibre`
>   (pre-existing); the geometry `codim_K = C` / `= 2λ` / `= cCodim + shift` (banked Core/ClosedForm).
> - **Assumed (carried hypotheses, visible in the type — NOT global axioms).** The two analytic bounds
>   (`cited_watanabe_upper`, `cited_aoyagi_lower`, fields of `RlctRealInterface`); the transfer `hT`
>   (`codim_ℝ = codim_K`, a standalone explicit hypothesis on each payoff theorem).
> - **Cited (named, sourced — the permanent boundary).**
>   - `cited_watanabe_upper` — Watanabe's universal log-canonical-threshold upper bound `λ ≤ codim_ℝ/2`.
>   - `cited_aoyagi_lower` — Aoyagi Thm 1 = Lehalleur–Rimányi Thm 8.6 (the DLN-specific matching lower
>     bound), scope `0 < N`.
>   - `T` (`codim_ℝ = codim_K`) — the real-vs-complex transfer; TRUE (smooth full-dim real points of the
>     top components, e.g. the rational `realizerD`, make real points Zariski-dense ⟹ real dim = complex
>     dim) but not bounded-provable at Mathlib v4.29 (no real-Nullstellensatz / semialgebraic dim).
>     Reduces (proved) to the ATOMIC real-dim = complex-dim equality `hdim`, so the irreducible cited
>     content is that dimension equality.
> - **Deferred (named, roadmapped — NOT done).** A hypothesis-free proof of the transfer `T` / its
>   atomic `hdim`: a smooth full-dim real point in each top-dimensional component ⟹ real points
>   Zariski-dense ⟹ real dim = complex dim (a future real-algebraic-geometry expedition; cf.
>   `rlct-runway-target`). For general-rank `B`, real-fibre nonemptiness (a real rank-`r` factorization)
>   is also deferred — which is why the codim-level `hT` is threaded through consumers rather than the
>   atomic `hdim` + nonemptiness (the catenary reduction is banked for when that lands).
> - **Status.** sorry-free (full `scripts/lb DLNFibre` green, 3815 jobs; `#print axioms` force-checked
>   on all 10 load-bearing theorems = `[propext, Classical.choice, Quot.sound]`). Awaiting reviewer
>   fidelity check.

---

### Caveat next to the claim (precision)
This is **not** an unconditional `rlct = ½·codim` theorem. The `_via_aoyagi` names signal the cited
analytic source; the `hT` hypothesis signals the cited geometric transfer. The real codim `codim_ℝ`
is the BARE real-locus codim — the `x² + y²` discriminator (real locus `{0}` has codim 2, matching
`height(vanishingIdeal ℝ {0}) = (x,y)`, NOT the generator-ideal height 1) is in the `codimRealFibre`
docstring; the transfer to the complex codim is the cited `T`, not something `codim_ℝ` knows.
