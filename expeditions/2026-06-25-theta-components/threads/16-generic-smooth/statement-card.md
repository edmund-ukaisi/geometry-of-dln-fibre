# Statement card — thread 16: generic smoothness of the reduced fibre chart

> **Claim.** Over an algebraically closed field, the reduced fibre variety of the multiplication map
> is smooth at the generic point of each top-dimensional irreducible component (`Algebra.IsSmoothAt`
> at that prime). The fibre is reducible for `θ ≥ 2`, so only the pointwise statement is true; it is
> assembled from the banked product trivialization `Away chartDsig ≃ₐ[k] SchurLoc ⊗ sweepFibreRing`
> and the always-smooth matrix factor `SchurLoc`. Here the **conditional rung** is delivered: the
> local matrix×fibre chart-piece `SchurLoc ⊗ Localization.Away g` is genuinely smooth, given the
> reduced fibre ring is smooth at the relevant prime (the thread-14 fact (C): generic Jacobian
> rank `= codim = C+δ` on every top component).

- **Lean (headline):** `DLNFibre.Core.smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre`
  (`lean/DLNFibre/Core/FibreGenericSmooth.lean` @ `c450983f`)
  - Signature: for `d : Fin (N+2) → ℕ`, `r`, `hp : r ≤ d (last (N+1))`, `hq : r ≤ d 0`, a prime `q`
    of `sweepFibreRing k d r hp hq` with `Algebra.IsSmoothAt k q`, there exists `g ∉ q` with
    `Smooth k (SchurLoc (d 0) (d (last (N+1))) r ⊗[k] Localization.Away g)`.
- **Gloss.** If the reduced fibre coordinate ring is formally smooth at the prime `q` (the generic
  point of a top-dimensional component), then there is a fibre function `g` non-vanishing at `q`
  such that, on the basic open `{g ≠ 0}`, the product of the (always smooth) Schur matrix
  localization with the fibre localization is a smooth `k`-algebra. This is the factor-wise
  smoothness of the tensor-trivialized chart, with the matrix factor discharged unconditionally and
  the fibre factor carried as the one honest hypothesis.

- **Proved (unconditional, axiom-clean `[propext, Classical.choice, Quot.sound]`):**
  - `Algebra.Smooth.tensorProduct` — `Smooth R A → Smooth R B → Smooth R (A ⊗[R] B)` (any comm base).
  - `smooth_away_mvPolynomial` — `Smooth k (Localization.Away g)` for `g` in a finite-variable
    polynomial ring over `k`.
  - `smooth_schurLoc` — `Smooth k (SchurLoc q p r)` (the matrix factor is smooth).
  - `isSmoothAt_of_smooth_localizationAway` — basic-open bridge `Smooth k (Away g) + g ∉ q ⟹
    IsSmoothAt k q` (needs `FinitePresentation k B`).
  - `finitePresentation_sweepFibreRing` — the reduced fibre ring is finitely presented over `k`.
  - `smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre` (the headline, conditional on the
    hypothesis below).
- **Assumed.** `Algebra.IsSmoothAt k q` for `sweepFibreRing` at the top-component generic prime `q`.
  This is the formal-smoothness reading of the thread-14 fact (C) (generic Jacobian rank `= codim =
  C+δ` on every top component, verified on 15600 dimension vectors + Singular certs); the
  Jacobian-rank `⟹` `IsSmoothAt` bridge rests on the `IsAlgClosed k` (hence perfect-field) setting
  named in the claim. NOT discharged in Lean here.
- **Cited.** none (the hypothesis is a Lean-level openness, not an external citation).
- **Deferred (the precise cost of going unconditional):**
  - (i) Discharge `IsSmoothAt k q` of `sweepFibreRing` at top-component generic points. Two routes,
    both unbanked: (a) the orbit-closure transport — `OrbitSmooth.isSmoothAt_normalFormIdeal` gives
    `IsSmoothAt` for a single orbit-closure ring `orbitRing M`, but the fibre is the reducible union;
    the missing step is a quotient-by-intersection localization comparison (`Loc.AtPrime (R⧸⋂Iⱼ) ≃
    Loc.AtPrime (R⧸I_M)` at a prime on `I_M` and off the others) plus "the normal-form point is off
    the other top components" — not in this harness; (b) the determinantal minor-unit feeding
    `FibreSmoothPlumbing` — blocked on thin Mathlib determinantal-rank support.
  - (ii) Transport `Smooth k (SchurLoc ⊗ Away g)` to `Algebra.IsSmoothAt k p` of `Away chartDsig`
    across the banked iso `reducedFibre_chartDsig_tensorEquiv_reducedVariety`. Needs the
    localization-of-base-change identification `SchurLoc ⊗ Away g ≃ Localization.Away (1 ⊗ g)` in
    `SchurLoc ⊗ sweepFibreRing` (`IsLocalization.tensorProduct_tensorProduct`, the
    `FibreBundleReduced` bookkeeping pattern, ~60-80 lines), then `isSmoothAt_of_smooth_localizationAway`
    through `e`.
- **Route.** FLOOR landing (per the thread-16 brief): both LEAD (orbit transport) and FALLBACK
  (determinantal minor-unit) proved walls inside the tide (Codex-confirmed: LEAD wall = localization-
  of-base-change + component-localization comparison; FALLBACK wall = determinantal rank theory).
  The chosen landing isolates the one honest input (`IsSmoothAt` of the fibre factor) and discharges
  everything else (matrix-factor smoothness, the tensor-smooth and basic-open bricks) unconditionally.
- **Status.** sorry-free + reviewed (fidelity PASS-WITH-NOTES; N1 wording + N3 field-assumption
  notes actioned; N2 framing guard-rail noted for downstream synthesis).
