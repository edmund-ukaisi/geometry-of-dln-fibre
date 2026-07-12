# FaithfulSJAt — the base-invariant design cert (OPT-A; the peel-closure postcondition #4 consumes / #5 preserves)

**Seat:** pen-and-paper (design cert BEFORE formalisation — genm-sj5-cover, with genm-sj5-desc3 on
formalizability). **Date:** 2026-07-12. **NO Lean build.** **Charge (team-lead):** the EXACT α/β/γ clauses of
the `FaithfulSJAt D (½·minAdm M)` invariant, Lean-friendly against the `SJDecoration` carrier, each tied to its
banked cert; confirm `htriv` + that it subsumes the `d=0∧ofMatrix` fix; specify #4 (consume) / #5 (preserve).

**Consumed:** `RouteMSJDecorated` (SJDecoration/decLoss/radialAttach/trivial), `RouteMSJLedger`
(sharedDivisorExp/commonDivisor/residualSupport/sjLoss/monomialThreshold), `RouteMSJAdm` (adm/admValuation/
pSimultaneous), `RouteMSJUnitsBridge` (#147), `stephyp-intersection-cert`, `dmcheck cert` (the settled
invariant), `transversality-recursion`. **Base-fork decision:** OPT-A (intrinsic coupling; cert §basefork,
decorrelated-confirmed). **Formalizability co-design with desc3** flagged at the one open point (§4).

---

## ★ The invariant (against the `SJDecoration` carrier)

`decLoss D u z = D.carrier.loss u (ctx z).1 (ctx z).2 = Σ_{i:ι} (∏_ℓ |u_ℓ|^{supp i ℓ} · res_i(z))²`
(`res_i(z) := carrier.residual (ctx z).1 (ctx z).2 i`). Write `k_ℓ := sharedDivisorExp supp ℓ = ⨅_i supp i ℓ`,
`commonDivisor(u) = ∏_ℓ |u_ℓ|^{k_ℓ}`. `D.integral c' = ∫_{dom} ∫_{unitBox} (∏|u_ℓ|^{jac_ℓ})·decLoss^{−c'}`.

> **`FaithfulSJAt (D : SJDecoration M) : Prop` :=**
> **either** (D.d = 0 ∧ `D.carrier = SJLinGenState.ofMatrix (M 0) (M last)`)   — the smooth free-block leaf
> **or** ( 1 ≤ D.d ∧
>   **(α)** `∃ i₀ : ι, ∀ (j:ι) (ℓ:Fin d), supp i₀ ℓ ≤ supp j ℓ`   [= pSimultaneous — the DEHOMOGENISED gen i₀]
>   **(β)** `(½·minAdm M : ℝ≥0∞) ≤ monomialThreshold D.d (sharedDivisorExp D.carrier.supp) D.jac`   [THRESHOLD]
>   **(γ)** `∃ c > 0, (Z·Zᵀ − c•(1:Matrix)).PosSemidef`  on the WHOLE deeper tail `Z = A₂·A₃···A_L`
>          [BLOCK-LEVEL Z-UNITS-BOUND — the LOCKED form, see ★CORRECTION below] ).

The `d=0∧ofMatrix` disjunct SUBSUMES the FLAG-1 fix. `htriv`: `FaithfulSJAt (trivial M)` is the left disjunct
(`trivial.d=0`, `trivial.carrier = ofMatrix` by def) — discharges immediately (`rfl`-level). ✓.

> **★ LOCKED (2026-07-12, γ-lock — read the ★CORRECTION section at the bottom for the binding spec).** The
> (γ) clause above is the block-level Z-units-bound `Z·Zᵀ ≽ c·I` on the WHOLE tail `Z` — NOT the i₀-component
> and NOT `‖residualBlock‖`. #4 (base) closes via route-A `corankLeaf_rpow_lt_top` at threshold
> `min(T_u, D_Γ/2)` (MIN-of-two-full-budgets, NOT ADD). The §1–§4 inline prose below predates the lock; where
> it says `σ_min(A₂)` read `σ_min(Z)` (whole tail) and where it says `‖residualBlock‖`/i₀-component read
> `Z·Zᵀ≽c·I`. The 4 LOCK conditions are enumerated in the ★CORRECTION.

## 1. The three clauses, each tied to a banked cert

- **(α) pSimultaneous** — the dehomogenised generator `i₀` with `supp i₀ ℓ = k_ℓ ∀ℓ` (attains the shared min),
  so its monomial `∏|u_ℓ|^{supp i₀ ℓ} = commonDivisor(u)`. **BANKED**: `RouteMSJAdm.admValuation` /
  `RouteMSJAdmEncoding.pSimultaneous` (already in adm; the (T) condition, rejects `x²+y²` regression-2). This
  is the "corank generator is a unit at every critical divisor = p=0" (transversality-recursion).
- **(β) THRESHOLD `½minAdm ≤ monomialThreshold(d, k, jac)`** — `monomialThreshold = ⨅_{ℓ: k_ℓ>0} (jac_ℓ+1)/(2
  k_ℓ)`. This is the CHARGES-ADD condition: the accumulated `(jac, k)` give the corner threshold `= ½minAdm`
  (dmcheck's `½(M₀ρ+min(M₀q,D_q))`, the QIP identity, `minAdm_eq_backPeel` #144). **TIED**: `#144`
  (`RouteMSJTransversality`/`RouteMSJBackPeel`) + dmcheck's no-collapse (β is exactly "no cell undershoots
  ½minAdm"). #5 MAINTAINS it across the peel.
- **(γ) BLOCK-LEVEL Z-UNITS-BOUND (quantitative, ∃c>0 — `Z·Zᵀ ≽ c·I` on the WHOLE tail `Z`)** — the deeper
  tail product is uniformly nondegenerate on `dom` (after the smooth/Morse coordinates). **TIED**: the `#147`
  units bridge (`RouteMSJUnitsBridge`: full-row-rank `Z` ⟹ `Z·Zᵀ ≽ c·I` — already WHOLE-`Z`) + my
  `stephyp-cert` T4 (`σ_min(Z)≥ε` on the WHOLE deeper product, NOT just `A₂` — γ-lock). This is Codex's
  γ-catch: `res(z)=z^N` has a NULL zero-set but a divergent negative moment — the base needs the tail bounded
  below (a unit), NOT merely a.e.-nonzero. [The i₀-component version is UNSATISFIABLE for free `Γ`; ★CORRECTION.]

## 2. #4 — the base `FaithfulSJAt ⟹ DecoratedBoxThresholdFinite` (consume)

Two cases, for `c' < ½minAdm M`:
- **`d=0` (ofMatrix):** `commonDivisor≡1`, `decLoss = Σ_i res_i² = frobSq(prod M z)` (the smooth width-2
  free-block, `M` a 2-node = single matrix, `{prod=0}` smooth). `∫_{dom} frobSq(prod M z)^{−c'} < ⊤` for
  `c' < ½·(M₀·M₁) = ½minAdm` — the free-Morse / `baseBoxCoV` (banked, `RouteMSJBaseFinite`). ✓.
- **`d≥1`:** the coupled `u`-monomial × free corank block `Γ`. Route-A `corankLeaf_rpow_lt_top`
  (`RouteMSJLeafRayleigh`/`LeafFinite`): the uniform block lower comparison `decLoss ≳ commonDivisor(u)²·‖Γ·Z‖²`,
  then Rayleigh `frobSq(ΓZ) ≥ c·frobSq(Γ)` (consuming **(γ)** `Z·Zᵀ≽c·I` on the WHOLE `Z`) integrates `Γ` as a
  FREE BLOCK. Threshold `= min(T_u, D_Γ/2)` — **MIN-of-two-full-budgets, NOT ADD** (the base is separable; charges
  ADD only at the #5 STEP corner, not here — do not conflate). Reaches `½minAdm` because **(β)** `T_u ≥ ½minAdm`
  AND the **LEAF IDENTITY** `dim Γ = minAdm(M)` at the width-2 leaf (`M=(b,M₂)`: `minAdm = b·M₂ = D_Γ`), giving
  `D_Γ/2 = ½minAdm`. Closes `∫ (∏|u|^{jac})·decLoss^{−c'} < ⊤` for `c' < ½minAdm`. `vol(dom) < ⊤` banked.

## 3. #5 — the step PRESERVES `FaithfulSJAt` (the substantial content, = my certs)

The peel (radialAttach + the coupled-corner chart + redChain reduction) maps a FaithfulSJAt decoration to a
FaithfulSJAt reduced decoration, MAINTAINING α/β/γ:
- **(β preserved) = charges-ADD:** the peel adds `peelCharge = ab` to the `u`-monomial and reduces `minAdm` by
  `peelCharge` (`minAdm = peelCharge + minAdm(redChain)`, `#144`); `monomialThreshold` stays `≥ ½minAdm(redChain)`
  after the `½peelCharge` shift (`carrierThreshold_shift`, banked). The nD-homogeneous corner `½Σ(block dims)`
  (dmcheck) is the per-peel realisation.
- **(γ preserved) = the units sector on the WHOLE `Z`:** the peel's coercive tail comes from the `σ_min(Z) ≥ ε`
  quantitative sector (`Z·Zᵀ ≽ c·I` on the WHOLE deeper product `Z = A₂···A_L`, NOT just `A₂` — γ-lock; T4, my
  stephyp cert; `#147`). The rank-drop-of-`Z` complement `{σ_min(Z)<ε}` splits to a higher-`Mval` recursive
  branch (dmcheck P3, threshold `≥½minAdm`). **This is the coupled estimate I certified** (NOT a codim freebie
  — the `x²(x²+y^{2N})` correction; the joint tube `D_q ≤ M₀q` per-branch).
- **(α preserved):** the peel keeps the dehomogenised generator (`radialStep`'s shared-divisor structure;
  `sharedDivisorExp_prependColumn` banked) — the fresh divisor is shared by all generators, so `i₀` persists.
- **FLAG-2 (peel keeps `ν` fixed):** the `genuineCarrier` `ν=product-type` pinning must be preserved (record
  row-elimination in coeff/supp, not shrink `ν`) — else genuineCarrier fails (cover #3-audit).

## 4. ★ The one formalizability point to co-settle with desc3 (base-derivation, `d≥1`) — RESOLVED (γ-lock)

> **RESOLVED (2026-07-12, γ-lock).** The fork below is decided: **SEPARABLE** — route-A `corankLeaf_rpow_lt_top`
> gives the base threshold `min(T_u, D_Γ/2)` (MIN-of-two-full-budgets, not the coupled ADD). Both budgets are
> full: `T_u ≥ ½minAdm` (β) and `D_Γ/2 = ½minAdm` (leaf identity `dim Γ = minAdm`). The prose below is retained
> as the record of how the fork was posed; read §2's corrected `d≥1` line + the ★CORRECTION for the binding form.

The `d≥1` base (§2) — is the `u`-monomial × residual **SEPARABLE** (the smooth width-2 residual decouples
from the `u`'s ⟹ a clean product `(∫commonDivisor^{−2c'}∏|u|^{jac})·(∫frobSq(residual)^{−c'})`, each threshold
`≥½minAdm`... but a PRODUCT gives `min`, and charges must ADD, so a naive drop-to-`i₀` lower bound is TOO WEAK
— it gives `min`, not the coupled `½Σ`) OR genuinely **COUPLED** (the corner estimate, charges-ADD)? At a
SMOOTH width-2 leaf there is no corner to resolve, so a FAITHFUL resolution should have the `u`-divisors
already resolved (from higher peels) and the residual a clean free-block — suggesting separability with the
`u`-charge already = the reduced threshold and the free-block = the width-2 charge, tied by the
threshold-shift ledger. **The exact form (separable via the ledger vs the coupled-corner estimate) is the ONE
thing to pin with desc3 against the signatures + the charge bookkeeping.** Both close ½minAdm; which is the
Lean-cleanest depends on how `jac`/`k`/`minAdm(2-node)` relate at width-2 (the accumulated-charge ↔
threshold-shift consistency). **Recommendation:** state `FaithfulSJAt`'s (β) as the `monomialThreshold ≥
½minAdm` and let #4 use whichever bound the ledger makes clean; if separable, (γ) is the free-block
coercivity; if coupled, (γ) feeds the corner estimate. desc3 pins it on formalizability.

## Firmest / break / next
- **Firmest.** `FaithfulSJAt = (d=0∧ofMatrix) ∨ (d≥1 ∧ pSimultaneous ∧ monomialThreshold≥½minAdm ∧
  coercive-residual)`; each clause banked-tied (α=pSimultaneous; β=charges-ADD/#144; γ=#147/stephyp T4);
  `htriv` discharges (trivial = the `d=0∧ofMatrix` disjunct); subsumes the FLAG-1 fix. #4 consumes, #5
  preserves — ONE invariant, both revolve around it (the controller's consolidation).
- **Most likely to break.** #5's (β)+(γ) PRESERVATION over the intersection/deficient-rank branches — the
  coupled estimate (my stephyp/dmcheck certs), the deepest #5 content; and the §4 separable-vs-coupled base
  form (a formalizability detail, not a soundness one — both close ½minAdm).
- **Next.** desc3 formalises `adm := genuineCarrier ∧ (a=0∨b=0∨ FaithfulSJAt D)` (FaithfulSJAt replacing/
  strengthening admValuation), `htriv`, and #4 (`FaithfulSJAt ⟹ finite`); I audit the #5 (β)+(γ) preservation
  against `stephyp-intersection-cert` + `dmcheck cert` + `#147`, and co-settle §4.

---

## ★ CORRECTION (2026-07-12, γ-lock, decorrelated-confirmed — `codex/gammalock-answer.md`) — γ is the BLOCK-level Z-units-bound; #4 via route-A corankLeaf

The γ-clause above (`‖residualBlock‖ ≥ c`) and the intermediate desc3 sharpening (the i₀-COMPONENT
`|res_{i₀}| ≥ c`) are BOTH superseded. The locked form (γ-lock, decorrelated Codex + cover, no third flip):

- **γ = the BLOCK-level Z-units-bound `∃ c>0, Z·Zᵀ ≽ c·I`** on the DEEPER TAIL product `Z = A₂·A₃···A_L`.
  NOT the i₀-component (`|res_{i₀}|≥c` is **UNSATISFIABLE** for a free corank block `Γ`: `Γ=tΓ₀ → res_{i₀}→0`;
  verified `/tmp/prodD/gamma_component.py`). NOT the block-norm `‖residualBlock‖` (too weak / wrong object).
  The block-level `ZZᵀ≽cI` concerns ONLY `Z`, so the free `Γ`'s rank-deficiency does NOT break it.
- **★ on the WHOLE `Z`, not just the factor `A₂`.** `σ_min(A₂)≥ε` alone is INSUFFICIENT (counterexample
  `A₂=I, A₃=0 → Z=0`). The units sector must control `σ_min(Z) ≥ ε` (the whole deeper product); the
  small-`σ_min(Z)` complement recurses (rank-drop branch, dmcheck P3). **This corrects "σ_min(A₂)" in this
  cert AND in `stephyp-intersection-cert` (see its correction note).**
- **#4 (base) = route-A `corankLeaf_rpow_lt_top`** (banked LOSS part, `RouteMSJLeafRayleigh`/`LeafFinite`):
  `decLoss ≍ commonDivisor(u)²·frobSq(Γ·Z)`, Rayleigh `frobSq(ΓZ) ≥ c·frobSq(Γ)`, integrate `Γ` as a FREE
  BLOCK. The threshold is **`min(T_u, D_Γ/2)`** (`T_u=monomialThreshold`, `D_Γ=dim Γ=b·M₂`) — **MIN-of-two-
  full-budgets, NOT ADD** (charges do NOT add at the base; the base is separable). Reaches `½minAdm` because
  (β) `T_u ≥ ½minAdm` AND the **LEAF IDENTITY `dim Γ = minAdm(M)`** (width-2 leaf `M=(b,M₂)`:
  `minAdm=b·M₂=D_Γ`), so `D_Γ/2 = ½minAdm`. [The #5 STEP corner is ADD (`½Σ block dims`); the #4 base is MIN.
  Distinct — do not conflate.]
- **The 4 lock conditions (Codex):** (1) β `T_u≥½minAdm`; (2) leaf identity `dim Γ = minAdm(M)`; (3) the
  uniform block lower comparison `decLoss ≳ commonDivisor²·‖ΓZ‖²`; (4) the units sector controls the WHOLE `Z`
  (`ZZᵀ≽cI`), rank-drop complement recursive.
- **Honest correction to §2/§4 above:** my §4 "separable / i₀-component" framing was on the right track (MIN,
  both full) but (a) the i₀-component version desc3 built is unsatisfiable (drop it); (b) my closed-form
  `min_s|q₁+sq₂| = σ_min(block)` was WRONG (it is `dist(q₁, span q₂)`) — the conclusion (i₀ unsatisfiable)
  holds; (c) γ is `ZZᵀ≽cI` on the WHOLE `Z`, route-A `corankLeaf` consumes it, MIN-of-full-budgets. **#5's
  γ-preservation = `ZZᵀ≽cI` on the WHOLE `Z` via the units sector (my updated audit focus).**
