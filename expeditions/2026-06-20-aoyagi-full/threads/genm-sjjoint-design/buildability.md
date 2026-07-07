# Buildability / reachability verdict — THE WALL brick (product-Gram principalisation)

**Seat:** pen-and-paper (reachability assessment, à la the #120 route-call; Mathlib recon + judgment;
decorrelated Codex xhigh, leaning withheld). **Question:** is THE WALL brick of the outer `(S,J)`
resolution — joint principalisation of `det(Q_b Q_bᵀ)=‖∧^q Q_b‖²` of the PRODUCT `Q_b=A·Z` at corank ≥ 2,
tracking shared support — break-it-down-buildable in Lean/Mathlib, from-scratch resolution-of-singularities,
or avoidable by a narrower route? This decides whether R1-UPPER charges as bounded labor or is an operator
scope-call.

---

## VERDICT

- **The brick AS POSED (R-ATOM route: principalise the atom's `det(Q_b Q_bᵀ)^{−p/2}` residual over the
  degenerate tail) is `B` — from-scratch resolution-of-singularities.** It is a determinantal-variety /
  multi-ideal principalisation of a matrix PRODUCT, which Mathlib entirely lacks. The corank ≥ 2
  shared-support step is exactly where it fails: no banked decomposition gives coordinates valid ON the
  rank-drop locus.
- **BUT `C` applies and dominates: R-BLOWUP (Aoyagi's native stepwise single-radial resolution) AVOIDS the
  Gram-determinant principalisation entirely** — the hard object never forms — **and R-BLOWUP is itself `A`
  (break-it-down-buildable):** chart algebra on the banked radial engine + monomial endpoint + the
  `Case111/Case222` templates + the banked charge budget, with the corank ≥ 2 sharing encoded NATIVELY in
  the single-radial-per-block chart (exact DATA below).
- **Net for the R1-UPPER leg: `A` via R-BLOWUP — bounded labor, NOT an operator scope-call — PROVIDED the
  OUTER recursion uses the blow-up route, not the atom's Gram-det principalisation.** The atom (already
  being built on `genm-sjjoint`: `det_rightMulₚ`, `lintegral_comp_rightMulₚ`,
  `matBox_corank_residual_fullSpace_eq`, CFC posdef-sqrt) is sound and useful for the *fixed-full-rank /
  generic* top-layer integration; it is only the OUTER integration over the *degenerate* strata that must
  NOT be a Gram-det principalisation (the B-trap) but the `(S,J)` blow-up (the A-route). The controller's
  in-flight `R1ResolutionGeneral` is the correct architecture; this verdict confirms it and flags the
  atom→Gram path as a B-trap for the outer recursion.

Decorrelated Codex (xhigh, leaning withheld) returned **exactly this**: Q1 `B` ("the outer R-ATOM brick is
a resolution-of-singularities/determinantal-variety problem in disguise"), Q2 R-BLOWUP avoids it and is
buildable ("R-ATOM asks Lean to prove a singular ideal secretly has normal crossings; R-BLOWUP CONSTRUCTS
the normal-crossing coordinates inductively"), Q3 recommend R-BLOWUP.

---

## Mathlib recon (facts — what EXISTS vs what is MISSING)

Read-only over `lean/.lake/packages/mathlib/`.

**(i) exterior power / compound / Cauchy–Binet / `‖∧^q Q_b‖²`:**
- EXISTS: `Mathlib/LinearAlgebra/ExteriorPower/{Basic,Basis,Pairing}.lean`; `det_transpose`,
  `det_conjTranspose`; `(A Aᵀ).rank = A.rank` (`Matrix/Rank.lean`).
- **MISSING: Cauchy–Binet** (`det(AB)=∑_S det A_{·,S} det B_{S,·}`), hence **MISSING the identity
  `det(Q_b Q_bᵀ)=∑_{|S|=q}(det Q_b[:,S])²=‖∧^q Q_b‖²`.** (All `rg` "cauchy" hits are Cauchy sequences /
  integral / bound — unrelated.) *Codex + I agree this is an ELEMENTARY missing lemma, bounded to build.*

**(ii) decomposition `Q_b = D_b·U_b` with `U_b U_bᵀ` nonsingular:**
- EXISTS: `posSemidef_conjTranspose_mul_self` / `_self_mul_conjTranspose` (`Q_bQ_bᵀ` PosSemidef);
  **CFC matrix sqrt** in `Mathlib/Analysis/Matrix/Order.lean` (`CFC.sqrt`, `Matrix.det_sqrt`,
  `Matrix.inv_sqrt`, `CFC.sq_sqrt`, `CFC.sqrt_nonneg`, `PosDef (CFC.sqrt M)`) — *my first recon missed this
  file; the `genm-sjjoint` tide found it; correcting: the posdef-sqrt for FULL-RANK `Q_b` is buildable
  (~80–120 LoC)*; Hermitian spectral theorem (`Analysis/InnerProductSpace/Spectrum`, `Matrix/Spectrum`);
  LDL `S=LDLᴴ` (`Analysis/Matrix/LDL`) **but ONLY for positive-DEFINITE (nonsingular) `S`**; Gram–Schmidt;
  singular-VALUE sequence (`InnerProductSpace/SingularValues`) with `rank(T)`-support.
- **MISSING: a matrix SVD FACTORISATION `U Σ Vᵀ`; and — decisively — ANY decomposition valid ON the
  rank-drop (degenerate) locus.** LDL/Cholesky/CFC-sqrt/spectral all presuppose the nonsingular (or fixed
  eigenstructure) case; none principalises the divisor `{det(Q_bQ_bᵀ)=0}`.

**(iii) monomialisation / principalisation / blow-up / resolution:**
- **MISSING ENTIRELY: resolution of singularities, principalisation, blow-up charts (abstract),
  monomialisation, Newton polytope/polyhedron, log-canonical-threshold, determinantal-variety machinery.**
  (`rg` hits for "blowup"/"resolution" are all tactic-performance notes / Coxeter combinatorics.)
- EXISTS (repo, banked, the constructive substitute): the **radial residual-power engine**
  `radial_morse_residual_power_le` (`∫(frobSq Γ+w)^{−c'} ≤ C·w^{−(c'−pq/2)}`, `c'>pq/2`); the **monomial box
  endpoint** `Case222Cover.monomialIntegrand_integrable_of_lt` (`∫∏|u|^α·unit<∞ ⟺ α_i>−1`),
  `monomialThreshold_ge_of_mult`; the **explicit Aoyagi Case-1/Case-2 single-radial blow-up charts** for the
  `(2,2,2)` instance (`Case111.lean`, `Case222*.lean`); the general linear Haar cov
  `map_linearMap_addHaar_eq_smul_addHaar`; and the atom pieces on `genm-sjjoint`
  (`det_rightMulₚ`, `lintegral_comp_rightMulₚ`, `matBox_corank_residual_fullSpace_eq`).

## The judgment (why R-ATOM is B and R-BLOWUP is A)

**R-ATOM (integrate Γ out → `det(Q_b Q_bᵀ)^{−p/2}` residual, then integrate the OUTER tail).** For a FIXED
full-rank `Q_b` the atom is buildable (banked/in-flight). But the OUTER integral over the tail params runs
`Q_b = A·Z` through its rank-drop, where `det(Q_bQ_bᵀ)^{−p/2}→∞`. Bounding that requires principalising the
maximal-minor / Gram ideal of a **product** jointly with the shared reduced-core ideal. The elementary parts
(Cauchy–Binet, `‖∧^q‖²`, exterior bookkeeping, bounded units, monomial endpoint) are buildable; the decisive
missing step is **knowing which exceptional coordinates are shared by which generators** at corank ≥ 2 — the
`⟨δx,δy⟩=½` vs `⟨δ₁x,δ₂y⟩=1` distinction — which changes the exponent. No pivot chart / LDL / CFC-sqrt /
spectral / singular-value list produces coordinates valid on the rank-drop locus. **This is
resolution-of-singularities of a determinantal variety in disguise — `B`.**

**R-BLOWUP (Aoyagi's native stepwise single-radial resolution).** Do NOT integrate the block out. Blow up
ONE radial coordinate `u` for the WHOLE current corank block (`d-block = u·d'`, top-left normalised), charge
`u` by the full block codim, reduce by one pivot, recurse carrying the reduced block × the downstream
product. The Gram determinant NEVER forms; the fully-resolved loss is a monomial `∑ b_i²`
(`b_i = ∏ u_j`), closed by the banked monomial endpoint. **The corank ≥ 2 sharing is ENCODED IN THE CHART:**
one radial `u` for the block ⟹ that `u` is shared across the block's generators — the correct (lower) RLCT —
and the shared support is *explicitly recorded* as the product monomials `b_i`, not discovered by resolving a
Gram ideal. This is chart algebra (finite cover, coordinate maps, Jacobian powers, recursive loss identity,
exponent inequalities) on banked pieces — **`A`, large but not RoS.**

## The corank ≥ 2 probe (hardest — exact DATA, `sjj_radial_shared.py`)

A 2-corank block coupled to downstream directions `(x,y)`, resolved two ways (exact toric RLCT
`min_{w>0}(Σw)/(min_α⟨w,α⟩)`):

| resolution | monomials | RLCT | structure |
|---|---|---|---|
| **single-radial** `Δ=u·V` (Aoyagi Case-2 / banked radial engine) | `u²x², u²y²` | **½** | SHARED `u` = `⟨δx,δy⟩` — CORRECT |
| per-entry `Δ₁=u₁,Δ₂=u₂` (naive / threshold-only) | `u₁²x², u₂²y²` | 1 | SEPARATE = `⟨δ₁x,δ₂y⟩` — WRONG (over-counts) |

**The single-radial-per-block chart realises the shared support NATIVELY** (one `u` ⟹ lower/correct RLCT).
So the corank ≥ 2 shared-support is NOT a separate symbolic-bookkeeping brick in R-BLOWUP — it is a
consequence of using one radial coordinate per block (the very structure the banked
`radial_morse_residual_power_le` already has). In R-ATOM the same distinction must instead be RECOVERED by
resolving a determinantal ideal (the B-wall). This is the crux of the A-vs-B split.

## Sub-brick decomposition of the recommended (R-BLOWUP) runway + template map

| sub-brick | maps to (banked template / class) |
|---|---|
| finite chart cover of the rank-≥t / corank strata per layer | `pivotChartCover_matBox_le_sum` + `pivotLocus_eq_iUnion` (banked) |
| single-radial blow-up of the corank block + Jacobian power `= block codim` | `radial_morse_residual_power_le` engine (banked); the `(2,2,2)` charts `Case222*` (template) |
| Case-1 partial-block step + inner exponent-add recursion | `Case111.lean` (template, `(2,2,2)`) — generalise to general widths |
| the recursive loss identity `→ reduced-chain form × monomial radial factors` | NEW general-`L` chart lemma (Codex's "single hardest sub-brick") |
| exponent/charge bookkeeping (accumulated `= Mval(branch) ≥ minAdm`) | `minAdmRec_eq_minAdm`, `sjChargeUpdate_accum`, `sjSubordination` (banked) + the `0/171` threshold-monotonicity (DATA, outer-construction-cert) |
| monomial endpoint `∫∏|u|^α·unit<∞ ⟺ α_i>−1` | `monomialIntegrand_integrable_of_lt`, `monomialThreshold_ge_of_mult` (banked) |
| (elementary, only if R-ATOM pieces reused) `det(Q_bQ_bᵀ)=‖∧^q Q_b‖²` | Cauchy–Binet — MISSING but bounded-standard |

**The single hardest sub-brick (Codex + me):** the **general-`(L,S,J)` single-radial blow-up chart lemma** —
construct the recursive charts at general widths, prove the transformed loss has the reduced-chain form with
explicit monomial radial factors, and compute the Jacobian/exponent bookkeeping uniformly. It is large
formalisation work (the `(2,2,2)` `Case111/Case222` are the templates; the value is certified general-`L`;
the charge budget is banked), NOT general RoS. Once banked, the radial estimates + monomial endpoint are
within the existing runway.

---

## DATA (mine) vs Codex INTERPRETATION

- **DATA (exact):** Mathlib recon (facts above); `sjj_radial_shared.py` (single-radial `u` ⟹ RLCT ½ =
  shared; per-entry ⟹ 1 = separate) — the exact corank-≥2 chart-vs-ideal distinction; the `genm-sjjoint`
  tide's built atom pieces (`det_rightMulₚ` etc., sorry-free, confirmed from the branch).
- **Codex INTERPRETATION** (`codex/buildability-{prompt,answer}.md`, xhigh, leaning withheld): Q1 `B`
  (outer R-ATOM = RoS/determinantal in disguise; Cauchy–Binet elementary-missing; "no coordinates valid on
  the rank-drop locus"); Q2 R-BLOWUP avoids it and is buildable, corank≥2 handled by sequential single-radial
  charts with support recorded as `b_i=∏u_j` — "R-ATOM asks Lean to prove a singular ideal secretly has
  normal crossings; R-BLOWUP constructs the normal-crossing coordinates inductively"; Q3 recommend R-BLOWUP,
  hardest sub-brick = the general-`(L,S,J)` chart lemma. (Inference, but matches the exact recon + DATA.)

## Closing

- **Firmest.** The literal WALL brick (R-ATOM Gram-det-of-product principalisation) is `B` (RoS Mathlib
  lacks). R-BLOWUP avoids it and is `A` (chart algebra on banked radial + monomial + `Case111/Case222` +
  charge budget), corank≥2 encoded natively in the single-radial chart (exact DATA). Net: **R1-UPPER charges
  as bounded labor via R-BLOWUP; it is NOT an operator scope-call — SO LONG AS the outer recursion is the
  blow-up, not the atom's Gram principalisation.** Decorrelated Codex identical.
- **The one strategic hazard.** If a formaliser tries to complete the *atom* route all the way through the
  OUTER integral (principalise `det(Q_bQ_bᵀ)` of the product), they hit the `B`-wall. The atom is correct
  and useful for the fixed-full-rank / generic slice; the degenerate strata must route to the `(S,J)`
  blow-up. Keep the two uses distinct.
- **Most likely to break this verdict.** If the general-`(L,S,J)` single-radial chart lemma turns out to
  need a *simultaneous* (not sequential-per-layer) resolution of the shared `Z` degeneracies that a finite
  explicit chart cover cannot express — i.e. if the `(2,2,2)` templates do NOT generalise by
  opaque-width induction. I judge this unlikely (Aoyagi's construction is explicitly the sequential `(S,J)`
  progression, and the value is certified general-`L`), but it is the cheapest thing to test before
  committing the multi-tide build: attempt the general-`L` chart lemma on the smallest genuinely-coupled
  corank-≥2 product case (a 4-width chain with a corank-2 binding cut, e.g. embed `(3,3,4)`'s `2×2` corank
  into `(3,3,4,·)`), checking the recursive loss identity `→ reduced-chain × monomial` holds on the finite
  chart cover. *(Speculation registered; the Lean route is the controller's.)*
