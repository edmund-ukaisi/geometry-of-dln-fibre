# genm-vsastruct — the T4 / DecoratedPeelStep architecture design (the (□)-core)

**Seat:** pen-and-paper (design + obstruction). **Date:** 2026-07-11. **NO Lean.** **Charge:** nail the
architecture of the decorated peel step before the formaliser is commissioned. **Exact algebra:**
`/tmp/dps_coupling.py` (prior); monomial-threshold algebra (below). **Decorrelated:**
`codex/t4design-{prompt,answer}.md` (gpt-5.6, xhigh; my lean withheld — it CONFIRMED every point and
supplied the `∀`-decoration counterexample + the product-vs-sum threshold proof). Reads: own
`dps-instance-cert.md` + `corank2-cert.md`; live code `RouteMSJDecorated{,Rec,RowMix}.lean`,
`RouteMSJLedger.lean`, `RouteMSJCorankPeel.lean`, `RouteMSJResolution.lean`; recon-map (banked file:lines).

---

## ONE-LINE VERDICT

**Route (A) — the decorated double induction — IS the right primitive (route (B) collapses into it). BUT
two corrections make it MORE than "assemble regime A/B into one peel", and one is load-bearing:
(1) the `∀`-decoration predicate is FALSE (`(trivial (1,2)).radialAttach 0` diverges at `c'=3/4 <
½·minAdm=1`); the step must quantify over an inductively-closed ADMISSIBLE/REACHABLE decoration class.
(2) ★ The target `½·minAdm` is NOT delivered by repeated `radialAttach` — that produces the MULTIPLICATIVE
terminal `∏|u_k|^{h_k−2c'}`, threshold `½·min_k p_k = 3/2` (the undershoot), decorrelated-confirmed. The
`7/2` requires the ADDITIVE coupled-corner blow-up (`(∑_k u_k²U_k)^{−c'}`, `u_k=u·τ_k` → ONE divisor
`H=Σh_k+(m−1)`, threshold `½·Σp_k = ½·minAdm`) — a divisor-MERGE operation the banked `radialAttach`
(fresh independent divisor) and `corankBlock_morsePeel` (integrate-out, fails past the shifted threshold at
level ≥2) do NOT provide. This coupled-corner-merge, with the units `U_k` bounded below via an EXPLICIT
A₂-rank-drop stratum, is the genuinely-new HEART. It is NOT a hard wall (vslice §5 verifies `7/2` by exactly
this merge), but it is the unbuilt crux — and building the recursion on `radialAttach`-across-levels as
currently framed would land the `3/2` undershoot.**

---

## 1. (Q1) Route (A) is primitive; (B) collapses into it

At level `k`, `det(Q_b^{(k)}Q_b^{(k)ᵀ})^{−a/2}` is the induced-volume Jacobian of `Γ↦Γ·Q_b`; `Q_b` is
built from the DEEPER product, so its singular (rank-drop) divisor is exactly what the NEXT peel
principalises. So the level-`k` det and the level-`(k+1)` coupling are the SAME SPECIES (singular volume
data coupled to a residual product loss) — not the same scalar formula (dims/exponents differ; the earlier
det becomes `jac`/support data once the deeper coupling is resolved). Hence the closed recursive object is
NOT a plain loss but a **decoration** (loss + accumulated divisor valuations + generator support). Route (B)
(a standalone joint-weighted lemma) is either (i) a raw-det global majorant — which is NOT a theorem about
the true bounded-box integral (the full-space `Γ`-atom is `+∞` along `ker(Γ↦Γ·Q_b)` when `rank Q_b < b`,
while the bounded-box integral can be finite), so it needs rank-stratification anyway; or (ii) once
repaired, its proof IS the decorated recursion in specialised form. **⟹ (A) is the general primitive; a
fixed-chain (B) is at most a base-case/validation lemma.** [FACT+INFERENCE — Codex Q1, confirmed.]

## 2. (Q2) The `∀`-decoration predicate is FALSE — an Admissible class is required

The team lead's proposed `DecoratedPeelStep'` quantifies `∀ decoration δ`. **This is false.** [FACT —
Codex counterexample, banked constructors:] on `M=(1,2)` (`½·minAdm = 1`), `D = (trivial M).radialAttach 0`
has `D.integral(c') = (∫₀¹ u^{−2c'} du)·(trivial M).integral(c')`, and `∫₀¹u^{−2c'}` DIVERGES at
`c'=3/4 < 1`. So not every `SJDecoration` inhabitant is finite below the chain threshold (the current
struct allows arbitrary `jac`, carrier, `Z`, `dom`). The predicate must be

> `∀ M, [∀ M' shorter, ∀ D', Admissible(M',D') → Finite(D')] → [∀ D, Admissible(M,D) → Finite(D)]`

with `Admissible(M,D)` an **inductively-closed reachability** predicate (reachable from the trivial product
carrier through the permitted chart ops), enforcing at minimum:
- `jac` = the ACTUAL Jacobian valuation of the composite chart (not arbitrary); a fresh `p`-dim radial
  contributes `p−1`, a corner substitution INCREMENTS the shared-divisor exponent by the merge dimensions;
- the carrier support = permitted block-splits / unit row-mixes / corank steps, preserving nested/shared
  support relations;
- `dom`/measure from the parameter box through VALID changes of variables;
- **unit coefficients bounded above AND below on the relevant rank sector**;
- **rank-drop complements routed to explicit deeper strata**;
- accumulated charge + remaining chain satisfy the binding-budget (`minAdm M = Σ peelCharge`).

[FACT — the counterexample; INFERENCE — the class list, Codex Q2 + corank2-cert.] Defining `Admissible`
precisely is itself part of the build (it is the honest content the recon called "the SJState/sjRunMin
stubs"). The arity driver (`routeMBoxThresholdFinite_of_step`, generic `Nat.strong_induction_on`)
GENERALISES to this predicate — the strong-induction scaffold is predicate-agnostic — but needs a decorated
re-statement + an Admissible base (every admissible decoration reaching a 2-node chain is finite), which
`radialAttach 0` shows is FALSE for the un-restricted quantifier.

## 3. ★ (Q3) The charges DO NOT add via `radialAttach` — the coupled-corner MERGE is the crux

**Repeated `radialAttach` gives the MIN, not the sum.** [FACT — Codex Q3, exact; matches my derivation.]
`radialAttach` multiplies the loss by `u_k²` and prepends a fresh divisor (`sharedDivisorExp = 1`), so `m`
levels give the MULTIPLICATIVE terminal

> `∏_k |u_k|^{h_k}·(∏_k u_k²)^{−c'} = ∏_k |u_k|^{h_k−2c'}`,  finite ⟺ `c' < ½·min_k(h_k+1) = ½·min_k p_k`.

For `(3,3,3,4)` (`p = (4,3)`, `h = p−1 = (3,2)`): `½·min(4,3) = 3/2` — the UNDERSHOOT, exactly the
`min(2,3/2)` of vslice §5 / corank2-cert §1. The banked `monomialThreshold d (sharedDivisorExp e) h =
min_ℓ (h_ℓ+1)/(2·sharedDivisorExp_ℓ)` (Case222Cover / RouteMSJLedger terminal) IS this min. **So a
recursion built on `radialAttach`-across-levels lands `3/2`, NOT `7/2`.**

**The sum-threshold requires the ADDITIVE coupled-corner loss + a MERGE blow-up.** [FACT — Codex Q3.] The
correct local model is `∏_k|u_k|^{h_k}·(∑_k u_k²U_k)^{−c'}`, `U_k ≍ 1` — the loss vanishes only at the
COMMON corner. Blow it up (`u_k = u·τ_k`, `k>1`): ONE exceptional coordinate `u` with Jacobian exponent
`H = Σ_k h_k + (m−1)` and loss order `u²`, threshold

> `(H+1)/2 = ½·Σ_k(h_k+1) = ½·Σ_k p_k = ½·minAdm(M)`.

For `p=(4,3)`: `H = 3+2+1 = 6 → 7/2`. ✓ (the vslice §5 corner, verified). Equivalently, the regime-A Morse
integrate-out ADDS exponent shifts `c'↦c'−p₁/2↦c'−(p₁+p₂)/2↦…` — but ONLY while each step retains the
ADDITIVE coupled loss; it CANNOT be replaced by factoring a multiplicative `radialAttach`. **This
coupled-corner-merge is NOT banked:** `radialAttach` is the multiplicative product (→min); repeated
`corankBlock_morsePeel` (integrate-out, shift `ab/2`) FAILS past the shifted threshold — at `(3,3,3,4)`
level 2 the shifted exponent `c'−2 < 3/2 = ab/2` so regime A is inapplicable, so the additive-shift chain
breaks and the `7/2` must come from the joint corner (route i). **So the divisor-MERGE (additive corner →
single divisor) is the genuinely-new operation the decorated carrier is missing.**

**The A₂-rank-drop must be an EXPLICIT stratum** (soundness (d), Codex Q3-confirmed): near
`{rank Q_b < b}` the units `U_k` lose their uniform positive lower bound, so the coupled-corner blow-up's
`U_k ≍ 1` FAILS there. One must cover a generic-minor sector `{U_k ≥ a > 0}` and send its complement to a
deeper / higher-`Mval` resolution. **An a.e. deletion does NOT control the surrounding singular tube** (the
`|u|^{−1}` model). Treating the det valuation and the reduced loss as independent scalar branches along the
shared divisor takes the MIN (the `z²(x²+y²)` RLCT-collapse); the correct coupled corner ADDS them.

## 4. (guards) — baked in

- **Binding cut** (`exists_binding_cut`): the peel MUST use `u★` with `minAdm M = peelCharge + minAdm(redChain)`
  — else (dps-cert Q3, `M=(4,4,2,2)` t=2) the `c'=ab/2` log-borderline coincides with `½·minAdm` and the
  regime switch sits at the threshold. At the binding cut, `minAdm(redChain) ≥ 1 ⟹ ½·minAdm > ab/2`
  (borderline strictly interior). [BANKED shift `carrierThreshold_shift` is tight here.]
- **Base case** = the trivial decoration (`decoratedBoxThresholdFinite_trivial_iff` = plain box, free-matrix
  Morse `sjBase1_freeMatrix`) — but as an ADMISSIBLE base (§2), the base must cover every admissible
  decoration reaching a 2-node chain, not the trivial one alone.

## 5. What is banked vs genuinely-new (scoping the real %)

- **BANKED (scaffold):** `SJDecoration` (∀-decoration struct), `DecoratedBoxThresholdFinite`,
  `decoratedBoxThresholdFinite_trivial_iff`, `radialAttach` (+ integral), `rowMix` (const-support
  `rowMix_decLoss`), `sharedDivisorExp`/`commonDivisor`/`residualSupport`, the terminal
  `sjLoss_terminal_lintegral_lt_top` (min-threshold), the arity driver, `carrierThreshold_shift`, the
  charge bookkeeping, `corankBlock_morsePeel` (single-block integrate-out), the FreedPeel regimes A/B.
- **GENUINELY NEW (the heart, in priority):**
  1. ★ **The coupled-corner MERGE operation** on the decorated carrier: the additive `∑u_k²U_k` corner →
     single merged divisor `H=Σh_k+(m−1)` (the sum-threshold). This is the min→sum fix; NOT `radialAttach`,
     NOT repeated `corankBlock_morsePeel`. Without it the recursion undershoots to `3/2`.
  2. **The `Admissible`/`Reachable` decoration class** + its inductive closure (units bounded below on the
     rank sector; rank-drop complements routed to deeper strata) + the decorated arity driver over it.
  3. **The explicit A₂-rank-drop stratification** (generic-minor sector + deeper-resolution complement) —
     the soundness (d) trap.
  4. **T2 a′** rowMix at analytic (non-const) support (`hsh`) — needed for the merge to record the shared
     divisor faithfully.

---

## VERDICT / firmest / most-likely-to-break / next

- **VERDICT.** Architecture (A) is the right primitive, corrected to an **admissible-decoration
  induction**. `∀`-decoration is FALSE. `½·minAdm` is reachable via the additive coupled-corner blow-up
  (or the additive exponent-shift chain that retains the coupled loss), NOT via the multiplicative
  `radialAttach` product. **Do NOT commission the T4 formaliser on "assemble regime A/B + radialAttach
  across levels"** — that lands the `3/2` undershoot. The remaining genuine obstruction is precise:
  construct the peel map on ADMISSIBLE carriers with the coupled-corner MERGE (sum-threshold), and prove
  its joint corner / truncated estimate on every deep-rank stratum, especially the A₂-rank-drop complement
  where the units are not bounded below. NOT a hard wall (vslice §5 verifies `7/2` by this merge).
- **Firmest.** (Q3) `radialAttach`-product → `½·min p_k = 3/2`; coupled-corner-merge → `½·Σ p_k = 7/2`
  (`H=6`); both exact + decorrelated. (Q2) `∀`-decoration false (banked `radialAttach 0` counterexample).
  (Q1) (B) collapses into (A).
- **Most likely to break.** The MERGE realisation in the carrier: `sharedDivisorExp` must ACCUMULATE the
  shared-A₂ coupling so the level-`k` and level-`(k+1)` divisors coincide (one binding divisor with the
  summed `h`), else the terminal min undershoots. And the A₂-rank-drop stratum: an a.e.-drop silently
  RLCT-collapses. These are the ~genuinely-new content; the scaffold does not deliver them.
- **Next (smallest settling build).** On `(3,3,3,4)` at `t=1`: realise ONE coupled-corner MERGE of the two
  radial divisors (Γ-block `h=3`, boundary-row `h=2`) into the single `H=6` divisor and confirm the
  terminal threshold is `7/2` (not the `3/2` product-min) THROUGH the decorated carrier's `sharedDivisorExp`
  — with the A₂-rank-drop routed to an explicit generic-minor sector. If the carrier can express the merge
  (sum-threshold) with units bounded below, the (A) architecture is fully specified and buildable-as-labour;
  if the merge cannot be expressed without a new carrier operation (a corner-blow-up constructor beyond
  `radialAttach`/`rowMix`), that constructor is the isolated minimal new primitive to build first.
